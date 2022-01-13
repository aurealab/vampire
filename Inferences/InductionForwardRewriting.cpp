/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file InductionForwardRewriting.cpp
 * Implements class InductionForwardRewriting.
 */

#include "Lib/Metaiterators.hpp"
#include "Lib/PairUtils.hpp"

#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Ordering.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"

#include "Indexing/IndexManager.hpp"

#include "Shell/Options.hpp"

#include "InductionForwardRewriting.hpp"
#include "InductionHelper.hpp"
#include "InductionRemodulation.hpp"

ClauseIterator InductionForwardRewriting::generateClauses(Clause *premise)
{
  CALL("InductionForwardRewriting::generateClauses");

  ClauseIterator res = ClauseIterator::getEmpty();
  if (InductionHelper::isInductionClause(premise) && InductionHelper::isInductionLiteral((*premise)[0])) {
    auto itf1 = premise->iterLits();

    // Get an iterator of pairs of selected literals and rewritable subterms
    // of those literals. Here all subterms of a literal are rewritable.
    auto itf2 = getMapAndFlattenIterator(itf1, [](Literal *lit) {
      NonVariableIterator nvi(lit);
      return pvi(pushPairIntoRightIterator(lit,
        getUniquePersistentIteratorFromPtr(&nvi)));
    });

    // Get clauses with a function definition literal whose lhs is a generalization of the rewritable subterm,
    // returns a pair with the original pair and the generalization result (includes substitution)
    auto itf3 = getMapAndFlattenIterator(itf2, [this](pair<Literal *, TermList> arg) {
      return pvi(pushPairIntoRightIterator(arg, _index->getGeneralizations(arg.second)));
    });

    //Perform forward rewriting
    res = pvi(getMappingIterator(itf3, [this, premise](pair<pair<Literal *, TermList>, TermQueryResult> arg) {
      TermQueryResult &qr = arg.second;
      return InductionForwardRewriting::perform(
        premise, arg.first.first, arg.first.second, qr.clause,
        qr.literal, qr.term, qr.substitution, true, _salg->getOrdering());
    }));
  }
  if (canUseForRewrite(premise))
  {
    auto itb1 = premise->iterLits();
    auto itb2 = getMapAndFlattenIterator(itb1, [this](Literal* lit) {
      return pvi(pushPairIntoRightIterator(lit, EqHelper::getLHSIterator(lit, _salg->getOrdering())));
    });
    auto itb3 = getFilteredIterator(itb2, [premise](pair<Literal*, TermList> arg) {
      return termHasAllVarsOfClause(arg.second, premise);
    });
    auto itb4 = getMapAndFlattenIterator(itb3, [this](pair<Literal*, TermList> arg) {
      return pvi(pushPairIntoRightIterator(arg, _tindex->getInstances(arg.second, true)));
    });

    res = pvi(getMappingIterator(itb4, [this,premise](pair<pair<Literal*, TermList>, TermQueryResult> arg) -> Clause* {
      if(premise == arg.second.clause) {
        return nullptr;
      }

      TermQueryResult& qr = arg.second;
      return InductionForwardRewriting::perform(
        qr.clause, qr.literal, qr.term,
        premise, arg.first.first, arg.first.second, qr.substitution, false, _salg->getOrdering());
    }));
  }
  // Remove null elements
  return pvi(getFilteredIterator(res, NonzeroFn()));
}

Clause *InductionForwardRewriting::perform(
    Clause *rwClause, Literal *rwLit, TermList rwTerm,
    Clause *eqClause, Literal *eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult, Ordering& ord)
{
  CALL("InductionForwardRewriting::perform/2");

  if (SortHelper::getTermSort(rwTerm, rwLit) != SortHelper::getEqualityArgumentSort(eqLit)) {
    // sorts don't match
    return 0;
  }

  // ASS_REP(!eqLHS.isVar(), *eqClause);

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);

  TermList tgtTermS = eqIsResult ? subst->applyToBoundResult(tgtTerm) : subst->applyToBoundQuery(tgtTerm);
  Literal* eqLitS = eqIsResult ? subst->applyToBoundResult(eqLit) : subst->applyToBoundQuery(eqLit);

  Literal *tgtLitS = EqHelper::replace(rwLit, rwTerm, tgtTermS);
  if (EqHelper::isEqTautology(tgtLitS)) {
    return 0;
  }

  unsigned rwLength = rwClause->length();
  unsigned eqLength = eqClause->length();
  unsigned newLength = rwLength + eqLength - 1;

  Inference inf(GeneratingInference2(InferenceRule::INDUCTION_FORWARD_REWRITING, rwClause, eqClause));
  Clause *res = new (newLength) Clause(newLength, inf);

  (*res)[0] = tgtLitS;

  unsigned next = 1;
  for (unsigned i = 0; i < rwLength; i++) {
    Literal *curr = (*rwClause)[i];
    if (curr != rwLit) {
      curr = EqHelper::replace(curr, rwTerm, tgtTermS);

      if (EqHelper::isEqTautology(curr)) {
        res->destroy();
        return 0;
      }

      (*res)[next++] = curr;
    }
  }

  vset<pair<Literal*,Literal*>> rest;
  {
    for (unsigned i = 0; i < eqLength; i++) {
      Literal *curr = (*eqClause)[i];
      if (curr != eqLit) {
        Literal *currAfter = eqIsResult ? subst->applyToBoundResult(curr) : subst->applyToBoundQuery(curr);
        rest.insert(make_pair(curr,currAfter));

        if (EqHelper::isEqTautology(currAfter)) {
          res->destroy();
          return 0;
        }

        (*res)[next++] = currAfter;
      }
    }
  }

  const auto rinfos = rwClause->getRemodulationInfo<DHSet<RemodulationInfo>>();
  // TODO not sure this block helps a lot, find out
  if (rinfos) {
    DHSet<RemodulationInfo>::Iterator rit(*rinfos);
    while (rit.hasNext()) {
      auto rinfo = rit.next();
      if (rinfo._eqGr == eqLitS) {
        // if rest from rinfo contains current rest,
        // the rewriting with eqClause or a clause
        // that subsumes eqClause was done
        bool contains = !rinfo._rest.empty();
        for (const auto& kv : rinfo._rest) {
          if (!rest.count(kv)) {
            contains = false;
            break;
          }
        }
        if (contains) {
          res->destroy();
          return 0;
        }
      }
    }
  }

  auto rinfosU = RemodulationInfo::update(res, tgtLitS, rinfos, ord);

  if (rinfosU->isEmpty()) {
    delete rinfosU;
  } else {
    res->setRemodulationInfo(rinfosU);
    res->markInductionLemma();
  }
  return res;
}