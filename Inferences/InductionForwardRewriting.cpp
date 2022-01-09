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
#include "Shell/InductionPreprocessor.hpp"

#include "InductionForwardRewriting.hpp"
#include "InductionHelper.hpp"
#include "InductionRemodulation.hpp"

#if VDEBUG
#include <iostream>
using namespace std;
#endif

using namespace Inferences;
using namespace Lib;
using namespace Kernel;
using namespace Saturation;

struct InductionForwardRewriting::GeneralizationsFn {
  GeneralizationsFn(RewritingLHSIndex *index) : _index(index) {}
  VirtualIterator<pair<pair<Literal *, TermList>, TermQueryResult>> operator()(pair<Literal *, TermList> arg)
  {
    CALL("InductionForwardRewriting::GeneralizationsFn()");
    return pvi(pushPairIntoRightIterator(arg, _index->getGeneralizations(arg.second)));
  }

private:
  RewritingLHSIndex* _index;
};

struct InductionForwardRewriting::RewriteableSubtermsFn {
  VirtualIterator<pair<Literal *, TermList>> operator()(Literal *lit)
  {
    CALL("InductionForwardRewriting::RewriteableSubtermsFn()");
    NonVariableIterator nvi(lit);
    return pvi(pushPairIntoRightIterator(lit,
                                         getUniquePersistentIteratorFromPtr(&nvi)));
  }
};

struct InductionForwardRewriting::ForwardResultFn {
  ForwardResultFn(Clause *cl, Ordering& ord) : _cl(cl), _ord(ord) {}

  Clause* operator()(pair<pair<Literal *, TermList>, TermQueryResult> arg)
  {
    CALL("InductionForwardRewriting::ForwardResultFn()");

    TermQueryResult &qr = arg.second;
    return InductionForwardRewriting::perform(
      _cl, arg.first.first, arg.first.second, qr.clause,
      qr.literal, qr.term, qr.substitution, true, _ord);
  }
private:
  Clause *_cl;
  Ordering& _ord;
};

struct AllVarsFilterFn {
  AllVarsFilterFn(Clause* cl) : _cl(cl) {}
  bool operator()(pair<Literal*, TermList> arg) {
    return termHasAllVarsOfClause(arg.second, _cl);
  }
private:
  Clause* _cl;
};

struct RewritingLHSFn
{
  RewritingLHSFn(Ordering& ord) : _ord(ord) {};
  VirtualIterator<pair<Literal*, TermList>> operator()(Literal* lit)
  {
    return pvi(pushPairIntoRightIterator(lit, EqHelper::getLHSIterator(lit, _ord)));
  }
private:
  Ordering& _ord;
};

struct RewritableResultsFn
{
  RewritableResultsFn(RemodulationSubtermIndex* index) : _index(index) {}
  VirtualIterator<pair<pair<Literal*, TermList>, TermQueryResult> > operator()(pair<Literal*, TermList> arg)
  {
    return pvi(pushPairIntoRightIterator(arg, _index->getInstances(arg.second, true)));
  }
private:
  RemodulationSubtermIndex* _index;
};

struct InductionForwardRewriting::BackwardResultFn
{
  BackwardResultFn(Clause* cl, Ordering& ord) : _cl(cl), _ord(ord) {}
  Clause* operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("BackwardResultFn::operator()");

    if(_cl==arg.second.clause) {
      return 0;
    }

    TermQueryResult& qr = arg.second;
    return InductionForwardRewriting::perform(
      qr.clause, qr.literal, qr.term,
	    _cl, arg.first.first, arg.first.second, qr.substitution, false, _ord);
  }
private:
  Clause* _cl;
  Ordering& _ord;
};


ClauseIterator InductionForwardRewriting::generateClauses(Clause *premise)
{
  CALL("InductionForwardRewriting::generateClauses");

  ClauseIterator res = ClauseIterator::getEmpty();
  if (InductionHelper::isInductionClause(premise) && InductionHelper::isInductionLiteral((*premise)[0])) {
    auto itf1 = premise->iterLits();

    // Get an iterator of pairs of selected literals and rewritable subterms
    // of those literals. Here all subterms of a literal are rewritable.
    auto itf2 = getMapAndFlattenIterator(itf1, RewriteableSubtermsFn());

    // Get clauses with a function definition literal whose lhs is a generalization of the rewritable subterm,
    // returns a pair with the original pair and the generalization result (includes substitution)
    auto itf3 = getMapAndFlattenIterator(itf2, GeneralizationsFn(_index));

    //Perform forward rewriting
    res = pvi(getMappingIterator(itf3, ForwardResultFn(premise, _salg->getOrdering())));
  }
  else if (canUseForRewrite(premise))
  {
    auto itb1 = premise->iterLits();
    auto itb2 = getMapAndFlattenIterator(itb1, RewritingLHSFn(_salg->getOrdering()));
    auto itb3 = getFilteredIterator(itb2, AllVarsFilterFn(premise));
    auto itb4 = getMapAndFlattenIterator(itb3, RewritableResultsFn(_tindex));

    res = pvi(getMappingIterator(itb4, BackwardResultFn(premise, _salg->getOrdering())));
  }
  // Remove null elements
  auto it2 = getFilteredIterator(res, NonzeroFn());
  return getTimeCountedIterator(it2, TC_FNDEF_REWRITING);
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
    res->setInductionLemma(true);
  }
  return res;
}
