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
 * @file InductionRemodulation.cpp
 * Implements class InductionRemodulation.
 */

#include "Lib/Metaiterators.hpp"

#include "Kernel/SortHelper.hpp"
#include "Kernel/TermIterators.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"

#include "InductionHelper.hpp"

#include "InductionRemodulation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;

TermList SingleOccurrenceReplacement::transformSubterm(TermList trm)
{
  CALL("SingleOccurrenceReplacement::transformSubterm");

  if(trm.isTerm() && trm.term() == _o){
    if (_iteration == _matchCount++) {
      return _r;
    }
  }
  return trm;
}

Literal* SingleOccurrenceReplacement::transformSubset()
{
  CALL("SingleOccurrenceReplacement::transformSubset");
  // Increment _iteration, since it either is 0, or was already used.
  _iteration++;
  if (_iteration > _occurrences) {
    return nullptr;
  }
  _matchCount = 1;
  return transform(_lit);
}

void InductionRemodulation::attach(SaturationAlgorithm* salg)
{
  CALL("InductionRemodulation::attach");
  GeneratingInferenceEngine::attach(salg);
  _lhsIndex=static_cast<RemodulationLHSIndex*>(
	  _salg->getIndexManager()->request(REMODULATION_LHS_SUBST_TREE) );
  _termIndex=static_cast<RemodulationSubtermIndex*>(
	  _salg->getIndexManager()->request(REMODULATION_SUBTERM_INDEX) );
}

void InductionRemodulation::detach()
{
  CALL("InductionRemodulation::detach");
  _lhsIndex = 0;
  _salg->getIndexManager()->release(REMODULATION_LHS_SUBST_TREE);
  _termIndex = 0;
  _salg->getIndexManager()->release(REMODULATION_SUBTERM_INDEX);
  GeneratingInferenceEngine::detach();
}

struct ReverseLHSIteratorFn {
  ReverseLHSIteratorFn(Clause* cl) : _cl(cl) {}
  VirtualIterator<pair<Literal*, TermList>> operator()(pair<Literal*, TermList> arg)
  {
    CALL("ReverseLHSIteratorFn()");
    auto rhs = EqHelper::getOtherEqualitySide(arg.first, arg.second);
    if (!litHasAllVarsOfClause(arg.first, _cl) ||
        !termHasAllVarsOfClause(rhs, _cl)) {
      return VirtualIterator<pair<Literal*, TermList>>::getEmpty();
    }
    if (env.options->inductionRemodulationRedundancyCheck() && !hasTermToInductOn(arg.second.term(), arg.first)) {
      return VirtualIterator<pair<Literal*, TermList>>::getEmpty();
    }
    return pvi(getSingletonIterator(make_pair(arg.first,rhs)));
  }
private:
  Clause* _cl;
};

ClauseIterator InductionRemodulation::generateClauses(Clause* premise)
{
  CALL("InductionRemodulation::generateClauses");
  ClauseIterator res1 = ClauseIterator::getEmpty();

  if (InductionHelper::isInductionClause(premise) && InductionHelper::isInductionLiteral((*premise)[0])) {
    // forward result
    auto it1 = premise->getLiteralIterator();
    auto it2 = getFilteredIterator(it1, [](Literal* lit){
      return InductionHelper::isInductionLiteral(lit);
    });
    auto it3 = getMapAndFlattenIterator(it2, [](Literal* lit) {
      NonVariableNonTypeIterator nvi(lit);
      return pvi( pushPairIntoRightIterator(lit, getUniquePersistentIteratorFromPtr(&nvi)) );
    });
    auto it4 = getMapAndFlattenIterator(it3, [this](pair<Literal*, TermList> arg) {
      return pvi( pushPairIntoRightIterator(arg, _lhsIndex->getGeneralizations(arg.second, true)) );
    });
    res1 = pvi(getMapAndFlattenIterator(it4, [this, premise](pair<pair<Literal*, TermList>, TermQueryResult> arg) {
      TermQueryResult& qr = arg.second;
      return perform(premise, arg.first.first, arg.first.second,
        qr.clause, qr.literal, qr.term, qr.substitution, true, qr.constraints);
    }));
  }

  // backward result
  ClauseIterator res2 = ClauseIterator::getEmpty();
  if (canUseForRewrite(premise))
  {
    auto itb1 = premise->getLiteralIterator();
    auto itb2 = getMapAndFlattenIterator(itb1,EqHelper::LHSIteratorFn(_salg->getOrdering()));
    auto itb3 = getMapAndFlattenIterator(itb2,ReverseLHSIteratorFn(premise));
    auto itb4 = getMapAndFlattenIterator(itb3, [this](pair<Literal*, TermList> arg) {
      return pvi( pushPairIntoRightIterator(arg, _termIndex->getInstances(arg.second, true)) );
    });
    res2 = pvi(getMapAndFlattenIterator(itb4,[this, premise](pair<pair<Literal*, TermList>, TermQueryResult> arg) {
      if(premise == arg.second.clause) {
        return ClauseIterator::getEmpty();
      }

      TermQueryResult& qr = arg.second;
      return perform(qr.clause, qr.literal, qr.term,
        premise, arg.first.first, arg.first.second, qr.substitution, false, qr.constraints);
    }));
  }

  auto it6 = getConcatenatedIterator(res1,res2);
  auto it7 = getFilteredIterator(it6, NonzeroFn());
  return pvi( it7 );
}

ClauseIterator InductionRemodulation::perform(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult, UnificationConstraintStackSP constraints)
{
  CALL("InductionRemodulation::perform");
  // we want the rwClause and eqClause to be active
  // ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);

  // cout << "performRemodulation with " << rwClause->toString() << " and " << eqClause->toString() << endl;
  //   cout << "rwTerm " << rwTerm.toString() << " eqLHS " << eqLHS.toString() << endl;
  //   // cout << "subst " << endl << subst->tryGetRobSubstitution()->toString() << endl;
  //   cout << "eqIsResult " << eqIsResult << endl;

  unsigned rwLength = rwClause->length();
  // ASS_EQ(eqClause->length(), 1);
  unsigned eqLength = eqClause->length();
  unsigned newLength = rwLength + (eqLength - 1);

  ClauseIterator res = ClauseIterator::getEmpty();
  if (eqLHS.isVar()) {
    TermList eqLHSsort = SortHelper::getEqualityArgumentSort(eqLit);
    TermList tgtTermSort = SortHelper::getTermSort(rwTerm, rwLit);
    if (eqLHSsort != tgtTermSort) {
      return res;
    }
  }

  TermList tgtTerm = EqHelper::getOtherEqualitySide(eqLit, eqLHS);
  TermList tgtTermS = eqIsResult ? subst->applyToBoundResult(tgtTerm) : subst->applyToBoundQuery(tgtTerm);
  Literal* eqLitS = eqIsResult ? subst->applyToBoundResult(eqLit) : subst->applyToBoundQuery(eqLit);

  auto comp = _salg->getOrdering().compare(tgtTermS,rwTerm);
  if (comp != Ordering::GREATER && comp != Ordering::GREATER_EQ) {
    ASS_NEQ(comp, Ordering::INCOMPARABLE);
    return res;
  }

  // we should only do the redundancy check if one side is possibly rewritten
  // and the other side doesn't contain the tgtTermS already (since we are
  // rewriting the occurrences one-by-one)
  bool shouldCheckRedundancy = rwLit->isEquality() &&
    ((rwTerm==*rwLit->nthArgument(0) && !rwLit->nthArgument(1)->containsSubterm(tgtTermS)) ||
     (rwTerm==*rwLit->nthArgument(1) && !rwLit->nthArgument(0)->containsSubterm(tgtTermS)));

  SingleOccurrenceReplacement sor(rwLit, rwTerm.term(), tgtTermS);
  Literal* tgtLit = nullptr;
  while ((tgtLit = sor.transformSubset())) {
    Inference inf(GeneratingInference2(InferenceRule::INDUCTION_REMODULATION, rwClause, eqClause));
    Inference::Destroyer inf_destroyer(inf);

    // cout << "LIT " << *ilit << endl;
    if(EqHelper::isEqTautology(tgtLit)) {
      continue;
    }

    inf_destroyer.disable(); // ownership passed to the the clause below
    Clause* newCl = new(newLength) Clause(newLength, inf);

    (*newCl)[0] = tgtLit;
    int next = 1;
    for(unsigned i=0;i<rwLength;i++) {
      Literal* curr=(*rwClause)[i];
      if(curr!=rwLit) {
        (*newCl)[next++] = curr;
      }
    }

    bool destroy = false;
    vset<pair<Literal*,Literal*>> rest;
    for (unsigned i = 0; i < eqLength; i++) {
      Literal *curr = (*eqClause)[i];
      if (curr != eqLit) {
        Literal *currAfter = eqIsResult ? subst->applyToBoundResult(curr) : subst->applyToBoundQuery(curr);
        rest.insert(make_pair(curr, currAfter));

        if (EqHelper::isEqTautology(currAfter)) {
          newCl->destroy();
          destroy = true;
          break;
        }

        (*newCl)[next++] = currAfter;
      }
    }
    if (destroy) {
      continue;
    }

    static const bool checkRedundancy = env.options->inductionRemodulationRedundancyCheck();
    if (checkRedundancy) {
      auto rinfos = RemodulationInfo::update(newCl, tgtLit,
        rwClause->getRemodulationInfo<DHSet<RemodulationInfo>>(), _salg->getOrdering());

      // The following case has to be checked to decide that
      // this rewrite makes the new clauses redundant or not
      //
      // since we only rewrite one occurrence of rwTerm, the case
      // we are looking for is when one side is tgtTermS and the
      // other is unchanged
      static const bool indGen = env.options->inductionGen();
      if (!shouldCheckRedundancy ||
        (tgtTermS!=*tgtLit->nthArgument(0) && tgtTermS!=*tgtLit->nthArgument(1) &&
         // in non-generalized case we check that the rewritten
         // term is not contained anymore in the new literal
         (indGen || !tgtLit->containsSubterm(rwTerm))))
      {
        RemodulationInfo rinfo;
        rinfo._eq = eqLit;
        rinfo._eqGr = eqLitS;
        rinfo._rest = rest;
        rinfo._cl = eqClause;
        rinfos->insert(rinfo);
      }
      // TODO: if -av=off, we should check also that the rest of rwClause is greater than the eqClause

      if (rinfos->isEmpty()) {
        delete rinfos;
      } else {
        newCl->setRemodulationInfo(rinfos);
      }
    }
    newCl->setInductionPhase(2);
    env.statistics->inductionRemodulation++;
    res = pvi(getConcatenatedIterator(res, getSingletonIterator(newCl)));
  }

  return res;
}

}
