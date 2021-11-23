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

#include "Debug/RuntimeStatistics.hpp"

// #include "Lib/DHSet.hpp"
// #include "Lib/Environment.hpp"
// #include "Lib/Int.hpp"
#include "Lib/Metaiterators.hpp"
// #include "Lib/TimeCounter.hpp"
// #include "Lib/Timer.hpp"
// #include "Lib/VirtualIterator.hpp"

// #include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
// #include "Kernel/Inference.hpp"
// #include "Kernel/Ordering.hpp"
// #include "Kernel/Renaming.hpp"
#include "Kernel/SortHelper.hpp"
// #include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
// #include "Kernel/ColorHelper.hpp"
// #include "Kernel/RobSubstitution.hpp"

// #include "Indexing/Index.hpp"
// #include "Indexing/IndexManager.hpp"
// #include "Indexing/TermIndex.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

#include "Shell/Options.hpp"
#include "Shell/Statistics.hpp"
#include "Shell/UnificationWithAbstractionConfig.hpp"

#include "InductionHelper.hpp"

#include "InductionRemodulation.hpp"

namespace Inferences {

using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;


TermList LiteralSubsetReplacement2::transformSubterm(TermList trm)
{
  CALL("LiteralSubsetReplacement2::transformSubterm");

  if(trm.isTerm() && trm.term() == _o){
    if (_iteration == _matchCount++) {
      return _r;
    }
  }
  return trm;
}

Literal* LiteralSubsetReplacement2::transformSubset() {
  CALL("LiteralSubsetReplacement2::transformSubset");
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
  _termIndex=static_cast<InductionTermIndex*>(
	  _salg->getIndexManager()->request(INDUCTION_TERM_INDEX) );
}

void InductionRemodulation::detach()
{
  CALL("InductionRemodulation::detach");
  _lhsIndex = 0;
  _salg->getIndexManager()->release(REMODULATION_LHS_SUBST_TREE);
  _termIndex = 0;
  _salg->getIndexManager()->release(INDUCTION_TERM_INDEX);
  GeneratingInferenceEngine::detach();
}

struct InductionLiteralsFn
{
  InductionLiteralsFn() = default;

  bool operator()(Literal* lit)
  {
    CALL("InductionLiteralsFn()");
    return InductionHelper::isInductionLiteral(lit);
  }
};

struct RewriteableSubtermsFn
{
  VirtualIterator<pair<Literal*, TermList> > operator()(Literal* lit)
  {
    CALL("RewriteableSubtermsFn()");
    NonVariableNonTypeIterator nvi(lit);
    TermIterator it = getUniquePersistentIteratorFromPtr(&nvi);
    return pvi( pushPairIntoRightIterator(lit, it) );
  }
};

struct RewritableResultsFn
{
  RewritableResultsFn(InductionTermIndex* index) : _index(index) {}
  VirtualIterator<pair<pair<Literal*, TermList>, TermQueryResult> > operator()(pair<Literal*, TermList> arg)
  {
    CALL("RewritableResultsFn()");
    return pvi( pushPairIntoRightIterator(arg, _index->getInstances(arg.second, true)) );
  }
private:
  InductionTermIndex* _index;
};


struct ApplicableRewritesFn
{
  ApplicableRewritesFn(RemodulationLHSIndex* index) : _index(index) {}
  VirtualIterator<pair<pair<Literal*, TermList>, TermQueryResult> > operator()(pair<Literal*, TermList> arg)
  {
    CALL("ApplicableRewritesFn()");
    return pvi( pushPairIntoRightIterator(arg, _index->getGeneralizations(arg.second, true)) );
  }
private:
  RemodulationLHSIndex* _index;
};

struct ForwardResultFn
{
  ForwardResultFn(Clause* cl, InductionRemodulation& parent)
    : _cl(cl), _parent(parent) {}

  ClauseIterator operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("ForwardResultFn::operator()");

    TermQueryResult& qr = arg.second;
    return _parent.perform(_cl, arg.first.first, arg.first.second,
	    qr.clause, qr.literal, qr.term, qr.substitution, true, qr.constraints);
  }
private:
  Clause* _cl;
  InductionRemodulation& _parent;
};

struct BackwardResultFn
{
  BackwardResultFn(Clause* cl, InductionRemodulation& parent) : _cl(cl), _parent(parent) {}
  ClauseIterator operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("BackwardResultFn::operator()");

    if(_cl==arg.second.clause) {
      return ClauseIterator::getEmpty();
    }

    TermQueryResult& qr = arg.second;
    return _parent.perform(qr.clause, qr.literal, qr.term,
	    _cl, arg.first.first, arg.first.second, qr.substitution, false, qr.constraints);
  }
private:
  Clause* _cl;
  InductionRemodulation& _parent;
};

struct ReverseLHSIteratorFn {
  VirtualIterator<pair<Literal*, TermList>> operator()(pair<Literal*, TermList> arg)
  {
    CALL("ReverseLHSIteratorFn()");
    auto rhs = EqHelper::getOtherEqualitySide(arg.first, arg.second);
    if (!rhs.containsAllVariablesOf(arg.second)) {
      return VirtualIterator<pair<Literal*, TermList>>::getEmpty();
    }
    NonVariableIterator stit(arg.second.term());
    bool found = false;
    while (stit.hasNext()) {
      auto st = stit.next();
      if (InductionHelper::isInductionTermFunctor(st.term()->functor()) &&
        (InductionHelper::isStructInductionFunctor(st.term()->functor()) ||
         InductionHelper::isIntInductionTermListInLiteral(st, arg.first))) {
          found = true;
          break;
      }
    }
    if (!found) {
      return VirtualIterator<pair<Literal*, TermList>>::getEmpty();
    }
    return pvi(getSingletonIterator(make_pair(arg.first,rhs)));
  }
};

ClauseIterator InductionRemodulation::generateClauses(Clause* premise)
{
  CALL("InductionRemodulation::generateClauses");
  ClauseIterator res1 = ClauseIterator::getEmpty();

  if (InductionHelper::isInductionClause(premise)) {
    // forward result
    auto it1 = premise->getLiteralIterator();
    auto it2 = getFilteredIterator(it1, InductionLiteralsFn());
    auto it3 = getMapAndFlattenIterator(it2, RewriteableSubtermsFn());
    auto it4 = getMapAndFlattenIterator(it3, ApplicableRewritesFn(_lhsIndex));
    res1 = pvi(getMapAndFlattenIterator(it4, ForwardResultFn(premise, *this)));
  }

  // backward result
  ClauseIterator res2 = ClauseIterator::getEmpty();
  if (premise->length() == 1) {
    auto itb1 = premise->getLiteralIterator();
    auto itb2 = getMapAndFlattenIterator(itb1,EqHelper::LHSIteratorFn(_salg->getOrdering()));
    auto itb3 = getMapAndFlattenIterator(itb2,ReverseLHSIteratorFn());
    auto itb4 = getMapAndFlattenIterator(itb3,RewritableResultsFn(_termIndex));
    res2 = pvi(getMapAndFlattenIterator(itb4,BackwardResultFn(premise, *this)));
  }

  auto it6 = getConcatenatedIterator(res1,res2);
  auto it7 = getFilteredIterator(it6, NonzeroFn());
  return pvi( it7 );
}

OccurrenceMap buildOccurrenceMap(const vset<Term*> allowed, Literal* l, const vset<Term*>& rwTerms) {
  OccurrenceMap om;
  Stack<pair<Term*, bool>> todos;
  for (unsigned i = 0; i < l->arity(); i++) {
    todos.push(make_pair(l->nthArgument(i)->term(),false));
  }
  while (todos.isNonEmpty()) {
    auto kv = todos.pop();
    if (rwTerms.count(kv.first)) {
      kv.second = true;
    }
    if (allowed.count(kv.first)) {
      ASS(!rwTerms.count(kv.first));
      om.add(l, kv.first, kv.second);
    }
    for (unsigned i = 0; i < kv.first->arity(); i++) {
      todos.push(make_pair(kv.first->nthArgument(i)->term(), kv.second));
    }
  }
  om.finalize();
  return om;
}

ClauseIterator InductionRemodulation::perform(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult, UnificationConstraintStackSP constraints)
{
  CALL("InductionRemodulation::perform");
  TimeCounter tc(TC_REMODULATION);
  // we want the rwClause and eqClause to be active
  // ASS(rwClause->store()==Clause::ACTIVE);
  ASS(eqClause->store()==Clause::ACTIVE);

  // cout << "performSuperposition with " << rwClause->toString() << " and " << eqClause->toString() << endl;
  //   cout << "rwTerm " << rwTerm.toString() << " eqLHS " << eqLHS.toString() << endl;
  //   // cout << "subst " << endl << subst->tryGetRobSubstitution()->toString() << endl;
  //   cout << "eqIsResult " << eqIsResult << endl;

  // the first checks the reference and the second checks the stack
  bool hasConstraints = !constraints.isEmpty() && !constraints->isEmpty();

  unsigned rwLength = rwClause->length();
  ASS_EQ(eqClause->length(), 1);
  unsigned conLength = hasConstraints ? constraints->size() : 0;
  unsigned newLength = rwLength + conLength;

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

  if(!Ordering::isGorGEorE(_salg->getOrdering().compare(tgtTermS,rwTerm))) {
    return res;
  }

  vset<Term*> newAllowed;
  NonVariableIterator stit(tgtTerm.term());
  // cout << "NEWALLOWED ";
  while (stit.hasNext()) {
    auto st = stit.next();
    auto t = (eqIsResult ? subst->applyToBoundResult(st) : subst->applyToBoundQuery(st)).term();
    // cout << *t << " ";
    newAllowed.insert(t);
  }
  // cout << endl;
  vset<Term*> allowed;
  vset<Term*> rewrites;
  if (rwClause->inference().rule() == InferenceRule::INDUCTION_REMODULATION) {
    auto ptr = static_cast<RemodulationInfo*>(rwClause->getRemodulationInfo());
    if (ptr) {
      // cout << "ALLOWED ";
      for (const auto& e : ptr->_allowed) {
        // cout << *e << " ";
        if (e != rwTerm.term() && !e->containsSubterm(rwTerm)) {
          allowed.insert(e);
        }
      }
      rewrites = ptr->_rewrites;
      // cout << endl;
    }
  }
  rewrites.insert(tgtTermS.term());
  vset<Term*> newAllowed2;
  if (!allowed.empty()) {
    for (const auto& e : allowed) {
      if (newAllowed.count(e)) {
        newAllowed2.insert(e);
      }
    }
  } else {
    newAllowed2 = newAllowed;
  }

  if (newAllowed2.empty()) {
    return res;
  }

  LiteralSubsetReplacement2 subsetReplacement(rwLit, rwTerm.term(), tgtTermS);
  Literal* ilit = nullptr;
  while ((ilit = subsetReplacement.transformSubset())) {
    Inference inf(GeneratingInference2(InferenceRule::INDUCTION_REMODULATION, rwClause, eqClause));
    Inference::Destroyer inf_destroyer(inf);

    // cout << "LIT " << *ilit << endl;
    if(EqHelper::isEqTautology(ilit)) {
      continue;
    }

    inf_destroyer.disable(); // ownership passed to the the clause below
    Clause* newCl = new(newLength) Clause(newLength, inf);

    (*newCl)[0] = ilit;
    int next = 1;
    for(unsigned i=0;i<rwLength;i++) {
      Literal* curr=(*rwClause)[i];
      if(curr!=rwLit) {
        (*newCl)[next++] = curr;
      }
    }

    newCl->setInductionLemma(true);
    auto rinfo = new RemodulationInfo();
    rinfo->_allowed = newAllowed2;
    rinfo->_rewrites = rewrites;
    rinfo->_om = buildOccurrenceMap(newAllowed2, ilit, rewrites);
    newCl->setRemodulationInfo(rinfo);
    res = pvi(getConcatenatedIterator(res, getSingletonIterator(newCl)));
  }

  return res;
}

}
