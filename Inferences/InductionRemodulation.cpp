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
    // Replace either if there are too many occurrences to try all possibilities,
    // or if the bit in _iteration corresponding to this match is set to 1.
    if ((_occurrences > _maxOccurrences) || (1 & (_iteration >> _matchCount++))) {
      return _r;
    }
  }
  return trm;
}

Literal* LiteralSubsetReplacement2::transformSubset() {
  CALL("LiteralSubsetReplacement2::transformSubset");
  // Increment _iteration, since it either is 0, or was already used.
  _iteration++;
  static unsigned maxSubsetSize = env.options->maxInductionGenSubsetSize();
  // Note: __builtin_popcount() is a GCC built-in function.
  unsigned setBits = __builtin_popcount(_iteration);
  // Skip this iteration if not all bits are set, but more than maxSubset are set.
  while ((_iteration <= _maxIterations) &&
         ((maxSubsetSize > 0) && (setBits < _occurrences) && (setBits > maxSubsetSize))) {
    _iteration++;
    setBits = __builtin_popcount(_iteration);
  }
  if ((_iteration >= _maxIterations) ||
      ((_occurrences > _maxOccurrences) && (_iteration > 1))) {
    // All combinations were already returned.
    return nullptr;
  }
  _matchCount = 0;
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
  _splitter = _salg->getSplitter();
  _dupLitRemoval->attach(salg);
}

void InductionRemodulation::detach()
{
  CALL("InductionRemodulation::detach");
  _dupLitRemoval->detach();
  _splitter = 0;
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
  RewriteableSubtermsFn(Ordering& ord) : _ord(ord) {}

  VirtualIterator<pair<Literal*, TermList> > operator()(Literal* lit)
  {
    CALL("RewriteableSubtermsFn()");
    NonVariableNonTypeIterator nvi(lit);
    TermIterator it = getUniquePersistentIteratorFromPtr(&nvi);
    // TermIterator it = EqHelper::getSubtermIterator(lit, _ord);
    return pvi( pushPairIntoRightIterator(lit, it) );
  }

private:
  Ordering& _ord;
};

struct RewritableResultsFn
{
  RewritableResultsFn(InductionTermIndex* index) : _index(index) {}
  VirtualIterator<pair<pair<Literal*, TermList>, TermQueryResult> > operator()(pair<Literal*, TermList> arg)
  {
    CALL("RewritableResultsFn()");
    // cout << "GETINST " << arg.second << endl;
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
    // cout << "rw " << arg.second << endl;
    return pvi( pushPairIntoRightIterator(arg, _index->getGeneralizations(arg.second, true)) );
  }
private:
  RemodulationLHSIndex* _index;
};

struct ForwardResultFn
{
  ForwardResultFn(Clause* cl, InductionRemodulation& parent, unsigned depth, vset<Term*> allowed)
    : _cl(cl), _parent(parent), _depth(depth), _allowed(allowed) {}

  ClauseIterator operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("ForwardResultFn::operator()");

    TermQueryResult& qr = arg.second;
    return _parent.perform(_cl, arg.first.first, arg.first.second,
	    qr.clause, qr.literal, qr.term, qr.substitution, true, _allowed, qr.constraints, _depth);
  }
private:
  Clause* _cl;
  InductionRemodulation& _parent;
  unsigned _depth;
  vset<Term*> _allowed;
};

struct BackwardResultFn
{
  BackwardResultFn(Clause* cl, InductionRemodulation& parent, unsigned depth) : _cl(cl), _parent(parent), _depth(depth) {}
  ClauseIterator operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    CALL("BackwardResultFn::operator()");

    if(_cl==arg.second.clause) {
      return ClauseIterator::getEmpty();
    }

    TermQueryResult& qr = arg.second;
    return _parent.perform(qr.clause, qr.literal, qr.term,
	    _cl, arg.first.first, arg.first.second, qr.substitution, false, vset<Term*>(), qr.constraints, _depth);
  }
private:
  Clause* _cl;
  InductionRemodulation& _parent;
  unsigned _depth;
};

struct ReverseLHSIteratorFn {
  VirtualIterator<pair<Literal*, TermList>> operator()(pair<Literal*, TermList> arg)
  {
    CALL("ReverseLHSIteratorFn()");
    auto rhs = EqHelper::getOtherEqualitySide(arg.first, arg.second);
    if (!rhs.containsAllVariablesOf(arg.second)) {
      return VirtualIterator<pair<Literal*, TermList>>::getEmpty();
    }
    // cout << "LHS " << arg.second << endl;
    // NonVariableIterator stit(arg.second.term());
    // bool found = false;
    // while (stit.hasNext()) {
    //   auto st = stit.next();
    //   if (InductionHelper::isInductionTermFunctor(st.term()->functor()) &&
    //     (InductionHelper::isStructInductionFunctor(st.term()->functor()) ||
    //      InductionHelper::isIntInductionTermListInLiteral(st, arg.first))) {
    //       cout << "INDTERM IN LHS " << st << endl;
    //       found = true;
    //       break;
    //   }
    // }
    // if (!found) {
    //   return VirtualIterator<pair<Literal*, TermList>>::getEmpty();
    // }
    // cout << "EQUALITY " << *arg.first << " " << rhs << endl;
    return pvi(getSingletonIterator(make_pair(arg.first,rhs)));
  }
};

struct PrintFn {
  pair<pair<Literal*, TermList>, TermQueryResult> operator()(pair<pair<Literal*, TermList>, TermQueryResult> arg)
  {
    cout << "RW " << *arg.first.first << " " << arg.first.second << " " << arg.second.term << endl;
    return arg;
  }
};

ClauseIterator InductionRemodulation::generateClauses(Clause* premise, unsigned depth, vset<Term*> allowed)
{
  CALL("InductionRemodulation::generateClauses");
  ClauseIterator res1 = ClauseIterator::getEmpty();
  // cout << "DEPTH " << depth << endl;
  if (++depth > 2) {
    return res1;
  }

  if (InductionHelper::isInductionClause(premise)) {
    // forward result
    auto it1 = premise->getLiteralIterator();
    auto it2 = getFilteredIterator(it1, InductionLiteralsFn());
    auto it3 = getMapAndFlattenIterator(it2, RewriteableSubtermsFn(_salg->getOrdering()));
    auto it4 = getMapAndFlattenIterator(it3, ApplicableRewritesFn(_lhsIndex));
    res1 = pvi(getMapAndFlattenIterator(it4, ForwardResultFn(premise, *this, depth, allowed)));
  }

  // backward result
  ClauseIterator res2 = ClauseIterator::getEmpty();
  if (premise->length() == 1 && depth == 1) {
    auto itb1 = premise->getLiteralIterator();
    auto itb2 = getMapAndFlattenIterator(itb1,EqHelper::LHSIteratorFn(_salg->getOrdering()));
    auto itb3 = getMapAndFlattenIterator(itb2,ReverseLHSIteratorFn());
    auto itb4 = getMapAndFlattenIterator(itb3,RewritableResultsFn(_termIndex));
    // auto ito = getMappingIterator(itb4,PrintFn());
    res2 = pvi(getMapAndFlattenIterator(itb4,BackwardResultFn(premise, *this, depth)));
  }

  auto it6 = getConcatenatedIterator(res1,res2);
  auto it7 = getFilteredIterator(it6, NonzeroFn());
  return pvi( it7 );
}

ClauseIterator InductionRemodulation::perform(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult,
    vset<Term*> allowed, UnificationConstraintStackSP constraints, unsigned depth)
{
  CALL("InductionRemodulation::perform");
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
  while (stit.hasNext()) {
    auto st = stit.next();
    auto t = (eqIsResult ? subst->applyToBoundResult(st) : subst->applyToBoundQuery(st)).term();
    // if (InductionHelper::isInductionTermFunctor(t->functor()) &&
    //     (InductionHelper::isStructInductionFunctor(t->functor())/*  ||
    //      InductionHelper::isIntInductionTermListInLiteral(st, arg.first) */)) {
    //       // cout << "INDTERM IN LHS " << st << endl;
      newAllowed.insert(t);
    // }
  }
  // cout << "NEWALLOWED ";
  // for (const auto& t : newAllowed) {
  //   cout << *t << " ";
  // }
  // cout << endl;
  // cout << "ALLOWED ";
  // for (const auto& t : allowed) {
  //   cout << *t << " ";
  // }
  // cout << endl;
  for (auto it = allowed.begin(); it != allowed.end();) {
    if ((*it) == rwTerm.term() || (*it)->containsSubterm(rwTerm)) {
      it = allowed.erase(it);
    } else {
      it++;
    }
  }
  if (allowed.empty()) {
    allowed = newAllowed;
  } else {
    vset<Term*> newAllowed2;
    for (const auto& t : allowed) {
      if (newAllowed.count(t)) {
        newAllowed2.insert(t);
      }
    }
    allowed = newAllowed2;
  }

  if (allowed.empty()) {
    return res;
  }
  // cout << "ALLOWED2 ";
  // for (const auto& t : allowed) {
  //   cout << *t << " ";
  // }
  // cout << endl;

  LiteralSubsetReplacement2 subsetReplacement(rwLit, rwTerm.term(), tgtTermS);
  Literal* ilit = nullptr;
  while ((ilit = subsetReplacement.transformSubset())) {
    Inference inf(GeneratingInference2(InferenceRule::INDUCTION_REMODULATION, rwClause, eqClause));
    Inference::Destroyer inf_destroyer(inf);

    // cout << "LIT " << *ilit << endl;
    if(EqHelper::isEqTautology(ilit)) {
      return res;
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

    if(hasConstraints){
      for(unsigned i=0;i<constraints->size();i++){
        UnificationConstraint con = (*constraints)[i];

        TermList qT = subst->applyTo(con.first.first,con.first.second);
        TermList rT = subst->applyTo(con.second.first,con.second.second);

        TermList sort = SortHelper::getResultSort(rT.term());
        Literal* constraint = Literal::createEquality(false,qT,rT,sort);

        static Options::UnificationWithAbstraction uwa = env.options->unificationWithAbstraction();
        if(uwa==Options::UnificationWithAbstraction::GROUND && 
          !constraint->ground() &&
          (!UnificationWithAbstractionConfig::isInterpreted(qT) 
            && !UnificationWithAbstractionConfig::isInterpreted(rT) )) {

          // the unification was between two uninterpreted things that were not ground 
          newCl->destroy();
          return res;
        }

        (*newCl)[next] = constraint;
        next++;   
      }
    }

    if (_splitter) {
      _splitter->onNewClause(newCl);
    }
    auto temp = _dupLitRemoval->simplify(newCl);
    if (temp != newCl) {
      if (_splitter) {
        _splitter->onNewClause(newCl);
      }
      newCl = temp;
    }

    _induction->setAllowed(allowed);
    auto indIt = _induction->generateClauses(newCl);
    _induction->clearAllowed();
    res = pvi(getConcatenatedIterator(res, getConcatenatedIterator(generateClauses(newCl, depth, allowed), indIt)));
  }

  return res;
}

}
