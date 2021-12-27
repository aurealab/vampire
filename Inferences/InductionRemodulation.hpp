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
 * @file InductionRemodulation.hpp
 * Defines class InductionRemodulation
 *
 */

#ifndef __InductionRemodulation__
#define __InductionRemodulation__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "InferenceEngine.hpp"
#include "GeneralInduction.hpp"
#include "InductionHelper.hpp"
#include "InductionForwardRewriting.hpp"
#include "InductionRemodulationSubsumption.hpp"
#include "Indexing/LiteralSubstitutionTree.hpp"
#include "Kernel/EqHelper.hpp"
#include "Lib/SharedSet.hpp"

namespace Inferences
{

using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

class LiteralSubsetReplacement2 : TermTransformer {
public:
  LiteralSubsetReplacement2(Literal* lit, Term* o, TermList r)
      : _lit(lit), _o(o), _r(r) {
    _occurrences = _lit->countSubtermOccurrences(TermList(_o));
  }

  Literal* transformSubset();

protected:
  virtual TermList transformSubterm(TermList trm);

private:
  // _iteration serves as a map of occurrences to replace
  unsigned _iteration = 0;
  // Counts how many occurrences were already encountered in one transformation
  unsigned _matchCount = 0;
  unsigned _occurrences;
  Literal* _lit;
  Term* _o;
  TermList _r;
};

class InductionRemodulation
: public GeneratingInferenceEngine
{
public:
  CLASS_NAME(InductionRemodulation);
  USE_ALLOCATOR(InductionRemodulation);

  InductionRemodulation()
    : _lhsIndex(), _termIndex() {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  ClauseIterator generateClauses(Clause* premise) override;
  ClauseIterator perform(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult,
    UnificationConstraintStackSP constraints);
private:
  RemodulationLHSIndex* _lhsIndex;
  InductionTermIndex* _termIndex;
};

class InductionSGIWrapper
: public SimplifyingGeneratingInference
{
public:
  CLASS_NAME(InductionSGIWrapper);
  USE_ALLOCATOR(InductionSGIWrapper);

  InductionSGIWrapper(GeneralInduction* induction, InductionRemodulation* inductionRemodulation,
      SimplifyingGeneratingInference* generator, InductionForwardRewriting* rewriting)
    : _induction(induction), _inductionRemodulation(inductionRemodulation), _generator(generator),
      _rewriting(rewriting) {}

  ClauseGenerationResult generateSimplify(Clause* premise) override {
    if (!premise->isInductionLemma()) {
      return _generator->generateSimplify(premise);
    }
    ASS(InductionHelper::isInductionClause(premise));
    ASS_EQ(premise->length(), 1);
    ASS(InductionHelper::isInductionLiteral((*premise)[0]));
    ClauseIterator clIt = _induction->generateClauses(premise);
    clIt = pvi(getConcatenatedIterator(clIt, _inductionRemodulation->generateClauses(premise)));
    clIt = pvi(getConcatenatedIterator(clIt, _rewriting->generateClauses(premise)));
    return ClauseGenerationResult {
      .clauses          = clIt,
      .premiseRedundant = false,
    };
  }
  void attach(SaturationAlgorithm* salg) override
  {
    _generator->attach(salg);
  }
  void detach() override
  {
    _generator->detach();
  }
private:
  GeneralInduction* _induction;
  InductionRemodulation* _inductionRemodulation;
  ScopedPtr<SimplifyingGeneratingInference> _generator;
  InductionForwardRewriting* _rewriting;
};

struct RemodulationInfo {
  Literal* _eq;
  Literal* _eqGr;
  vset<pair<Literal*,Literal*>> _rest;

  bool operator==(const RemodulationInfo& other) const {
    return _eq == other._eq && _eqGr == other._eqGr && _rest == other._rest;
  }
  bool operator!=(const RemodulationInfo& other) const {
    return !operator==(other);
  }

  static DHSet<RemodulationInfo>* update(Clause* cl, Literal* lit, DHSet<RemodulationInfo>* rinfos, Ordering& ord) {
    auto res = new DHSet<RemodulationInfo>();
    if (rinfos) {
      DHSet<RemodulationInfo>::Iterator it(*rinfos);
      while (it.hasNext()) {
        auto rinfo = it.next();
        // we have to check that each greater side is contained
        auto lhsIt = EqHelper::getLHSIterator(rinfo._eqGr, ord);
        ASS(lhsIt.hasNext());
        TermList lhs = lhsIt.next();
        ASS(!lhsIt.hasNext());
        // TODO check also rest literals from rinfo
        if (lit->containsSubterm(lhs)) {
          res->insert(rinfo);
        }
      }
    }
    return res;
  }
};

}

#endif /*__InductionRemodulation__*/
