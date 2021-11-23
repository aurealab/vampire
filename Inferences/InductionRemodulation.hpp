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

  InductionRemodulation(GeneralInduction* induction)
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

  InductionSGIWrapper(GeneralInduction* induction, InductionRemodulation* inductionRemodulation, SimplifyingGeneratingInference* generator)
    : _induction(induction), _inductionRemodulation(inductionRemodulation), _generator(generator) {}

  ClauseGenerationResult generateSimplify(Clause* premise) override {
    if (!premise->isInductionLemma()) {
      return _generator->generateSimplify(premise);
    }
    ClauseIterator clIt = _induction->generateClauses(premise);
    clIt = pvi(getConcatenatedIterator(clIt, _inductionRemodulation->generateClauses(premise)));
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
};

struct RemodulationInfo {
  CLASS_NAME(RemodulationInfo);
  USE_ALLOCATOR(RemodulationInfo);

  OccurrenceMap _om;
  vset<Term*> _rewrites;
  vset<Term*> _allowed;
};

}

#endif /*__InductionRemodulation__*/
