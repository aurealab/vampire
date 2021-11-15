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
    _maxIterations = pow(2, _occurrences);
  }

  Literal* transformSubset();

protected:
  virtual TermList transformSubterm(TermList trm);

private:
  // _iteration serves as a map of occurrences to replace
  unsigned _iteration = 0;
  unsigned _maxIterations;
  // Counts how many occurrences were already encountered in one transformation
  unsigned _matchCount = 0;
  unsigned _occurrences;
  const unsigned _maxOccurrences = 20;
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
    : _lhsIndex(), _termIndex(),
      _induction(induction), _splitter(),
      _dupLitRemoval(new DuplicateLiteralRemovalISE()) {}

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  ClauseIterator generateClauses(Clause* premise) override {
    // cout << "START " << *premise << endl;
    return generateClauses(premise, 0, vset<Term*>());
  }
  ClauseIterator generateClauses(Clause* premise, unsigned depth, vset<Term*> allowed);
  ClauseIterator perform(
    Clause* rwClause, Literal* rwLit, TermList rwTerm,
    Clause* eqClause, Literal* eqLit, TermList eqLHS,
    ResultSubstitutionSP subst, bool eqIsResult,
    vset<Term*> allowed,
    UnificationConstraintStackSP constraints, unsigned depth);
private:
  RemodulationLHSIndex* _lhsIndex;
  InductionTermIndex* _termIndex;
  GeneralInduction* _induction;
  Splitter* _splitter;
  unique_ptr<DuplicateLiteralRemovalISE> _dupLitRemoval;
};

};

#endif /*__InductionRemodulation__*/
