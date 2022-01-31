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
 * @file InductionForwardRewriting.hpp
 * Defines class InductionForwardRewriting.
 */

#ifndef __InductionForwardRewriting__
#define __InductionForwardRewriting__

#include "Forwards.hpp"
#include "Indexing/TermIndex.hpp"

#include "Saturation/SaturationAlgorithm.hpp"

namespace Inferences {

class InductionForwardRewriting
  : public GeneratingInferenceEngine
  {
public:
  CLASS_NAME(InductionForwardRewriting);
  USE_ALLOCATOR(InductionForwardRewriting);

  void attach(SaturationAlgorithm* salg) override
  {
    GeneratingInferenceEngine::attach(salg);
    _index=static_cast<RewritingLHSIndex*>(
      _salg->getIndexManager()->request(REWRITING_LHS_INDEX));
    _tindex=static_cast<RemodulationSubtermIndex*>(
      _salg->getIndexManager()->request(REMODULATION_SUBTERM_INDEX));
  }
  void detach() override
  {
    _index=0;
    _tindex = 0;
    _salg->getIndexManager()->release(REMODULATION_SUBTERM_INDEX);
    _salg->getIndexManager()->release(REWRITING_LHS_INDEX);
    GeneratingInferenceEngine::detach();
  }
  ClauseIterator generateClauses(Clause *premise) override;

private:
  static Clause *perform(
      Clause *rwClause, Literal *rwLiteral, TermList rwTerm,
      Clause *eqClause, Literal *eqLiteral, TermList eqLHS,
      ResultSubstitutionSP subst, bool eqIsResult, Ordering& ord);

  RewritingLHSIndex* _index;
  RemodulationSubtermIndex* _tindex;
};

}; // namespace Inferences

#endif /* __InductionForwardRewriting__ */
