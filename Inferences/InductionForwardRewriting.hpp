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

namespace Inferences {

using namespace Kernel;
using namespace Shell;
using namespace Indexing;

class InductionForwardRewriting
  : public GeneratingInferenceEngine
  {
public:
  CLASS_NAME(InductionForwardRewriting);
  USE_ALLOCATOR(InductionForwardRewriting);

  void attach(SaturationAlgorithm* salg) override
  {
    GeneratingInferenceEngine::attach(salg);
    _index=static_cast<DemodulationLHSIndex*>(
      _salg->getIndexManager()->request(DEMODULATION_LHS_SUBST_TREE));
  }
  void detach() override
  {
    _index=0;
    _salg->getIndexManager()->release(DEMODULATION_LHS_SUBST_TREE);
    GeneratingInferenceEngine::detach();
  }
  ClauseIterator generateClauses(Clause *premise) override;

private:
  static Clause *perform(
      Clause *rwClause, Literal *rwLiteral, TermList rwTerm,
      Clause *eqClause, Literal *eqLiteral, TermList eqLHS,
      ResultSubstitutionSP subst, Ordering& ord);

  struct ForwardResultFn;
  struct RewriteableSubtermsFn;
  struct GeneralizationsFn;

  DemodulationLHSIndex* _index;
};

}; // namespace Inferences

#endif /* __InductionForwardRewriting__ */
