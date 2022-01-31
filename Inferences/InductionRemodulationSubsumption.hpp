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
 * @file InductionRemodulationSubsumption.hpp
 * Defines class InductionRemodulationSubsumption.
 */

#ifndef __InductionRemodulationSubsumption__
#define __InductionRemodulationSubsumption__

#include "Forwards.hpp"
#include "InferenceEngine.hpp"
#include "Indexing/LiteralIndex.hpp"

namespace Inferences {

class InductionRemodulationSubsumption
: public ImmediateSimplificationEngine
{
public:
  CLASS_NAME(InductionRemodulationSubsumption);
  USE_ALLOCATOR(InductionRemodulationSubsumption);

  void attach(SaturationAlgorithm* salg) override;
  void detach() override;
  Clause* simplify(Clause* cl) override;

private:
  InductionRemodulationLiteralIndex* _index;
};

};

#endif /* __InductionRemodulationSubsumption__ */
