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
 * @file InductionRemodulationSubsumption.cpp
 * Implements class InductionRemodulationSubsumption.
 */

#include "Saturation/SaturationAlgorithm.hpp"
#include "InductionRemodulation.hpp"

#include "InductionRemodulationSubsumption.hpp"

namespace Inferences
{
using namespace Lib;
using namespace Kernel;
using namespace Indexing;
using namespace Saturation;

void InductionRemodulationSubsumption::attach(SaturationAlgorithm* salg)
{
  CALL("InductionRemodulationSubsumption::attach");
  ImmediateSimplificationEngine::attach(salg);
  _index=static_cast<InductionRemodulationLiteralIndex*>(
	  _salg->getIndexManager()->request(INDUCTION_REMODULATION_LITERAL_INDEX) );
}

void InductionRemodulationSubsumption::detach()
{
  CALL("InductionRemodulationSubsumption::detach");
  _index=0;
  _salg->getIndexManager()->release(INDUCTION_REMODULATION_LITERAL_INDEX);
  ImmediateSimplificationEngine::detach();
}

Clause* InductionRemodulationSubsumption::simplify(Clause* cl)
{
  CALL("InductionRemodulationSubsumption::simplify");

  if(!cl->isInductionLemma() || cl->length() != 1) {
    return cl;
  }

  // ASS_EQ(cl->length(), 1);
  const auto rinfos = cl->getRemodulationInfo<DHSet<RemodulationInfo>>();
  Clause* res = cl;
  for (unsigned li = 0; li < cl->length(); li++) {
    SLQueryResultIterator it = _index->getGeneralizations( (*cl)[li], false, false);
    if (it.hasNext()) {
      // Since we cannot retract induction formulas,
      // just get rid of the current clause and don't
      // induct on it.
      res = nullptr;
      break;
    }
  }

  return res;
}

}
