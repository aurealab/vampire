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

  if(!cl->isInductionLemma()) {
    return cl;
  }

  ASS_EQ(cl->length(), 1);
  auto rinfos = static_cast<DHSet<RemodulationInfo>*>(cl->getRemodulationInfo());
  Clause* res = cl;
  for (unsigned li = 0; li < cl->length(); li++) {
    SLQueryResultIterator it = _index->getGeneralizations( (*cl)[li], false, false);
    while (it.hasNext()) {
      res = nullptr; // for now since all clauses are unit, delete the original clause
      Clause* premise = it.next().clause;
      ASS(premise->isInductionLemma());
      // cout << "subsumed: " << *cl << endl;
      // cout << "by:       " << *premise << endl;
      if (!rinfos || rinfos->isEmpty()) {
        break; // exit if there is nothing to update the other clause with
      }
      auto rinfosP = static_cast<DHSet<RemodulationInfo>*>(premise->getRemodulationInfo());
      if (!rinfosP) {
        rinfosP = new DHSet<RemodulationInfo>();
        premise->setRemodulationInfo(rinfosP);
      }
      DHSet<RemodulationInfo>::Iterator rit(*rinfos);
      while (rit.hasNext()) {
        auto rinfo = rit.next();
        rinfosP->insert(rinfo);
      }
    }
  }

  return res;
}

}
