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
 * @file InductionSchemeGenerator.hpp
 * Defines classes for generating induction schemes from function terms
 */

#ifndef __InductionSchemeGenerator__
#define __InductionSchemeGenerator__

#include "Forwards.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermTransformer.hpp"
#include "InductionPreprocessor.hpp"
#include "Lib/STL.hpp"

#include "Inferences/InductionHelper.hpp"

#include <bitset>

namespace Shell {

using namespace Kernel;
using namespace Lib;
using namespace Indexing;

/* Provides a wrapper for a bit vector. After setting its bits and size, it
 * can iterate through all combinations of bit vectors masking its 1 bits. */
class Occurrences {
public:
  Occurrences(bool initial)
    : _occ(1 & initial), _iter(), _max(1 << 1), _finished(false) {}

  void add(bool val) {
    ASS(!_finished);
    if (_max & ((uint64_t)1 << 63)) {
      return;
    }
    _occ <<= 1;
    _max <<= 1;
    _occ |= (1 & val);
  }

  // reverse the bit vector
  void finalize() {
    ASS(!_finished);
    _finished = true;
    const auto c = num_bits();
    auto temp = _occ;
    _occ = 0;
    for (uint64_t i = 0; i < c; i++) {
      _occ <<= 1;
      _occ |= temp & 1;
      temp >>= 1;
    }
    _iter = _occ;
  }

  // iterate to the next bit vector
  bool next() {
    ASS(_finished);
    _iter++;
    _iter |= _occ; // mask initial bits
    return _iter < _max;
  }

  bool pop_last() {
    ASS(_finished);
    ASS(_max);
    bool res = _iter & 1;
    _iter >>= 1;
    _max >>= 1;
    return res;
  }

  uint64_t val() {
    ASS(_finished);
    return _iter;
  }

  uint64_t num_bits() const {
    ASS(_finished);
    ASS(_max);
    return __builtin_ctz(_max);
  }

  uint64_t num_set_bits() const {
    return __builtin_popcount(_occ);
  }

  void set_bits() {
    _iter = _max - 1;
  }

  void reset_bits() {
    _iter = _occ;
  }

  vstring toString() const {
    vstringstream str;
    auto temp = _iter;
    for (uint64_t i = 0; i < num_bits(); i++) {
      str << (temp & 1);
      temp >>= 1;
    }
    if (_iter >= _max) {
      str << '!';
    }
    return str.str();
  }

private:
  uint64_t _occ;
  uint64_t _iter;
  uint64_t _max;
  bool _finished;
};

class OccurrenceMap {
public:
  void add(Literal* l, Term* t, bool active) {
    CALL("OccurrenceMap::add");

    auto p = make_pair(l, t);
    auto oIt = _m.find(p);
    if (oIt == _m.end()) {
      _m.insert(make_pair(p, Occurrences(active)));
    } else {
      oIt->second.add(active);
    }
  }

  void finalize() {
    CALL("OccurrenceMap::finalize");

    for (auto& o : _m) {
      o.second.finalize();
    }
  }

  OccurrenceMap create_necessary(const InductionScheme& sch) {
    CALL("OccurrenceMap::create_necessary");

    OccurrenceMap necessary;
    for (const auto& kv : _m) {
      if (sch.inductionTerms().count(kv.first.second)) {
        necessary._m.insert(kv);
      }
    }
    return necessary;
  }

  vmap<pair<Literal*, Term*>, Occurrences> _m;
};

struct InductionPremise {
  InductionPremise(Literal* l, Clause* c, bool o = false) : literal(l), clause(c), originalPremise(o) {}

  Literal* literal;
  Clause* clause;
  bool originalPremise;

  vstring toString() const {
    vstring res = literal->toString() + " (" +
      (clause ? clause->toString() : "no clause") + ") " +
      (originalPremise ? "OP" : "not OP");
    return res;
  }

  friend bool operator<(const InductionPremise& lhs, const InductionPremise& rhs) {
    return ((lhs.literal < rhs.literal) ||
            ((lhs.literal == rhs.literal) && (lhs.clause < rhs.clause)));
  }
  
  friend bool operator==(const InductionPremise& lhs, const InductionPremise& rhs) {
    return (lhs.literal == rhs.literal) && (lhs.clause == rhs.clause);
  }
};

struct InductionPremises {
  InductionPremises(const InductionPremise& mainPremise)
      : _main(mainPremise), _sides(), _bounds() {}

  vstring toString() const {
    vstring res = "main: " + _main.toString() + "; sides: [";
    bool first = true;
    for (const auto& side : _sides) {
      res += (first ? " " : ", ") + side.toString();
      first = false;
    }
    res += " ]; bounds: [";
    first = true;
    for (const auto& bound : _bounds) {
      res += (first ? " " : ", ") + bound.toString();
      first = false;
    }
    res += " ]";
    return res;
  }

  void addPremise(Literal* l, Clause* c, bool originalPremise, bool bound) {
    if (l == _main.literal && c == _main.clause) {
      return;
    }
    ASS(!originalPremise || !_main.originalPremise);
    if (bound) {
      if (_bounds.emplace(l, c, originalPremise).second) {
        ASS(!originalPremise || !_boundsHaveOriginalPremise);
        _boundsHaveOriginalPremise = _boundsHaveOriginalPremise || originalPremise;
      }
    } else {
      if (_sides.emplace(l, c, originalPremise).second) {
        ASS(!originalPremise || !_sidesHaveOriginalPremise);
        _sidesHaveOriginalPremise = _sidesHaveOriginalPremise || originalPremise;
      }
    }
  }

  void addSidePremise(Literal* l, Clause* c, bool originalPremise = false) {
    if (Inferences::InductionHelper::isMainSidePair(_main.literal, _main.clause, l, c)) {
      addPremise(l, c, originalPremise, false);
    }
  }

  void addBound(Literal* l, Clause* c, bool originalPremise = false) {
    if (!_sides.count(InductionPremise(l, c))) {
      addPremise(l, c, originalPremise, true);
    }
  }

  const InductionPremise& main() const { return _main; }
  const vset<InductionPremise>& sides() const { return _sides; }
  const vset<InductionPremise>& bounds() const { return _bounds; }
  bool sidesHaveOriginalPremise() const { return _sidesHaveOriginalPremise; }
  bool boundsHaveOriginalPremise() const { return _boundsHaveOriginalPremise; }

private:
  InductionPremise _main;
  vset<InductionPremise> _sides;
  vset<InductionPremise> _bounds;
  bool _sidesHaveOriginalPremise = false;
  bool _boundsHaveOriginalPremise = false;
};

/**
 * This class instantiates the induction templates from a literal
 * we want to induct on. Afterwards, stores these and filters them.
 * Also stores all active occurrences of possible induction terms.
 */
struct InductionSchemeGenerator {
  virtual ~InductionSchemeGenerator() = default;
  virtual void generate(
    const InductionPremises& premises,
    vvector<pair<InductionScheme, OccurrenceMap>>& res) = 0;
  virtual bool setsFixOccurrences() const { return false; }
  virtual bool usesBounds() const { return false; }
};

struct RecursionInductionSchemeGenerator
  : public InductionSchemeGenerator
{
  CLASS_NAME(RecursionInductionSchemeGenerator);
  USE_ALLOCATOR(RecursionInductionSchemeGenerator);

  void generate(
    const InductionPremises& premises,
    vvector<pair<InductionScheme, OccurrenceMap>>& res) override;
  bool setsFixOccurrences() const override { return true; }

private:
  void generate(Clause* premise, Literal* lit);
  void process(Term* t, bool active, Stack<bool>& actStack, Literal* lit);
  void process(Literal* lit, Stack<bool>& actStack);
  void handleActiveTerm(Term* t, InductionTemplate& templ, Stack<bool>& actStack);

  vset<InductionScheme> _schemes;
  OccurrenceMap _actOccMaps;
};

struct StructuralInductionSchemeGenerator
  : public InductionSchemeGenerator
{
  CLASS_NAME(StructuralInductionSchemeGenerator);
  USE_ALLOCATOR(StructuralInductionSchemeGenerator);

  void generate(
    const InductionPremises& premises,
    vvector<pair<InductionScheme, OccurrenceMap>>& res) override;
};

struct IntegerInductionSchemeGenerator
  : public InductionSchemeGenerator
{
  CLASS_NAME(IntegerInductionSchemeGenerator);
  USE_ALLOCATOR(IntegerInductionSchemeGenerator);

  void generate(
    const InductionPremises& premises,
    vvector<pair<InductionScheme, OccurrenceMap>>& res) override;
  bool usesBounds() const override { return true; }

 private:
  void getIntegerInductionSchemes(Term* t,
      const vvector<pair<TermList*, const InductionPremise*>>& bounds1,
      const vvector<pair<TermList*, const InductionPremise*>>& bounds2,
      bool upward,
      bool mainIsOriginalPremise,
      vvector<InductionScheme>& schemes);

  vvector<InductionScheme::Case>* getCasesForBoundAndDirection(
      const TermList& bound, bool upward);

  void makeAndPushScheme(vmap<Term*, unsigned>& inductionTerms,
      vvector<InductionScheme::Case>* cases,
      Literal* bound1, Literal* optionalBound2,
      vvector<InductionScheme>& schemes,
      bool upward, bool defaultBound = false, bool secondDefaultBound = false) ;

  vmap<pair<const Term*, bool /*upwards*/>, vvector<InductionScheme::Case>> _baseCaseMap;
};

} // Shell

#endif