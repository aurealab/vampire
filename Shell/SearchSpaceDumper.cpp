#ifdef __FEATURE_SEARCH_SPACE_DUMPER

#include "SearchSpaceDumper.hpp"
#include <iostream>
#include "Forwards.hpp"
#include "Lib/Environment.hpp"
#include "Shell/Options.hpp"
#include "Lib/json.hpp"
#include "Kernel/Signature.hpp"
#include <vector>
#include <fstream>

using namespace nlohmann;
using namespace Kernel;
using namespace Shell;
using namespace std;
using Symbol =  Signature::Symbol;

#define UNIMPLEMENTED ASSERTION_VIOLATION

namespace Shell {

SearchSpaceDumper* SearchSpaceDumper::_instance = NULL;

SearchSpaceDumper* SearchSpaceDumper::instance() {
  return _instance;
}

void SearchSpaceDumper::init() {
  ASS(!(_instance))
  _instance = new SearchSpaceDumper();
}

SearchSpaceDumper::SearchSpaceDumper() : _clauses(decltype(_clauses)())
{ 
}

SearchSpaceDumper::~SearchSpaceDumper()
{ 
  for (auto c : _clauses) {
    c->decRefCnt();
  }
}

#define SETUP_SERIALIZE_CACHED(key_t, key, use_cache) \
  BYPASSING_ALLOCATOR \
  key_t ref = key; \
  auto& cache = caches.use_cache; \
  auto iter = cache.find(ref); \
  if (iter != cache.end()) { \
    return iter->second; \
  } \
  auto idx = caches.serialized.size(); \
  cache[ref] = idx; \
  caches.serialized.push_back(json()); \

#define SETUP_SERIALIZE_UNCACHED(key_t, key, use_cache) \
  BYPASSING_ALLOCATOR \
  auto idx = caches.serialized.size(); \
  caches.serialized.push_back(json()); \

#define __SERIALIZE_SIG(Type) \
  polymorphic_serialize& caches, \
  const Type& self \

struct polymorphic_serialize;

template<class A>
unsigned serialize(__SERIALIZE_SIG(A));

struct polymorphic_serialize {

  map<const void*, unsigned>& indices;
  map<unsigned, unsigned>& functions;
  map<unsigned, unsigned>& predicates;
  vector<json>& serialized;

  template<class B>
  unsigned operator()(const B& ser) { return serialize(*this, ser); }
};

// template<class A>
// unsigned serialize(__SERIALIZE_SIG(A)) {
//   SETUP_SERIALIZE(&self, indices, const void*)
//
//   auto ser = _serialize(self, caches);
//
//   json j;
//   j[get<0>(ser)] = get<1>(ser);
//
//   caches.serialized[idx] = j;
//
//
//   return idx;
// }

struct Function;
struct Predicate;
struct Predicate {
  unsigned functor;
};

struct Function {
  unsigned functor;
  const Term& term;
};

#define __SER_CONST__Predicate 

#define __SER_CONST__Function_(ConstantType, key, ...) \
  { \
    ConstantType c; \
    if (theory->tryInterpretConstant(&fun, c)) { \
      json j; \
      j[key] = __VA_ARGS__; \
      return j; \
    } \
  } \

json trySerializeNumber(const Term& fun) {
  __SER_CONST__Function_(IntegerConstantType, "Int", c.toInner())
  __SER_CONST__Function_(RationalConstantType, "Rat", vector<int>{ c.numerator().toInner(), c.denominator().toInner() })
  __SER_CONST__Function_(RealConstantType, "Real", vector<int>{ c.numerator().toInner(), c.denominator().toInner() })
  return json();
}

const char* serializeInterpretation(Interpretation i) {
#define CASE(pref, suff, expr) \
  case Kernel::Theory::Interpretation::pref ## suff: return expr; \

#define NUM_CASES(SORT) \
    CASE(SORT, _GREATER , "Greater") \
    CASE(SORT, _GREATER_EQUAL , "GreaterEqual") \
    CASE(SORT, _LESS , "Less") \
    CASE(SORT, _LESS_EQUAL , "LessEqual") \
 \
    CASE(SORT, _UNARY_MINUS, "Neg") \
    CASE(SORT, _PLUS, "Add") \
    CASE(SORT, _MINUS, "Sub") \
    CASE(SORT, _MULTIPLY, "Mul") \
    CASE(SORT, _QUOTIENT_E, "QuotientE") \
    CASE(SORT, _QUOTIENT_T, "QuotientT") \
    CASE(SORT, _QUOTIENT_F, "QuotientF") \
    CASE(SORT, _REMAINDER_E, "RemainderE") \
    CASE(SORT, _REMAINDER_T, "RemainderT") \
    CASE(SORT, _REMAINDER_F, "RemainderF") \
    CASE(SORT, _FLOOR, "Floor") \
    CASE(SORT, _CEILING, "Ceiling") \
    CASE(SORT, _TRUNCATE, "Truncate") \
    CASE(SORT, _ROUND, "Round") \


#define _CONVERSIONS(SORT, _CONV_, str) \
  CASE(INT, _CONV_##SORT, str) \
  CASE(RAT, _CONV_##SORT, str) \
  CASE(REAL, _CONV_##SORT, str) \

#define CONVERSIONS(_CONV_, str) \
    _CONVERSIONS(INT , _CONV_, str) \
    _CONVERSIONS(RAT , _CONV_, str) \
    _CONVERSIONS(REAL, _CONV_, str) \

#define FRAC_CASES(SORT) \
  CASE(SORT, _QUOTIENT, "Quot")

  switch (i) {
    case Kernel::Theory::Interpretation::EQUAL: return "Eq";
    case Kernel::Theory::Interpretation::INVALID_INTERPRETATION: return "Invalid";

    /* integers */
    NUM_CASES(INT)
    CASE(INT , _ABS    , "Abs")
    CASE(INT, _DIVIDES, "Divides") 
    CASE(INT, _SUCCESSOR , "Successor") 

    /* rationals */
    NUM_CASES(RAT)
    FRAC_CASES(RAT)

    /* reals */
    NUM_CASES(REAL)
    FRAC_CASES(REAL)

    /* numeric conversion functions */
    CONVERSIONS(_IS_, "IsType")
    CONVERSIONS(_TO_, "ToType")

    /* arrays */
    CASE(ARRAY, _SELECT, "Select")
    CASE(ARRAY_BOOL, _SELECT, "Select")
    CASE(ARRAY, _STORE, "Store")
  }
}

#define IF_FUN_Predicate(...)
#define IF_FUN_Function(...) __VA_ARGS__

#define _SERIALIZE_FUN_PRED(pred, Predicate) \
template<class Ser> tuple<const char*, json> _serialize(const Predicate& self, Ser serial) { \
  json j; \
  j["name"] = env.signature->get ## Predicate(self.functor)->name(); \
  json inter; \
  if (theory->isInterpreted ## Predicate(self.functor)) { \
    inter = serializeInterpretation(theory->interpret ## Predicate(self.functor));\
  } \
  IF_FUN_ ## Predicate (\
    else { \
      inter = trySerializeNumber(self.term); \
    } \
  ) \
  \
  j["inter"] = inter; \
  return {pred, j}; \
} \

_SERIALIZE_FUN_PRED("Pred", Predicate)
_SERIALIZE_FUN_PRED("Fun", Function)

template<class Ser> tuple<const char*, json> _serialize(const Term& self, Ser serial) {
  json j;
  Function fun = {.functor = self.functor(), .term = self};
  j["fun"] = serial(fun);
  vector<unsigned> terms;
  for (int i = 0; i < self.arity(); i++) {
    terms.push_back(serial(self[i]));
  }
  j["terms"] = terms;
  return { "Cterm", j };
}

template<class Ser> tuple<const char*, json> _serialize(const TermList& self, Ser serial) {
  json j; 
  if (self.isTerm()) {
    j["Cterm"] = serial(*self.term());
  } else if (self.isVar()) {
    j["Var"] = self.var();
  } else {
    ASSERTION_VIOLATION
  }
  return { "Term", j };
}

template<class Ser> tuple<const char*, json> _serialize(const Clause& self, Ser serial) {
  json j;
  j["thry_desc"] = self.isPureTheoryDescendant();

  json lits = json::array();
  for (int i = 0; i < self.size(); i++) {
    lits[i] = serial(*self[i]);
  }

  j["lits"] = lits;
  return { "Clause", j };
}


template<class Ser> tuple<const char*, json> _serialize(const Literal& self, Ser serial) {
  json j;
  j["pos"] = self.isPositive();
  Predicate p {.functor = self.functor()};
  j["pred"] = serial(p);
  vector<unsigned> terms;
  for (int i = 0; i < self.arity(); i++) {
    auto x  = serial(self[i]);
    // DBG(self[i].toString()," -> ", x)
    terms.push_back(x);
  }
  j["terms"] = terms;
  return { "Lit", j };
}

#define __SERIALIZE(cached, key_t, key, cache) \
    SETUP_SERIALIZE_ ## cached(key_t, key, cache) \
   \
    auto ser = _serialize(self, caches); \
   \
    json j; \
    j[get<0>(ser)] = get<1>(ser); \
   \
    caches.serialized[idx] = j; \
   \
    return idx; \

#define CACHED_SERIALIZE(Type, key_t, key, cache) \
  template<> \
  unsigned serialize<Type>(__SERIALIZE_SIG(Type)) {\
    __SERIALIZE(CACHED, key_t, key, cache) \
  } \

#define UNCACHED_SERIALIZE(Type, key_t, key, cache) \
  template<> \
  unsigned serialize<Type>(__SERIALIZE_SIG(Type)) {\
    __SERIALIZE(UNCACHED, key_t, key, cache) \
  } \


CACHED_SERIALIZE(Function, unsigned, self.functor, functions)
CACHED_SERIALIZE(Predicate, unsigned, self.functor, predicates)
CACHED_SERIALIZE(Term, const void*, &self, indices)
CACHED_SERIALIZE(Clause, const void*, &self, indices)
CACHED_SERIALIZE(Literal, const void*, &self, indices)
UNCACHED_SERIALIZE(TermList, -, -, -)




void SearchSpaceDumper::dumpFile(const vstring& out) const 
{
  CALL("SearchSpaceDumper::dumpFile")
  DBG("dumping searchspace to file ", env.options->searchSpaceOutput());
  BYPASSING_ALLOCATOR
  std::map<const void*, unsigned> indices;
  std::map<unsigned, unsigned> predicates;
  std::map<unsigned, unsigned> functions;
  std::vector<json> serialized;

  auto caches = polymorphic_serialize {
    .indices = indices,
    .functions = functions,
    .predicates = predicates,
    .serialized = serialized,
  };

  DBG("serializing...");
  for (auto c : _clauses) {
    serialize(caches, *c);
  }
  DBG("writing...");
  cout << out.c_str() << endl;
  ofstream f{ out.c_str() };
  // f << json(serialized) << endl;
  f << json(serialized).dump(3) << endl; 

  DBG("finished.");
  
  // pk.pack(std::string("Log message .packer 1"));
  // pk.pack(std::string("Log message ... 2"));
  // pk.pack(std::string("Log message ... 3"));

}
void SearchSpaceDumper::add(Kernel::Clause* clause) 
{
  clause->incRefCnt();
  _clauses.push(clause); 
}

} // namespace Shell

#endif
