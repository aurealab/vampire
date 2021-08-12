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
 * @file Z3Interfacing.hpp
 * Defines class Z3Interfacing
 */

#ifndef __Z3Interfacing__
#define __Z3Interfacing__

#if VZ3

/* an (imperfect and under development) version of tracing the Z3 interface
 *  so that vampire can be "factored-out" of runs which cause particular Z3
 *  behaviour. Should be useful for producing MWEs for the Z3 people.
 */
#define PRINT_CPP(X) // cout << X << endl;

#include <fstream>

#include "Lib/DHMap.hpp"
#include "Lib/Option.hpp"
#include "Lib/BiMap.hpp"
#include "Lib/Set.hpp"

#include "SATSolver.hpp"
#include "SATLiteral.hpp"
#include "SATClause.hpp"
#include "SATInference.hpp"
#include "SAT2FO.hpp"
#include "Lib/Option.hpp"
#include "Lib/Coproduct.hpp"

#define __EXCEPTIONS 1
#include "z3++.h"
#include "z3_api.h"

namespace SAT{

  struct UninterpretedForZ3Exception : public ThrowableBase
  {
    UninterpretedForZ3Exception()
    {
      CALL("Z3Interfacing::UninterpretedForZ3Exception::UninterpretedForZ3Exception");
    }
  };

struct Z3MkDatatypesCall;

namespace ProblemExport {

  struct NoExport {
    NoExport() {}
    NoExport(NoExport &&) = default;

    void initialize() {  }
    void terminate() {  }
    void declare_array_sort(z3::sort array, z3::sort index, z3::sort result) {  }
    void declareSort(z3::sort sort) {  }
    void eval(z3::expr const& x) {  }
    void unsatCore() {  }
    void addAssert(z3::expr const& x) {  }
    void check(Stack<z3::expr> const& xs) {  }
    void get_model() {  }
    void reset() {  }
    template<class Value>
    void set_param(const char* k, Value const& v) {  }
    void Z3_mk_datatypes(Z3MkDatatypesCall const& call) {  }
    void declare_fun(vstring const& name, z3::sort_vector domain, z3::sort codomain) {  }
  };

  struct Smtlib {
    std::ofstream out;
    z3::context& _context;

    Smtlib(std::ofstream out, z3::context& context) : out(std::move(out)), _context(context) {}
    Smtlib(Smtlib &&) = default;

    void initialize();
    void terminate();
    void declareSort(z3::sort sort);
    void eval(z3::expr const& x);
    void unsatCore();
    void addAssert(z3::expr const& x);
    void get_model();
    void reset();

    void declare_fun(vstring const& name, z3::sort_vector domain, z3::sort codomain);
    void check(Stack<z3::expr> const& assumptions);
    void declare_array_sort(z3::sort array, z3::sort index, z3::sort result);
    template<class Value>
    void set_param(const char* k, Value const& v);

    void Z3_mk_datatypes(Z3MkDatatypesCall const& call);
  };

  struct ApiCalls {
    std::ofstream out;
    z3::context& _context;
    Map<vstring, Map<vstring, unsigned>> varNames;

    ApiCalls(ApiCalls &&) = default;
    ApiCalls(std::ofstream out, z3::context& context) : out(std::move(out)), _context(context) {}

    vstring escapeVarName(z3::symbol const& sym);


    void initialize();
    void terminate();

    void declare_array_sort(z3::sort array, z3::sort index, z3::sort result);


    struct EscapeString;

    template<class C> struct Serialize { C const& inner; ApiCalls& state; };
    template<class C> Serialize<C> serialize(C const& c){ return Serialize<C>{ c, *this, }; };

    friend std::ostream& operator<<(std::ostream& out, Serialize<vstring> const& self);
    friend std::ostream& operator<<(std::ostream& out, Serialize<bool> const& self);
    friend std::ostream& operator<<(std::ostream& out, Serialize<z3::expr> const& self);
    template<class A>
    friend std::ostream& operator<<(std::ostream& out, Serialize<A> const& self);
    friend std::ostream& operator<<(std::ostream& out, Serialize<z3::symbol> const& self);
    void declareSort(z3::sort sort);
    void eval(z3::expr const& x);
    void unsatCore();
    void addAssert(z3::expr const& x);
    void check(Stack<z3::expr> const& xs);
    void get_model();
    void reset();
    template<class Value>
    void set_param(const char* k, Value const& v);
    void Z3_mk_datatypes(Z3MkDatatypesCall const& call);
    void declare_fun(vstring const& name, z3::sort_vector domain, z3::sort codomain);
  };
} // namespace ProblemExport


class Z3Interfacing : public PrimitiveProofRecordingSATSolver
{
public:
  CLASS_NAME(Z3Interfacing);
  USE_ALLOCATOR(Z3Interfacing);

  Z3Interfacing(const Shell::Options& opts, SAT2FO& s2f, bool unsatCore, vstring const& exportSmtlib);
  Z3Interfacing(SAT2FO& s2f, bool showZ3, bool unsatCore, vstring const& exportSmtlib, Shell::Options::ProblemExportSyntax s = Shell::Options::ProblemExportSyntax::SMTLIB);
  ~Z3Interfacing();

  static char const* z3_full_version();

  void addClause(SATClause* cl) override;

  Status solve();
  virtual Status solve(unsigned conflictCountLimit) override { return solve(); };
  /**
   * If status is @c SATISFIABLE, return assignment of variable @c var
   */
  virtual VarAssignment getAssignment(unsigned var) override;

  /**
   * If status is @c SATISFIABLE, return 0 if the assignment of @c var is
   * implied only by unit propagation (i.e. does not depend on any decisions)
   */
  virtual bool isZeroImplied(unsigned var) override;
  /**
   * Collect zero-implied literals.
   *
   * Can be used in SATISFIABLE and UNKNOWN state.
   *
   * @see isZeroImplied()
   */
  virtual void collectZeroImplied(SATLiteralStack& acc) override;
  /**
   * Return a valid clause that contains the zero-implied literal
   * and possibly the assumptions that implied it. Return 0 if @c var
   * was an assumption itself.
   * If called on a proof producing solver, the clause will have
   * a proper proof history.
   */
  virtual SATClause* getZeroImpliedCertificate(unsigned var) override;

  void ensureVarCount(unsigned newVarCnt) override {
    CALL("Z3Interfacing::ensureVarCnt");

    while (_varCnt < newVarCnt) {
      newVar();
    }
  }


  unsigned newVar() override;

  // Currently not implemented for Z3
  virtual void suggestPolarity(unsigned var, unsigned pol) override {}

  virtual void addAssumption(SATLiteral lit) override;
  virtual void retractAllAssumptions() override;
  virtual bool hasAssumptions() const override { return !_assumptions.isEmpty(); }

  virtual Status solveUnderAssumptions(const SATLiteralStack& assumps, unsigned conflictCountLimit, bool onlyProperSubusets) override;

  SATClause* getRefutation() override;

  template<class F>
  auto scoped(F f)  -> decltype(f())
  {
    _solver.push();
    auto result = f();
    _solver.pop();
    return result;
  }

  using FuncId = unsigned;
  using PredId = unsigned;
  using SortId = TermList;

  struct FuncOrPredId
  {
    explicit FuncOrPredId(unsigned id, bool isPredicate) : id(id), isPredicate(isPredicate) {}
    explicit FuncOrPredId(Term* term) : FuncOrPredId(term->functor(), term->isLiteral()) {}
    static FuncOrPredId function(FuncId id) { return FuncOrPredId ( id, false ); }
    static FuncOrPredId predicate(PredId id) { return FuncOrPredId ( id, true ); }
    unsigned id;
    bool isPredicate;

    friend struct std::hash<FuncOrPredId> ;
    friend bool operator==(FuncOrPredId const& l, FuncOrPredId const& r)
    { return l.id == r.id && l.isPredicate == r.isPredicate; }
    friend std::ostream& operator<<(std::ostream& out, FuncOrPredId const& self)
    { return out << (self.isPredicate ? "pred " : "func " )
      << (self.isPredicate ? env.signature->getPredicate(self.id)->name() : env.signature->getFunction(self.id)->name());
    }
  };

private:

  Map<SortId, z3::sort> _sorts;
  struct Z3Hash {
    static unsigned hash(z3::func_decl const& c) { return c.hash(); }
    static bool equals(z3::func_decl const& l, z3::func_decl const& r) { return z3::eq(l,r); }
  };
  Map<z3::func_decl, FuncOrPredId , Z3Hash > _fromZ3;
  Map<FuncOrPredId,  z3::func_decl, StlHash<FuncOrPredId>> _toZ3;
  Set<SortId> _createdTermAlgebras;

  z3::func_decl const& findConstructor(FuncId id);
  void createTermAlgebra(Shell::TermAlgebra&);

  z3::sort getz3sort(SortId s);

  z3::func_decl z3Function(FuncOrPredId function);

  friend struct ToZ3Expr;
  friend struct EvaluateInModel;
public:
  Term* evaluateInModel(Term* trm);
#ifdef VDEBUG
  z3::model& getModel() { return _model; }
#endif

private:

  struct Representation
  {
    Representation(z3::expr expr, Stack<z3::expr> defs) : expr(expr), defs(defs) {}
    Representation(Representation&&) = default;
    z3::expr expr;
    Stack<z3::expr> defs;
  };


  Representation getRepresentation(Term* trm);
  Representation getRepresentation(SATLiteral lit);
  Representation getRepresentation(SATClause* cl);


  unsigned _varCnt; // just to conform to the interface
  SAT2FO& _sat2fo; // Memory belongs to Splitter

  Shell::Options::ProblemExportSyntax const _outSyntax;
  // Option<std::ofstream> _out;
  Status _status;
  const bool _showZ3;
  const bool _unsatCore;
  Stack<z3::expr> _assumptions;

  z3::context _context;
  z3::solver _solver;
  z3::model _model;

  BiMap<SATLiteral, z3::expr> _assumptionLookup;
  Map<unsigned, z3::expr> _varNames;
  Map<TermList, z3::expr> _termIndexedConstants;
  Map<Signature::Symbol*, z3::expr> _constantNames;
  Coproduct<ProblemExport::NoExport, ProblemExport::Smtlib, ProblemExport::ApiCalls> _exporter;

  bool     isNamedExpr(unsigned var) const;
  z3::expr getNameExpr(unsigned var);

  z3::expr getNamingConstantFor(TermList name, z3::sort sort);
  z3::expr getConst(Signature::Symbol* symb, z3::sort srt);

  template<class Value>
  void             z3_set_param(const char* k, Value const& v);
  z3::check_result z3_check();
  z3::model        z3_get_model();
  void             z3_reset();
  void             z3_add(z3::expr const&);
  z3::expr_vector  z3_unsat_core();
  z3::expr         z3_eval(z3::expr const& x);
  z3::sort         z3_declare_sort(vstring const& name);
  z3::func_decl    z3_declare_fun(vstring const& name, z3::sort_vector domain, z3::sort codomain);
  z3::expr         z3_declare_const(vstring const& name, z3::sort sort);
  void             z3_output_initialize();

  // template<class Clsr>
  // void exportCall(Clsr f);
};

}//end SAT namespace
namespace std {
    template<>
    struct hash<SAT::Z3Interfacing::FuncOrPredId> {
      size_t operator()(SAT::Z3Interfacing::FuncOrPredId const& self)
      { return Lib::HashUtils::combine(self.id, self.isPredicate); }
    };
}

#endif /* if VZ3 */
#endif /*Z3Interfacing*/
