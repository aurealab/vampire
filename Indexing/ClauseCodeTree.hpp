/**
 * @file ClauseCodeTree.hpp
 * Defines class ClauseCodeTree.
 */

#ifndef __ClauseCodeTree__
#define __ClauseCodeTree__

#include "../Forwards.hpp"

#include "../Lib/Allocator.hpp"
#include "../Lib/DArray.hpp"
#include "../Lib/DHMap.hpp"
#include "../Lib/Hash.hpp"
#include "../Lib/List.hpp"
#include "../Lib/Recycler.hpp"
#include "../Lib/Stack.hpp"
#include "../Lib/TriangularArray.hpp"
#include "../Lib/Vector.hpp"
#include "../Lib/VirtualIterator.hpp"

#include "Index.hpp"


namespace Indexing {

using namespace Lib;
using namespace Kernel;

class ClauseCodeTree : public ClauseSubsumptionIndex 
{
public:

  struct ILStruct;
  struct SearchStruct;

  struct LitInfo
  {
    LitInfo() {}
    LitInfo(Clause* cl, unsigned litIndex);
    void dispose();

    static LitInfo getReversed(const LitInfo& li);
    static LitInfo getOpposite(const LitInfo& li);

    /** Index of this LitInfo in the ClauseMatcher object */
    unsigned liIndex;
    /** Index of the literal in the query clause */
    unsigned litIndex;
    FlatTerm* ft;
    bool opposite;
  };

  struct MatchInfo
  {
    MatchInfo(ILStruct* ils, unsigned liIndex, DArray<TermList>& bindingArray);
    ~MatchInfo();

    CLASS_NAME("ClauseCodeTree::MatchInfo");
    USE_ALLOCATOR(MatchInfo);

    /** Index of the matched LitInfo in the EContext */
    unsigned liIndex;
    /** this is redundant and is present here just so that the object
     * can be conveniently destroyed */
    unsigned bindCnt;
    /** array of bindings */
    TermList* bindings;
  };
  
  typedef Stack<MatchInfo*> MatchStack;

  /**
   * Structure with information about an indexed literal
   */
  struct ILStruct
  {
    ILStruct(unsigned varCnt, Stack<unsigned>& gvnStack);
    ~ILStruct();
    void putIntoSequence(ILStruct* previous_);

    bool equalsForOpMatching(const ILStruct& o) const;
    
    void disposeMatches();

    CLASS_NAME("ClauseCodeTree::ILStruct");
    USE_ALLOCATOR(ILStruct);

    struct GVArrComparator;
    
    unsigned depth;
    ILStruct* previous;
    unsigned varCnt;
    unsigned* globalVarNumbers;

    unsigned* sortedGlobalVarNumbers;
    
    /** Permutation that should be applied to bindings so that they will
     *  correspond to the sortedGlobalVarNumbers */
    unsigned* globalVarPermutation;
    
    unsigned timestamp;
    //from here on, the values are valid only if the timestamp is current
    MatchStack matches;
    /** all possible lits were tried to match */
    bool visited;
    bool finished;
  };

  enum Instruction
  {
    //it means fail if data==0
    SUCCESS_OR_FAIL = 0,
    SUCCESS2 = 4, //this one is here because pointers are guaranted to be only 4-byte aligned
    LIT_END = 1,
    LIT_END2 = 5, //this one also
    CHECK_FUN = 2,
    ASSIGN_VAR = 3,
    CHECK_VAR = 6,
    SEARCH_STRUCT = 7
  };

  /** Structure containing a single instruction and its arguments */
  struct OpCode
  {
    static OpCode getSuccess(Clause* cl);
    static OpCode getLitEnd(ILStruct* ils);
    static OpCode getTermOp(Instruction i, unsigned num);

    void makeFail() { data=0; }
    
    bool equalsForOpMatching(const OpCode& o) const;

    /**
     * Return true iff OpCode contains a success instruction
     *
     * A succes instruction is either SUCCESS or SUCCESS2, because
     * on some architectures, pointers are only 4-byte aligned and
     * the instruction is stored in first three bits.
     */
    inline bool isSuccess() const { return (instr()&3)==SUCCESS_OR_FAIL && data; }
    inline bool isFail() const { return !data; }
    inline bool isLitEnd() const { return (instr()&3)==LIT_END; }
    inline bool isSearchStruct() const { return instr()==SEARCH_STRUCT; }
    inline bool isCheckFun() const { return instr()==CHECK_FUN; }

    inline Clause* getSuccessResult() { ASS(isSuccess()); return result; }
    
    inline ILStruct* getILS()
    {
      ASS(isLitEnd());
      return reinterpret_cast<ILStruct*>(data&~static_cast<size_t>(LIT_END));
    }
    inline const ILStruct* getILS() const
    {
      return const_cast<OpCode*>(this)->getILS();
    }
    
    SearchStruct* getSearchStruct();

    inline Instruction instr() const { return info.instr; }
    inline void setInstr(Instruction i) { info.instr=i; }

    inline unsigned arg() const { return info.arg; }

#if VDEBUG
    string toString() const;
#endif

    union {
      struct {
        Instruction instr : 3;
        unsigned arg : 29;
      } info;
      Clause* result;
      size_t data;
    };
    /**
     * Pointer to an alternative operation
     *
     * If nonzero, always points to the first operation of
     * a @b CodeBlock.
     */
    OpCode* alternative;
  };
  
  struct SearchStruct
  {
    SearchStruct(size_t length);
    ~SearchStruct();
    OpCode*& targetOp(unsigned fn);

    CLASS_NAME("ClauseCodeTree::SearchStruct");
    USE_ALLOCATOR(SearchStruct);
    
    struct OpComparator;

    OpCode landingOp;
    size_t length;
    unsigned* values;
    OpCode** targets;
  };


  typedef Vector<OpCode> CodeBlock;
  typedef Stack<OpCode> CodeStack;

  //////// auxiliary methods //////////

  inline bool isEmpty() { return !_entryPoint; }
  inline OpCode* getEntryPoint() { ASS(!isEmpty()); return &(*_entryPoint)[0]; }
  static CodeBlock* firstOpToCodeBlock(OpCode* op);

  template<class Visitor>
  void visitAllOps(Visitor visitor);

  //////////// insertion //////////////

  typedef DHMap<unsigned,unsigned> VarMap;

  /** Context for code compilation */
  struct CompileContext
  {
    void init();
    void deinit(ClauseCodeTree* tree, bool discarded=false);

    void nextLit();

    unsigned nextVarNum;
    unsigned nextGlobalVarNum;
    VarMap varMap;
    VarMap globalVarMap;
  };

  void optimizeLiteralOrder(DArray<Literal*>& lits);
  void evalSharing(Literal* lit, OpCode* startOp, size_t& sharedLen, size_t& unsharedLen);
  static void matchCode(CodeStack& code, OpCode* startOp, size_t& matchedCnt);
  static CodeBlock* buildBlock(CodeStack& code, size_t cnt, ILStruct* prev);
  void incorporate(CodeStack& code);
  
  void compressCheckFnOps(OpCode* chainStart);

  static void compileLiteral(Literal* lit, CodeStack& code, CompileContext& cctx, bool addLitEnd);

  //////// retrieval //////////

  /**
   * Backtracking point for the interpretation of the code tree.
   */
  struct BTPoint
  {
    BTPoint() {}
    BTPoint(size_t tp, OpCode* op) : tp(tp), op(op) {}

    /** Position in the flat term */
    size_t tp;
    /** Pointer to the next operation */
    OpCode* op;
  };

  typedef Stack<BTPoint> BTStack;

  /** Context for finding matches of literals
   *
   * Here the actual execution of the code of the tree takes place */
  struct LiteralMatcher
  {
    void init(ClauseCodeTree* tree, OpCode* entry_, LitInfo* linfos_, size_t linfoCnt_);
    bool next();
    bool doEagerMatching();
    
    inline bool finished() const { return !_fresh && !_matched; }
    inline bool eagerlyMatched() const { return _eagerlyMatched; }
    inline bool matched() const { return _matched && op->isLitEnd(); }
    inline bool success() const { return _matched && op->isSuccess(); }

    inline ILStruct* getILS() { ASS(matched()); return op->getILS(); }

    CLASS_NAME("ClauseCodeTree::LiteralMatcher");
    USE_ALLOCATOR(LiteralMatcher);

    /** Pointer to the current operation */
    OpCode* op;
  private:
    /** Position in the flat term */
    size_t tp;
    /** Flat term to be traversed */
    FlatTerm* ft;
    /** Stack containing backtracking points */
    BTStack btStack;
    /** Variable bindings */
    DArray<TermList> bindings;

    bool _fresh;
    bool _matched;
    bool _eagerlyMatched;

    ClauseCodeTree* tree;
    OpCode* entry;
    LitInfo* linfos;
    size_t linfoCnt;
    size_t curLInfo;
    
    Stack<OpCode*> eagerResults;
  private:
    bool execute();

    bool backtrack();
    bool prepareLiteral();

    bool doSearchStruct();
    bool doCheckFun();
    void doAssignVar();
    bool doCheckVar();
    
    void recordMatch();
  };

  struct ClauseMatcher
  {
    void init(ClauseCodeTree* tree_, Clause* query_, bool sres_);
    void deinit();

    Clause* next(int& resolvedQueryLit);
    
    bool matched() { return lms.isNonEmpty() && lms.top()->success(); }
    OpCode* getSuccessOp() { ASS(matched()); return lms.top()->op; }

    CLASS_NAME("ClauseCodeTree::ClauseMatcher");
    USE_ALLOCATOR(ClauseMatcher);
    
  private:
    void enterLiteral(OpCode* entry);
    void leaveLiteral();
    bool litEndAlreadyVisited(OpCode* op);
    
    bool checkCandidate(Clause* cl, int& resolvedQueryLit);
    bool matchGlobalVars(int& resolvedQueryLit);
    bool compatible(ILStruct* bi, MatchInfo* bq, ILStruct* ni, MatchInfo* nq);

    Clause* query;
    ClauseCodeTree* tree;
    bool sres;

    DArray<LitInfo> lInfos;
    
    Stack<LiteralMatcher*> lms;
  };


  void incTimeStamp();

  //////// member variables //////////
  
#if VDEBUG
  unsigned _clauseMatcherCounter;
#endif

  unsigned _curTimeStamp;
  unsigned _maxVarCnt;

  CodeBlock* _entryPoint;
  
  struct ClauseSResIterator
  : public IteratorCore<ClauseSResQueryResult>
  {
    ClauseSResIterator(ClauseCodeTree* tree, Clause* query, bool sres)
    : ready(false)
    {
      Recycler::get(cm);
      cm->init(tree, query, sres);
    }
    ~ClauseSResIterator()
    {
      cm->deinit();
      Recycler::release(cm);
    }
    
    bool hasNext()
    {
      CALL("ClauseCodeTree::ClauseSResIterator::hasNext");
      if(ready) {
	return result;
      }
      ready=true;
      result=cm->next(resolvedQueryLit);
      ASS(!result || resolvedQueryLit<1000000);
      return result;
    }
    
    ClauseSResQueryResult next()
    {
      CALL("ClauseCodeTree::ClauseSResIterator::next");
      ASS(result);
      
      ready=false;
      if(resolvedQueryLit==-1) {
	return ClauseSResQueryResult(result);
      }
      else {
	return ClauseSResQueryResult(result, resolvedQueryLit);
      }
    }
  private:
    bool ready;
    Clause* result;
    int resolvedQueryLit;
    ClauseMatcher* cm;
  };
public:
  ClauseCodeTree();
  
  void insert(Clause* cl);
  void remove(Clause* cl);
  
  //overriding Index::handleClause
  void handleClause(Clause* cl, bool adding);
  
  ClauseSResResultIterator getSubsumingOrSResolvingClauses(Clause* c, bool subsumptionResolution);
};

}

#endif // __ClauseCodeTree__

