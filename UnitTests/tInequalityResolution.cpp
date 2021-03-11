/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Test/UnitTesting.hpp"
#include "Test/SyntaxSugar.hpp"
#include "Indexing/TermSharing.hpp"
#include "Inferences/InequalityResolution.hpp"
#include "Inferences/InterpretedEvaluation.hpp"
#include "Kernel/Ordering.hpp"
#include "Inferences/PolynomialEvaluation.hpp"
#include "Inferences/Cancellation.hpp"

#include "Test/SyntaxSugar.hpp"
#include "Test/TestUtils.hpp"
#include "Lib/Coproduct.hpp"
#include "Test/SimplificationTester.hpp"
#include "Test/GenerationTester.hpp"
#include "Kernel/KBO.hpp"
#include "Indexing/TermSubstitutionTree.hpp"
#include "Inferences/PolynomialEvaluation.hpp"

using namespace std;
using namespace Kernel;
using namespace Inferences;
using namespace Test;
using namespace Indexing;

////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
////// TEST CASES 
/////////////////////////////////////

#define SUGAR(Num)                                                                                            \
  NUMBER_SUGAR(Num)                                                                                           \
  DECL_DEFAULT_VARS                                                                                           \
  DECL_FUNC(f, {Num}, Num)                                                                                    \
  DECL_FUNC(g, {Num, Num}, Num)                                                                               \
  DECL_CONST(a, Num)                                                                                          \
  DECL_CONST(b, Num)                                                                                          \
  DECL_CONST(c, Num)                                                                                          \
  DECL_PRED(r, {Num,Num})                                                                                     \

#define MY_SYNTAX_SUGAR SUGAR(Rat)


Stack<Indexing::Index*> indices() 
{ 
  auto& kbo = *new KBO(KBO::testKBO());
  // auto uwa = env.options->unificationWithAbstraction();
  auto uwa = Options::UnificationWithAbstraction::ONE_INTERP;
  return {
    new InequalityResolutionIndex(
        new TermSubstitutionTree(uwa, true), kbo,
        InequalityNormalizer(PolynomialEvaluation(kbo)))
  };
}

REGISTER_GEN_TESTER(Test::Generation::GenerationTester<InequalityResolution>)

/////////////////////////////////////////////////////////
// Basic tests
//////////////////////////////////////

TEST_GENERATION(basic01,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({selected( f(x) > 0 ), x == 7   }) )
      .context ({ clause({         -f(x) > 0             }) })
      .expected(exactly(
            clause({ num(0) > 0,  x == 7  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic02,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({selected(  f(a) > 0)  }) )
      .context ({ clause({      a + -f(a) > 0 }) })
      .expected(exactly(
            clause({  a > 0  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic03,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({selected( -g(x,a) + -g(g(a,b), f(x)) > 0) }) )
      .context ({ clause({           g(b,a) +  g(g(a,b), f(a)) > 0  }) })
      .expected(exactly(
            clause({  g(b,a) + (-g(a,a))  > 0  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic04,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({ selected( a + -f(x) > 0), x == 7 }) )
      .context ({ clause({           a +  f(a) > 0 }) })
      .expected(exactly(
            clause({  2 * a > 0, a == 7  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic05,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({ selected( a + -f(y) > 0) }) )
      .context ({ clause({           a +  f(a) > 0 , x == 7}) })
      .expected(exactly(
            clause({  2 * a > 0, x == 7  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic06,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({ selected(-f(x) > 0) }) )
      .context ({ clause({    f(y) + f(a) > 0  }) })
      .expected(exactly(
            clause({  f(a) > 0 }),
            clause({  f(x) > 0 })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic07,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({ selected(a > 0) }) )
      .context ({ clause({          a > 0  }) })
      .expected(exactly(
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(basic08,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({ selected(a >= a) }) )
      .context ({ clause({          a > 0  }) })
      .expected(exactly(
      ))
      .premiseRedundant(false)
    )

/////////////////////////////////////////////////////////
// Testing gcd for int
//////////////////////////////////////

TEST_GENERATION_WITH_SUGAR(gcd01_Int,
    SUGAR(Int),
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({ selected(-6 * f(x) + b > 0) })  )
      .context ({ clause({           4 * f(y) + a > 0  }) })
      .expected(exactly(
            clause({  2 * b  + 3 * a + -1 > 0 })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION_WITH_SUGAR(gcd01_Rat,
    SUGAR(Rat),
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({ selected( 6 * f(x) + b > 0) })  )
      .context ({ clause({          -4 * f(y) + a > 0  }) })
      .expected(exactly(
            clause({  b  + frac(3,2) * a  > 0 })
      ))
      .premiseRedundant(false)
    )

/////////////////////////////////////////////////////////
// Testing substitution application
//////////////////////////////////////

TEST_GENERATION(substitution01,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({ selected(-f(f(x)) + f(x) > 0) })  )
      .context ({ clause({           f(f(a))        > 0  }) })
      .expected(exactly(
            clause({  f(a) > 0 })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION(substitution02,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({ selected(-g(f(x), f(f(b))) +    f(x)  > 0) })  )
      .context ({ clause({           g(f(a), f(f(y))) +    f(y)  > 0  }) })
      .expected(exactly(
            clause({  f(a) + f(b) > 0 })
      ))
      .premiseRedundant(false)
    )

/////////////////////////////////////////////////////////
// Testing abstraction
//////////////////////////////////////

TEST_GENERATION(abstraction1,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({ selected(-f(     0        ) > 0) })  )
      .context ({ clause({           f(f(a) + g(b, c)) > 0  }) })
      .expected(exactly(
            clause({ num(0) > 0, f(a) + g(b, c) != 0 })
      ))
      .premiseRedundant(false)
    )



/////////////////////////////////////////////////////////
// Testing normalization
//////////////////////////////////////

TEST_GENERATION(normalization01,
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({selected(0 > f(a))  }) )
      .context ({ clause({     a + f(a) > 0 }) })
      .expected(exactly(
            clause({  a > 0  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION_WITH_SUGAR(normalization02_Int,
    SUGAR(Int),
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({selected(~(0 > -f(a)))  }) )
      //                           ~(0 > -f(a)))
      //                     ==> -f(a) >= 0         ==> 0 >=  f(a)
      //                     ==> -f(a) + 1 > 0      
      .context ({ clause({     a + f(a) > 0 }) })// ==> a + f(a) >  f(a)
                                                 // ==> a        > 0
      .expected(exactly(
            clause({  a > 0  })
      ))
      .premiseRedundant(false)
    )

TEST_GENERATION_WITH_SUGAR(normalization02_Rat,
    SUGAR(Rat),
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({selected(~(0 > -f(a)))  }) )
      .context ({ clause({     a + f(a) > 0 }) })
      .expected(exactly(
            clause({  a > 0  })
      ))
      .premiseRedundant(false)
    )

// only for integers (which we r using here)
TEST_GENERATION_WITH_SUGAR(normalization03,
    SUGAR(Int),
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({selected( f(a) >= 0)  }) )
      .context ({ clause({     a + -f(a) >  0 }) })
      .expected(exactly(
            clause({  a   > 0  })
      ))
      .premiseRedundant(false)
    )

// only for integers (which we r using here)
TEST_GENERATION_WITH_SUGAR(bug01,
    SUGAR(Real),
    Generation::TestCase()
      .indices(indices())
      .input   (  clause({r(x, y), selected( (x + -y > 0) ) }) )
      .context ({ clause({     a >  0 }) })
      //                                      (y - 1 > 0) 
      .expected(exactly(
            clause({     x > 0, r(x, a) })
      ))
      .premiseRedundant(false)
    )
