/**
 * @file E2EPhase1Test.cpp
 * @brief End-to-end tests for complete 3-stage transpiler pipeline
 *
 * Tests the full pipeline:
 * Stage 1: Clang parses C++ → C++ AST
 * Stage 2: Handlers translate C++ AST → C AST
 * Stage 3: CodeGenerator emits C source
 * Validation: Compile C code with gcc and execute
 */

#include "tests/fixtures/DispatcherTestHelper.h"
#include "dispatch/TypeHandler.h"
#include "dispatch/ParameterHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/BinaryOperatorHandler.h"
#include "dispatch/UnaryOperatorHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/ParenExprHandler.h"
#include "dispatch/CallExprHandler.h"
#include "dispatch/CompoundStmtHandler.h"
#include "dispatch/DeclStmtHandler.h"
#include "dispatch/ReturnStmtHandler.h"
#include "dispatch/FunctionHandler.h"
#include "dispatch/VariableHandler.h"
#include "dispatch/TranslationUnitHandler.h"
#include <gtest/gtest.h>

using namespace cpptoc;

/**
 * @class E2EPhase1Test
 * @brief Test fixture for end-to-end pipeline testing
 */
class E2EPhase1Test : public ::testing::Test {
protected:
    /**
     * @brief Run complete pipeline: C++ source → C source → compile → execute
     * @param cppCode C++ source code
     * @param expectedExitCode Expected exit code from execution
     * @return true if test passed
     */
    bool runPipeline(const std::string& cppCode, int expectedExitCode) {
        // Create dispatcher pipeline
        auto pipeline = cpptoc::test::createDispatcherPipeline(cppCode);

        // Register handlers needed for Phase 1 (basic functions and variables)
        // Base handlers first
        TypeHandler::registerWith(*pipeline.dispatcher);
        ParameterHandler::registerWith(*pipeline.dispatcher);

        // Expression handlers
        LiteralHandler::registerWith(*pipeline.dispatcher);
        DeclRefExprHandler::registerWith(*pipeline.dispatcher);
        BinaryOperatorHandler::registerWith(*pipeline.dispatcher);
        UnaryOperatorHandler::registerWith(*pipeline.dispatcher);
        ImplicitCastExprHandler::registerWith(*pipeline.dispatcher);
        ParenExprHandler::registerWith(*pipeline.dispatcher);
        CallExprHandler::registerWith(*pipeline.dispatcher);

        // Statement handlers
        CompoundStmtHandler::registerWith(*pipeline.dispatcher);
        DeclStmtHandler::registerWith(*pipeline.dispatcher);
        ReturnStmtHandler::registerWith(*pipeline.dispatcher);

        // Declaration handlers
        FunctionHandler::registerWith(*pipeline.dispatcher);
        VariableHandler::registerWith(*pipeline.dispatcher);
        TranslationUnitHandler::registerWith(*pipeline.dispatcher);

        // Dispatch the TranslationUnit (dispatches all top-level declarations recursively)
        auto* TU = pipeline.cppAST->getASTContext().getTranslationUnitDecl();
        pipeline.dispatcher->dispatch(
            pipeline.cppAST->getASTContext(),
            pipeline.cAST->getASTContext(),
            TU
        );

        // Generate C code from C AST using PathMapper
        std::string cCode = cpptoc::test::generateCCode(
            pipeline.cAST->getASTContext(),
            *pipeline.pathMapper
        );

        // Compile and run
        int actualExitCode = cpptoc::test::compileAndRun(cCode, "e2e_phase1");

        if (actualExitCode == -1) {
            std::cerr << "Compilation failed!\n";
            std::cerr << "Generated C code:\n" << cCode << "\n";
            return false;
        }

        return actualExitCode == expectedExitCode;
    }
};

// ============================================================================
// E2E Test 1: Simple Program
// ============================================================================

TEST_F(E2EPhase1Test, SimpleProgram) {
    std::string cppCode = R"(
        int add(int a, int b) {
            return a + b;
        }
        int main() {
            return add(3, 4);
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 7)) << "Expected exit code 7 (3+4)";
}

// ============================================================================
// E2E Test 2: Local Variables
// ============================================================================

TEST_F(E2EPhase1Test, LocalVariables) {
    std::string cppCode = R"(
        int main() {
            int x = 5;
            int y = 3;
            return x + y;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 8)) << "Expected exit code 8 (5+3)";
}

// ============================================================================
// E2E Test 3: Arithmetic Expression
// ============================================================================

TEST_F(E2EPhase1Test, ArithmeticExpression) {
    std::string cppCode = R"(
        int main() {
            return 2 + 3 * 4;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 14)) << "Expected exit code 14 (2+3*4)";
}

// ============================================================================
// E2E Test 4: Function Calls
// ============================================================================

TEST_F(E2EPhase1Test, FunctionCalls) {
    std::string cppCode = R"(
        int double_it(int n) {
            return n * 2;
        }
        int main() {
            return double_it(5);
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 10)) << "Expected exit code 10 (5*2)";
}

// ============================================================================
// E2E Test 5: Complex Calculation
// ============================================================================

TEST_F(E2EPhase1Test, ComplexCalculation) {
    std::string cppCode = R"(
        int calculate() {
            int a = 10;
            int b = 20;
            int c = a + b;
            return c * 2;
        }
        int main() {
            return calculate();
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 60)) << "Expected exit code 60 ((10+20)*2)";
}

// ============================================================================
// E2E Test 6: Subtraction
// ============================================================================

TEST_F(E2EPhase1Test, Subtraction) {
    std::string cppCode = R"(
        int main() {
            return 10 - 3;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 7)) << "Expected exit code 7 (10-3)";
}

// ============================================================================
// E2E Test 7: Division
// ============================================================================

TEST_F(E2EPhase1Test, Division) {
    std::string cppCode = R"(
        int main() {
            return 20 / 4;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 5)) << "Expected exit code 5 (20/4)";
}

// ============================================================================
// E2E Test 8: Modulo
// ============================================================================

TEST_F(E2EPhase1Test, Modulo) {
    std::string cppCode = R"(
        int main() {
            return 10 % 3;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 1)) << "Expected exit code 1 (10%3)";
}

// ============================================================================
// E2E Test 9: Multiple Functions
// ============================================================================

TEST_F(E2EPhase1Test, MultipleFunctions) {
    std::string cppCode = R"(
        int add(int a, int b) {
            return a + b;
        }
        int multiply(int a, int b) {
            return a * b;
        }
        int main() {
            int sum = add(3, 4);
            int product = multiply(2, 5);
            return sum + product;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 17)) << "Expected exit code 17 (7+10)";
}

// ============================================================================
// E2E Test 10: Nested Expressions
// ============================================================================

TEST_F(E2EPhase1Test, NestedExpressions) {
    std::string cppCode = R"(
        int main() {
            return (2 + 3) * (4 + 1);
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 25)) << "Expected exit code 25 (5*5)";
}

// ============================================================================
// Basic Sanity Test (enabled)
// ============================================================================

TEST_F(E2EPhase1Test, BasicSanity) {
    // Just verify test infrastructure works
    EXPECT_TRUE(true);
}
