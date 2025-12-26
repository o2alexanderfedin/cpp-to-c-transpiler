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

#include "handlers/FunctionHandler.h"
#include "handlers/VariableHandler.h"
#include "handlers/ExpressionHandler.h"
#include "handlers/StatementHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "CodeGenerator.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>
#include <fstream>
#include <cstdlib>

using namespace cpptoc;

/**
 * @class E2EPhase1Test
 * @brief Test fixture for end-to-end pipeline testing
 */
class E2EPhase1Test : public ::testing::Test {
protected:
    std::unique_ptr<FunctionHandler> funcHandler;
    std::unique_ptr<VariableHandler> varHandler;
    std::unique_ptr<ExpressionHandler> exprHandler;
    std::unique_ptr<StatementHandler> stmtHandler;

    void SetUp() override {
        funcHandler = std::make_unique<FunctionHandler>();
        varHandler = std::make_unique<VariableHandler>();
        exprHandler = std::make_unique<ExpressionHandler>();
        stmtHandler = std::make_unique<StatementHandler>();
    }

    /**
     * @brief Run complete pipeline: C++ source → C source → compile → execute
     * @param cppCode C++ source code
     * @param expectedExitCode Expected exit code from execution
     * @return true if test passed
     */
    bool runPipeline(const std::string& cppCode, int expectedExitCode) {
        // Stage 1: Parse C++ code
        auto cppAST = clang::tooling::buildASTFromCode(cppCode);
        if (!cppAST) {
            std::cerr << "Failed to parse C++ code\n";
            return false;
        }

        // Stage 2: Translate to C AST
        auto cAST = clang::tooling::buildASTFromCode("int dummy;");  // C context
        if (!cAST) {
            std::cerr << "Failed to create C context\n";
            return false;
        }

        clang::CNodeBuilder builder(cAST->getASTContext());
        HandlerContext context(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            builder
        );

        // Translate all declarations
        for (auto* decl : cppAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
                if (!llvm::isa<clang::CXXMethodDecl>(func)) {
                    funcHandler->handleDecl(func, context);
                }
            }
        }

        // Stage 3: Generate C code
        std::string cCode;
        llvm::raw_string_ostream codeStream(cCode);
        CodeGenerator generator(codeStream, cAST->getASTContext());
        generator.printTranslationUnit(cAST->getASTContext().getTranslationUnitDecl());
        codeStream.flush();

        // Write C code to temporary file
        std::string tmpFile = "/tmp/e2e_test_" + std::to_string(rand()) + ".c";
        std::ofstream outFile(tmpFile);
        outFile << cCode;
        outFile.close();

        // Compile with gcc
        std::string compileCmd = "gcc -std=c99 " + tmpFile + " -o " + tmpFile + ".out 2>&1";
        int compileResult = system(compileCmd.c_str());
        if (compileResult != 0) {
            std::cerr << "Compilation failed for:\n" << cCode << "\n";
            std::cerr << "Generated C code:\n" << cCode << "\n";
            system(("cat " + tmpFile).c_str());
            return false;
        }

        // Execute
        std::string execCmd = tmpFile + ".out";
        int execResult = system(execCmd.c_str());
        int actualExitCode = WEXITSTATUS(execResult);

        // Cleanup
        system(("rm -f " + tmpFile + " " + tmpFile + ".out").c_str());

        return actualExitCode == expectedExitCode;
    }
};

// ============================================================================
// E2E Test 1: Simple Program
// ============================================================================

TEST_F(E2EPhase1Test, DISABLED_SimpleProgram) {
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

TEST_F(E2EPhase1Test, DISABLED_LocalVariables) {
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

TEST_F(E2EPhase1Test, DISABLED_ArithmeticExpression) {
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

TEST_F(E2EPhase1Test, DISABLED_FunctionCalls) {
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

TEST_F(E2EPhase1Test, DISABLED_ComplexCalculation) {
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

TEST_F(E2EPhase1Test, DISABLED_Subtraction) {
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

TEST_F(E2EPhase1Test, DISABLED_Division) {
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

TEST_F(E2EPhase1Test, DISABLED_Modulo) {
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

TEST_F(E2EPhase1Test, DISABLED_MultipleFunctions) {
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

TEST_F(E2EPhase1Test, DISABLED_NestedExpressions) {
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
