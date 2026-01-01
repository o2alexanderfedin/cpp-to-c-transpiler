/**
 * @file ControlFlowIntegrationTest.cpp
 * @brief Integration tests for control flow with Phase 1 features
 *
 * Tests control flow handlers working together with Phase 1 handlers
 * (functions, variables, expressions) to validate handler cooperation.
 */

#include "dispatch/FunctionHandler.h"
#include "dispatch/VariableHandler.h"
#include "dispatch/StatementHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ControlFlowIntegrationTest
 * @brief Test fixture for control flow integration testing
 */
class ControlFlowIntegrationTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    std::unique_ptr<FunctionHandler> funcHandler;
    std::unique_ptr<VariableHandler> varHandler;
    std::unique_ptr<ExpressionHandler> exprHandler;
    std::unique_ptr<StatementHandler> stmtHandler;

    void SetUp() override {
        // Create real AST contexts
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr);
        ASSERT_NE(cAST, nullptr);

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Create all handlers
        funcHandler = std::make_unique<FunctionHandler>();
        varHandler = std::make_unique<VariableHandler>();
        exprHandler = std::make_unique<ExpressionHandler>();
        stmtHandler = std::make_unique<StatementHandler>();
    }

    void TearDown() override {
        stmtHandler.reset();
        exprHandler.reset();
        varHandler.reset();
        funcHandler.reset();
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Helper to translate a function by name
     */
    clang::FunctionDecl* translateFunction(const std::string& code, const std::string& funcName) {
        auto testAST = clang::tooling::buildASTFromCode(code);
        if (!testAST) return nullptr;

        clang::FunctionDecl* cppFunc = nullptr;
        for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* func = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
                if (func->getNameAsString() == funcName) {
                    cppFunc = func;
                    break;
                }
            }
        }

        if (!cppFunc) return nullptr;

        return llvm::dyn_cast<clang::FunctionDecl>(
            funcHandler->handleDecl(cppFunc, *context)
        );
    }
};

// ============================================================================
// If/Else Integration Tests (5 tests)
// ============================================================================

TEST_F(ControlFlowIntegrationTest, FunctionWithIfElse) {
    // Test: Complete function with if-else
    std::string code = R"(
        int max(int a, int b) {
            if (a > b) {
                return a;
            } else {
                return b;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "max");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "max");
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

TEST_F(ControlFlowIntegrationTest, IfWithVariables) {
    // Test: If statement with local variables
    std::string code = R"(
        int compute(int x) {
            int result = 0;
            if (x > 0) {
                result = x * 2;
            }
            return result;
        }
    )";

    auto* cFunc = translateFunction(code, "compute");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "compute");
}

TEST_F(ControlFlowIntegrationTest, IfWithArithmetic) {
    // Test: If condition with complex arithmetic
    std::string code = R"(
        int check(int a, int b) {
            if ((a + b) * 2 > 10) {
                return 1;
            }
            return 0;
        }
    )";

    auto* cFunc = translateFunction(code, "check");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, NestedIfInFunction) {
    // Test: Nested if-else in function body
    std::string code = R"(
        int classify(int x) {
            if (x > 0) {
                if (x > 100) {
                    return 2;
                } else {
                    return 1;
                }
            } else {
                return 0;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "classify");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, MultipleIfStatements) {
    // Test: Multiple if statements in sequence
    std::string code = R"(
        int process(int x) {
            int result = x;
            if (x < 0) {
                result = -x;
            }
            if (result > 100) {
                result = 100;
            }
            return result;
        }
    )";

    auto* cFunc = translateFunction(code, "process");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Loop Integration Tests (5 tests)
// ============================================================================

TEST_F(ControlFlowIntegrationTest, ForLoopInFunction) {
    // Test: Complete function with for loop
    std::string code = R"(
        int sum(int n) {
            int total = 0;
            for (int i = 0; i < n; i++) {
                total += i;
            }
            return total;
        }
    )";

    auto* cFunc = translateFunction(code, "sum");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, WhileLoopWithVariables) {
    // Test: While loop declaring variables
    std::string code = R"(
        int countdown(int n) {
            int count = n;
            while (count > 0) {
                count--;
            }
            return count;
        }
    )";

    auto* cFunc = translateFunction(code, "countdown");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, NestedLoopsInFunction) {
    // Test: Nested for/while loops
    std::string code = R"(
        int nested(int n) {
            int result = 0;
            for (int i = 0; i < n; i++) {
                int j = 0;
                while (j < i) {
                    result++;
                    j++;
                }
            }
            return result;
        }
    )";

    auto* cFunc = translateFunction(code, "nested");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, LoopWithBreakContinue) {
    // Test: Loop with break and continue
    std::string code = R"(
        int find_first(int n) {
            for (int i = 0; i < n; i++) {
                if (i % 2 == 0) {
                    continue;
                }
                if (i > 10) {
                    break;
                }
            }
            return 0;
        }
    )";

    auto* cFunc = translateFunction(code, "find_first");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, DoWhileInFunction) {
    // Test: Function with do-while loop
    std::string code = R"(
        int process(int n) {
            int i = 0;
            do {
                i++;
            } while (i < n);
            return i;
        }
    )";

    auto* cFunc = translateFunction(code, "process");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Switch Integration Tests (3 tests)
// ============================================================================

TEST_F(ControlFlowIntegrationTest, SwitchInFunction) {
    // Test: Complete function with switch
    std::string code = R"(
        int get_value(int x) {
            switch (x) {
                case 1:
                    return 10;
                case 2:
                    return 20;
                default:
                    return 0;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "get_value");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, SwitchWithVariables) {
    // Test: Switch with variable declarations
    std::string code = R"(
        int compute(int x) {
            int result = 0;
            switch (x) {
                case 1:
                    result = 100;
                    break;
                case 2:
                    result = 200;
                    break;
                default:
                    result = -1;
                    break;
            }
            return result;
        }
    )";

    auto* cFunc = translateFunction(code, "compute");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, SwitchInLoop) {
    // Test: Switch inside loop
    std::string code = R"(
        int process(int n) {
            int total = 0;
            for (int i = 0; i < n; i++) {
                switch (i % 3) {
                    case 0:
                        total += 1;
                        break;
                    case 1:
                        total += 2;
                        break;
                    case 2:
                        total += 3;
                        break;
                }
            }
            return total;
        }
    )";

    auto* cFunc = translateFunction(code, "process");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Mixed Control Flow Tests (7 tests)
// ============================================================================

TEST_F(ControlFlowIntegrationTest, IfInForLoop) {
    // Test: If inside for loop
    std::string code = R"(
        int count_positive(int n) {
            int count = 0;
            for (int i = -n; i <= n; i++) {
                if (i > 0) {
                    count++;
                }
            }
            return count;
        }
    )";

    auto* cFunc = translateFunction(code, "count_positive");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, ForInWhileLoop) {
    // Test: For inside while
    std::string code = R"(
        int complex_loop(int n) {
            int outer = 0;
            int result = 0;
            while (outer < n) {
                for (int inner = 0; inner < outer; inner++) {
                    result++;
                }
                outer++;
            }
            return result;
        }
    )";

    auto* cFunc = translateFunction(code, "complex_loop");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, WhileInIfElse) {
    // Test: While inside if-else
    std::string code = R"(
        int conditional_loop(int x, int n) {
            int result = 0;
            if (x > 0) {
                int i = 0;
                while (i < n) {
                    result += x;
                    i++;
                }
            } else {
                int i = 0;
                while (i < n) {
                    result -= x;
                    i++;
                }
            }
            return result;
        }
    )";

    auto* cFunc = translateFunction(code, "conditional_loop");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, SwitchInForLoop) {
    // Test: Switch inside for loop
    std::string code = R"(
        int categorize(int arr[], int size) {
            int count = 0;
            for (int i = 0; i < size; i++) {
                switch (arr[i] % 2) {
                    case 0:
                        count++;
                        break;
                    case 1:
                        count--;
                        break;
                }
            }
            return count;
        }
    )";

    auto* cFunc = translateFunction(code, "categorize");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, ComplexControlFlow) {
    // Test: Mix of if, while, for, switch
    std::string code = R"(
        int complex(int n) {
            int result = 0;
            if (n > 0) {
                for (int i = 0; i < n; i++) {
                    int j = 0;
                    while (j < i) {
                        switch (j % 2) {
                            case 0:
                                result += j;
                                break;
                            case 1:
                                result -= j;
                                break;
                        }
                        j++;
                    }
                }
            }
            return result;
        }
    )";

    auto* cFunc = translateFunction(code, "complex");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, DeepNesting) {
    // Test: Deeply nested control flow
    std::string code = R"(
        int deep_nesting(int a, int b) {
            if (a > 0) {
                if (b > 0) {
                    for (int i = 0; i < a; i++) {
                        for (int j = 0; j < b; j++) {
                            if (i == j) {
                                return i + j;
                            }
                        }
                    }
                }
            }
            return 0;
        }
    )";

    auto* cFunc = translateFunction(code, "deep_nesting");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(ControlFlowIntegrationTest, AllConstructsTogether) {
    // Test: Every control flow construct in one function
    std::string code = R"(
        int all_constructs(int n) {
            int result = 0;

            // If-else
            if (n < 0) {
                n = -n;
            } else if (n == 0) {
                return 0;
            }

            // For loop
            for (int i = 0; i < n; i++) {
                result += i;
            }

            // While loop
            int count = 0;
            while (count < n) {
                count++;
            }

            // Do-while loop
            int j = 0;
            do {
                j++;
            } while (j < n);

            // Switch
            switch (n % 3) {
                case 0:
                    result *= 2;
                    break;
                case 1:
                    result *= 3;
                    break;
                case 2:
                    result *= 4;
                    break;
            }

            // Break and continue in loop
            for (int k = 0; k < n; k++) {
                if (k % 2 == 0) {
                    continue;
                }
                if (k > 10) {
                    break;
                }
                result++;
            }

            return result;
        }
    )";

    auto* cFunc = translateFunction(code, "all_constructs");
    ASSERT_NE(cFunc, nullptr);
}
