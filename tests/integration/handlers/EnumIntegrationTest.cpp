/**
 * @file EnumIntegrationTest.cpp
 * @brief Integration tests for enum interactions with other language features
 *
 * Tests Phase 47 scoped enum features working together with Phase 1-6 features:
 * - Scoped enums (enum class) with name prefixing
 * - Unscoped enums (C-style, direct mapping)
 * - Enum constants in control flow (switch, if/else)
 * - Enum parameters and return values
 * - Enum fields in structs
 * - Enum arrays and pointers
 * - Enum in binary operations
 * - Mixed scoped and unscoped enums
 */

#include "dispatch/FunctionHandler.h"
#include "dispatch/VariableHandler.h"
#include "dispatch/StatementHandler.h"
#include "DispatcherTestHelper.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class EnumIntegrationTest
 * @brief Test fixture for Phase 47 enum integration testing
 */
class EnumIntegrationTest : public ::testing::Test {
protected:
    cpptoc::test::DispatcherPipeline pipeline;

    void SetUp() override {
        pipeline = cpptoc::test::createDispatcherPipeline("int dummy;");

        // Register handlers
        FunctionHandler::registerWith(*pipeline.dispatcher);
        VariableHandler::registerWith(*pipeline.dispatcher);
        StatementHandler::registerWith(*pipeline.dispatcher);
    }

    void TearDown() override {
        // Pipeline auto-cleans on destruction
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

        // Dispatch through pipeline
        return pipeline.dispatcher->dispatchDecl<clang::FunctionDecl>(
            testAST->getASTContext(),
            pipeline.cAST->getASTContext(),
            cppFunc
        );
    }
};

// ============================================================================
// Test 1: Scoped Enum in Switch Statement (verify existing works)
// ============================================================================

TEST_F(EnumIntegrationTest, ScopedEnumInSwitch) {
    // Test: Scoped enum with switch statement
    std::string code = R"(
        enum class GameState { Menu, Playing, Paused };

        int getStateCode(GameState state) {
            switch (state) {
                case GameState::Menu:
                    return 0;
                case GameState::Playing:
                    return 1;
                case GameState::Paused:
                    return 2;
                default:
                    return -1;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "getStateCode");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "getStateCode");
    EXPECT_EQ(cFunc->getNumParams(), 1);
}

// ============================================================================
// Test 2: Enum in If/Else Comparisons
// ============================================================================

TEST_F(EnumIntegrationTest, EnumInIfElseComparisons) {
    // Test: Scoped enum in if/else conditions
    std::string code = R"(
        enum class Status { OK, Error, Pending };

        int checkStatus(Status s) {
            if (s == Status::OK) {
                return 1;
            } else if (s == Status::Error) {
                return -1;
            } else {
                return 0;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "checkStatus");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "checkStatus");
}

// ============================================================================
// Test 3: Enum as Function Parameter (Pass by Value)
// ============================================================================

TEST_F(EnumIntegrationTest, EnumAsFunctionParameter) {
    // Test: Enum as function parameter
    std::string code = R"(
        enum class Priority { Low, Medium, High };

        int getPriorityValue(Priority p) {
            return (int)p;
        }
    )";

    auto* cFunc = translateFunction(code, "getPriorityValue");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 1);

    // Verify parameter type is enum
    auto* param = cFunc->getParamDecl(0);
    ASSERT_NE(param, nullptr);
    EXPECT_TRUE(param->getType()->isEnumeralType() ||
                param->getType().getAsString().find("Priority") != std::string::npos);
}

// ============================================================================
// Test 4: Enum as Function Return Type
// ============================================================================

TEST_F(EnumIntegrationTest, EnumAsFunctionReturnType) {
    // Test: Enum as function return type
    std::string code = R"(
        enum class Color { Red, Green, Blue };

        Color getDefaultColor() {
            return Color::Blue;
        }
    )";

    auto* cFunc = translateFunction(code, "getDefaultColor");
    ASSERT_NE(cFunc, nullptr);

    // Verify return type is enum
    auto returnType = cFunc->getReturnType();
    EXPECT_TRUE(returnType->isEnumeralType() ||
                returnType.getAsString().find("Color") != std::string::npos);
}

// ============================================================================
// Test 5: Enum in Struct Field
// ============================================================================

TEST_F(EnumIntegrationTest, EnumInStructField) {
    // Test: Enum as struct field
    std::string code = R"(
        enum class State { Idle, Running, Stopped };

        struct Process {
            int id;
            State state;
        };

        int getProcessState(Process p) {
            return (int)p.state;
        }
    )";

    auto* cFunc = translateFunction(code, "getProcessState");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Test 6: Enum Array
// ============================================================================

TEST_F(EnumIntegrationTest, EnumArray) {
    // Test: Array of enum values
    std::string code = R"(
        enum class Status { OK, Error, Pending };

        int countErrors(Status arr[], int size) {
            int count = 0;
            for (int i = 0; i < size; i++) {
                if (arr[i] == Status::Error) {
                    count++;
                }
            }
            return count;
        }
    )";

    auto* cFunc = translateFunction(code, "countErrors");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

// ============================================================================
// Test 7: Enum Pointer
// ============================================================================

TEST_F(EnumIntegrationTest, EnumPointer) {
    // Test: Pointer to enum
    std::string code = R"(
        enum class Mode { Read, Write, Execute };

        void setMode(Mode* mode) {
            *mode = Mode::Write;
        }
    )";

    auto* cFunc = translateFunction(code, "setMode");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 1);

    // Verify parameter is pointer type
    auto* param = cFunc->getParamDecl(0);
    ASSERT_NE(param, nullptr);
    EXPECT_TRUE(param->getType()->isPointerType());
}

// ============================================================================
// Test 8: Enum in Binary Operations
// ============================================================================

TEST_F(EnumIntegrationTest, EnumInBinaryOperations) {
    // Test: Enum in comparison and equality operations
    std::string code = R"(
        enum class Level { Beginner, Intermediate, Advanced };

        int compareLevels(Level l1, Level l2) {
            if (l1 == l2) {
                return 0;
            } else if (l1 != l2) {
                return 1;
            }
            return -1;
        }
    )";

    auto* cFunc = translateFunction(code, "compareLevels");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

// ============================================================================
// Test 9: Enum in Ternary Operator
// ============================================================================

TEST_F(EnumIntegrationTest, EnumInTernaryOperator) {
    // Test: Enum in ternary conditional expression
    std::string code = R"(
        enum class Result { Success, Failure };

        Result getResult(int value) {
            return value > 0 ? Result::Success : Result::Failure;
        }
    )";

    auto* cFunc = translateFunction(code, "getResult");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Test 10: Mixed Scoped and Unscoped Enums in Same File
// ============================================================================

TEST_F(EnumIntegrationTest, MixedScopedAndUnscopedEnums) {
    // Test: Both scoped and unscoped enums in same translation unit
    std::string code = R"(
        enum Color { RED, GREEN, BLUE };
        enum class State { Idle, Running };

        int convertColorAndState(Color c, State s) {
            int result = 0;
            if (c == RED) result += 1;
            if (s == State::Idle) result += 10;
            return result;
        }
    )";

    auto* cFunc = translateFunction(code, "convertColorAndState");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

// ============================================================================
// Test 11: Enum Constant in Constant Expression
// ============================================================================

TEST_F(EnumIntegrationTest, EnumConstantInConstantExpression) {
    // Test: Enum constant used in constant expressions (array size, etc.)
    std::string code = R"(
        enum class Size { Small = 10, Medium = 20, Large = 30 };

        int getSize() {
            int arr[(int)Size::Small];
            return sizeof(arr) / sizeof(int);
        }
    )";

    auto* cFunc = translateFunction(code, "getSize");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Test 12: Enum with Type Specification in Complex Scenario
// ============================================================================

TEST_F(EnumIntegrationTest, EnumWithTypeSpecificationComplex) {
    // Test: Scoped enum with underlying type in complex scenario
    // Note: Type specification support may be partial in this phase
    std::string code = R"(
        enum class HttpStatus : int { OK = 200, NotFound = 404, Error = 500 };

        int processHttpStatus(HttpStatus status) {
            switch (status) {
                case HttpStatus::OK:
                    return 1;
                case HttpStatus::NotFound:
                    return 0;
                case HttpStatus::Error:
                    return -1;
                default:
                    return -2;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "processHttpStatus");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "processHttpStatus");
}
