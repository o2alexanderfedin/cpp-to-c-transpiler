/**
 * @file GlobalVariablesIntegrationTest.cpp
 * @brief Integration tests for global variables, arrays, strings, and types
 *
 * Tests Phase 3 features working together with Phase 1-2 features:
 * - Global variables with functions
 * - Static local variables
 * - String and character literals
 * - Arrays (declaration, initialization, subscript)
 * - Type casts
 * - Integration with control flow
 */

#include "dispatch/FunctionHandler.h"
#include "handlers/VariableHandler.h"
#include "handlers/ExpressionHandler.h"
#include "handlers/StatementHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class GlobalVariablesIntegrationTest
 * @brief Test fixture for Phase 3 integration testing
 */
class GlobalVariablesIntegrationTest : public ::testing::Test {
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
// Global Variables Integration Tests (5 tests)
// ============================================================================

TEST_F(GlobalVariablesIntegrationTest, FunctionUsingGlobalVariable) {
    // Test: Function accessing global variable
    std::string code = R"(
        int globalCounter = 0;

        int increment() {
            globalCounter++;
            return globalCounter;
        }
    )";

    auto* cFunc = translateFunction(code, "increment");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNameAsString(), "increment");
}

TEST_F(GlobalVariablesIntegrationTest, FunctionModifyingMultipleGlobals) {
    // Test: Function accessing multiple global variables
    std::string code = R"(
        int total = 0;
        int count = 0;

        int add_value(int value) {
            total += value;
            count++;
            return total / count;
        }
    )";

    auto* cFunc = translateFunction(code, "add_value");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 1);
}

TEST_F(GlobalVariablesIntegrationTest, GlobalInitializedWithExpression) {
    // Test: Global variable with complex initialization
    std::string code = R"(
        const int MAX_SIZE = 100;
        int buffer_size = MAX_SIZE / 2;

        int get_buffer_size() {
            return buffer_size;
        }
    )";

    auto* cFunc = translateFunction(code, "get_buffer_size");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, MixedLocalAndGlobalVariables) {
    // Test: Function using both local and global variables
    std::string code = R"(
        int globalValue = 42;

        int compute(int x) {
            int local = x * 2;
            int result = local + globalValue;
            return result;
        }
    )";

    auto* cFunc = translateFunction(code, "compute");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, GlobalConstVariable) {
    // Test: Const global variable
    std::string code = R"(
        const int PI_TIMES_100 = 314;

        int scale_by_pi(int value) {
            return (value * PI_TIMES_100) / 100;
        }
    )";

    auto* cFunc = translateFunction(code, "scale_by_pi");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Static Local Variables Integration Tests (4 tests)
// ============================================================================

TEST_F(GlobalVariablesIntegrationTest, StaticLocalCounter) {
    // Test: Function with static local variable
    std::string code = R"(
        int get_next_id() {
            static int id = 0;
            return ++id;
        }
    )";

    auto* cFunc = translateFunction(code, "get_next_id");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, MultipleStaticLocals) {
    // Test: Multiple static locals in one function
    std::string code = R"(
        int accumulate(int value) {
            static int total = 0;
            static int count = 0;
            total += value;
            count++;
            return total / count;
        }
    )";

    auto* cFunc = translateFunction(code, "accumulate");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, StaticLocalInLoop) {
    // Test: Static local with control flow
    std::string code = R"(
        int track_calls(int n) {
            static int call_count = 0;
            call_count++;

            int sum = 0;
            for (int i = 0; i < n; i++) {
                sum += i;
            }

            return sum + call_count;
        }
    )";

    auto* cFunc = translateFunction(code, "track_calls");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, StaticConstLocal) {
    // Test: Static const local variable
    std::string code = R"(
        int get_constant() {
            static const int MAGIC = 42;
            return MAGIC * 2;
        }
    )";

    auto* cFunc = translateFunction(code, "get_constant");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// String Literal Integration Tests (4 tests)
// ============================================================================

TEST_F(GlobalVariablesIntegrationTest, FunctionReturningString) {
    // Test: Function returning string literal
    std::string code = R"(
        const char* get_message() {
            return "Hello, World!";
        }
    )";

    auto* cFunc = translateFunction(code, "get_message");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, GlobalStringVariable) {
    // Test: Global string pointer
    std::string code = R"(
        const char* greeting = "Hello";

        const char* get_greeting() {
            return greeting;
        }
    )";

    auto* cFunc = translateFunction(code, "get_greeting");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, StringWithEscapeSequences) {
    // Test: String literals with escape sequences
    std::string code = R"(
        const char* get_formatted() {
            return "Line1\nLine2\tTabbed";
        }
    )";

    auto* cFunc = translateFunction(code, "get_formatted");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, CharacterLiteralInFunction) {
    // Test: Character literals
    std::string code = R"(
        char get_newline() {
            return '\n';
        }

        int is_digit(char c) {
            return c >= '0' && c <= '9';
        }
    )";

    auto* cFunc = translateFunction(code, "get_newline");
    ASSERT_NE(cFunc, nullptr);

    auto* cFunc2 = translateFunction(code, "is_digit");
    ASSERT_NE(cFunc2, nullptr);
}

// ============================================================================
// Array Integration Tests (6 tests)
// ============================================================================

TEST_F(GlobalVariablesIntegrationTest, LocalArrayInFunction) {
    // Test: Local array declaration and usage
    std::string code = R"(
        int sum_array() {
            int arr[5] = {1, 2, 3, 4, 5};
            int sum = 0;
            for (int i = 0; i < 5; i++) {
                sum += arr[i];
            }
            return sum;
        }
    )";

    auto* cFunc = translateFunction(code, "sum_array");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, ArrayAsParameter) {
    // Test: Function taking array parameter
    std::string code = R"(
        int sum_param(int arr[], int size) {
            int total = 0;
            for (int i = 0; i < size; i++) {
                total += arr[i];
            }
            return total;
        }
    )";

    auto* cFunc = translateFunction(code, "sum_param");
    ASSERT_NE(cFunc, nullptr);
    EXPECT_EQ(cFunc->getNumParams(), 2);
}

TEST_F(GlobalVariablesIntegrationTest, GlobalArray) {
    // Test: Global array declaration
    std::string code = R"(
        int values[10] = {0, 1, 2, 3, 4, 5, 6, 7, 8, 9};

        int get_value(int index) {
            if (index >= 0 && index < 10) {
                return values[index];
            }
            return -1;
        }
    )";

    auto* cFunc = translateFunction(code, "get_value");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, MultiDimensionalArray) {
    // Test: 2D array
    std::string code = R"(
        int matrix_sum() {
            int matrix[3][3] = {
                {1, 2, 3},
                {4, 5, 6},
                {7, 8, 9}
            };

            int sum = 0;
            for (int i = 0; i < 3; i++) {
                for (int j = 0; j < 3; j++) {
                    sum += matrix[i][j];
                }
            }
            return sum;
        }
    )";

    auto* cFunc = translateFunction(code, "matrix_sum");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, PartialArrayInitialization) {
    // Test: Partial initialization (rest should be zero)
    std::string code = R"(
        int check_zeros() {
            int arr[10] = {1, 2, 3};
            return arr[9];  // Should be 0
        }
    )";

    auto* cFunc = translateFunction(code, "check_zeros");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, CharArray) {
    // Test: Character array (string)
    std::string code = R"(
        int get_first_char() {
            char str[6] = "Hello";
            return str[0];
        }
    )";

    auto* cFunc = translateFunction(code, "get_first_char");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Type Cast Integration Tests (4 tests)
// ============================================================================

TEST_F(GlobalVariablesIntegrationTest, SimpleTypeCast) {
    // Test: C-style cast in function
    std::string code = R"(
        int truncate_float(float x) {
            return (int)x;
        }
    )";

    auto* cFunc = translateFunction(code, "truncate_float");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, PointerCast) {
    // Test: Pointer type cast
    std::string code = R"(
        void* get_pointer(int* ptr) {
            return (void*)ptr;
        }
    )";

    auto* cFunc = translateFunction(code, "get_pointer");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, CastInExpression) {
    // Test: Cast within complex expression
    std::string code = R"(
        int compute(float a, float b) {
            int x = (int)a;
            int y = (int)b;
            return x + y;
        }
    )";

    auto* cFunc = translateFunction(code, "compute");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, ConstCast) {
    // Test: Const cast
    std::string code = R"(
        char* remove_const(const char* str) {
            return (char*)str;
        }
    )";

    auto* cFunc = translateFunction(code, "remove_const");
    ASSERT_NE(cFunc, nullptr);
}

// ============================================================================
// Complex Integration Tests (7 tests)
// ============================================================================

TEST_F(GlobalVariablesIntegrationTest, GlobalArrayWithLoop) {
    // Test: Global array manipulation with loop
    std::string code = R"(
        int data[100];

        void initialize_data() {
            for (int i = 0; i < 100; i++) {
                data[i] = i * i;
            }
        }
    )";

    auto* cFunc = translateFunction(code, "initialize_data");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, StaticArrayAccumulator) {
    // Test: Static array for caching
    std::string code = R"(
        int get_cached(int index) {
            static int cache[10] = {0};

            if (cache[index] == 0) {
                cache[index] = index * index;
            }

            return cache[index];
        }
    )";

    auto* cFunc = translateFunction(code, "get_cached");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, GlobalLookupTable) {
    // Test: Global lookup table
    std::string code = R"(
        const int lookup[5] = {2, 4, 8, 16, 32};

        int power_of_two(int n) {
            if (n >= 0 && n < 5) {
                return lookup[n];
            }
            return 0;
        }
    )";

    auto* cFunc = translateFunction(code, "power_of_two");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, ArraySumWithCast) {
    // Test: Array processing with type cast
    std::string code = R"(
        float average(int arr[], int size) {
            int sum = 0;
            for (int i = 0; i < size; i++) {
                sum += arr[i];
            }
            return (float)sum / (float)size;
        }
    )";

    auto* cFunc = translateFunction(code, "average");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, StringProcessingFunction) {
    // Test: String processing with char array
    std::string code = R"(
        int count_chars(const char* str, char target) {
            int count = 0;
            for (int i = 0; str[i] != '\0'; i++) {
                if (str[i] == target) {
                    count++;
                }
            }
            return count;
        }
    )";

    auto* cFunc = translateFunction(code, "count_chars");
    ASSERT_NE(cFunc, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, ComplexGlobalState) {
    // Test: Multiple global variables with complex logic
    std::string code = R"(
        int global_sum = 0;
        int global_count = 0;
        const int MAX_VALUES = 100;

        int add_to_global(int value) {
            if (global_count < MAX_VALUES) {
                global_sum += value;
                global_count++;
                return 1;
            }
            return 0;
        }

        int get_average() {
            if (global_count == 0) {
                return 0;
            }
            return global_sum / global_count;
        }
    )";

    auto* cFunc = translateFunction(code, "add_to_global");
    ASSERT_NE(cFunc, nullptr);

    auto* cFunc2 = translateFunction(code, "get_average");
    ASSERT_NE(cFunc2, nullptr);
}

TEST_F(GlobalVariablesIntegrationTest, AllPhase3FeaturesTogether) {
    // Test: Everything together - globals, statics, arrays, strings, casts
    std::string code = R"(
        // Global variables
        int history[10];
        int history_count = 0;
        const char* status_messages[3] = {"OK", "Warning", "Error"};

        // Function using all features
        int process_value(int value) {
            // Static local
            static int call_count = 0;
            call_count++;

            // Array access and manipulation
            if (history_count < 10) {
                history[history_count] = value;
                history_count++;
            }

            // Type cast
            float avg = (float)value / (float)call_count;

            // String and character literals
            char status = 'O';
            if (avg > 100.0f) {
                status = 'W';
            }

            // Return cast
            return (int)avg;
        }
    )";

    auto* cFunc = translateFunction(code, "process_value");
    ASSERT_NE(cFunc, nullptr);
}
