/**
 * @file GlobalVariablesE2ETest.cpp
 * @brief End-to-end tests for global variables, arrays, and literals
 *
 * Tests the full pipeline with Phase 3 features:
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
#include "dispatch/ArraySubscriptExprHandler.h"
#include "dispatch/CompoundStmtHandler.h"
#include "dispatch/DeclStmtHandler.h"
#include "dispatch/ReturnStmtHandler.h"
#include "dispatch/StatementHandler.h"
#include "dispatch/FunctionHandler.h"
#include "dispatch/VariableHandler.h"
#include "dispatch/TranslationUnitHandler.h"
#include <gtest/gtest.h>

using namespace cpptoc;

/**
 * @class GlobalVariablesE2ETest
 * @brief Test fixture for end-to-end global variables testing
 */
class GlobalVariablesE2ETest : public ::testing::Test {
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

        // Register handlers needed for global variables tests
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
        ArraySubscriptExprHandler::registerWith(*pipeline.dispatcher);

        // Statement handlers
        CompoundStmtHandler::registerWith(*pipeline.dispatcher);
        DeclStmtHandler::registerWith(*pipeline.dispatcher);
        ReturnStmtHandler::registerWith(*pipeline.dispatcher);
        StatementHandler::registerWith(*pipeline.dispatcher);

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
        int actualExitCode = cpptoc::test::compileAndRun(cCode, "e2e_global_vars");

        if (actualExitCode == -1) {
            std::cerr << "Compilation failed!\n";
            std::cerr << "Generated C code:\n" << cCode << "\n";
            return false;
        }

        return actualExitCode == expectedExitCode;
    }
};

// ============================================================================
// E2E Test 1: Global Counter
// ============================================================================

TEST_F(GlobalVariablesE2ETest, GlobalCounter) {
    std::string cppCode = R"(
        int counter = 0;

        int increment() {
            counter = counter + 1;
            return counter;
        }

        int main() {
            increment();
            increment();
            return increment();  // Returns 3
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 3)) << "Expected exit code 3 (global counter)";
}

// ============================================================================
// E2E Test 2: String Length Calculation
// ============================================================================

TEST_F(GlobalVariablesE2ETest, StringLength) {
    std::string cppCode = R"(
        int stringLength(const char* str) {
            int len = 0;
            while (str[len] != '\0') {
                len = len + 1;
            }
            return len;
        }

        int main() {
            const char* text = "Hello";
            return stringLength(text);  // Returns 5
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 5)) << "Expected exit code 5 (string length)";
}

// ============================================================================
// E2E Test 3: Array Sum
// ============================================================================

TEST_F(GlobalVariablesE2ETest, ArraySum) {
    std::string cppCode = R"(
        int values[] = {1, 2, 3, 4, 5};

        int arraySum(int arr[], int size) {
            int sum = 0;
            for (int i = 0; i < size; i++) {
                sum = sum + arr[i];
            }
            return sum;
        }

        int main() {
            return arraySum(values, 5);  // 1+2+3+4+5 = 15
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 15)) << "Expected exit code 15 (array sum)";
}

// ============================================================================
// E2E Test 4: Array Average
// ============================================================================

TEST_F(GlobalVariablesE2ETest, ArrayAverage) {
    std::string cppCode = R"(
        int arrayAverage(int arr[], int size) {
            int sum = 0;
            for (int i = 0; i < size; i++) {
                sum = sum + arr[i];
            }
            return sum / size;
        }

        int main() {
            int numbers[] = {10, 20, 30, 40, 50};
            return arrayAverage(numbers, 5);  // (10+20+30+40+50)/5 = 30
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 30)) << "Expected exit code 30 (array average)";
}

// ============================================================================
// E2E Test 5: Matrix Operations (Simple)
// ============================================================================

TEST_F(GlobalVariablesE2ETest, MatrixSum) {
    std::string cppCode = R"(
        int matrixSum(int matrix[][3], int rows) {
            int sum = 0;
            for (int i = 0; i < rows; i++) {
                for (int j = 0; j < 3; j++) {
                    sum = sum + matrix[i][j];
                }
            }
            return sum;
        }

        int main() {
            int matrix[2][3] = {{1, 2, 3}, {4, 5, 6}};
            return matrixSum(matrix, 2);  // 1+2+3+4+5+6 = 21
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 21)) << "Expected exit code 21 (matrix sum)";
}

// ============================================================================
// E2E Test 6: Static Variable Counter
// ============================================================================

TEST_F(GlobalVariablesE2ETest, StaticCounter) {
    std::string cppCode = R"(
        int getNextId() {
            static int id = 0;
            id = id + 1;
            return id;
        }

        int main() {
            getNextId();  // Returns 1
            getNextId();  // Returns 2
            return getNextId();  // Returns 3
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 3)) << "Expected exit code 3 (static counter)";
}

// ============================================================================
// E2E Test 7: Global Lookup Table
// ============================================================================

TEST_F(GlobalVariablesE2ETest, LookupTable) {
    std::string cppCode = R"(
        int squares[] = {0, 1, 4, 9, 16, 25, 36, 49, 64, 81};

        int getSquare(int n) {
            if (n >= 0 && n < 10) {
                return squares[n];
            }
            return -1;
        }

        int main() {
            return getSquare(7);  // 7^2 = 49
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 49)) << "Expected exit code 49 (lookup table)";
}

// ============================================================================
// E2E Test 8: String Reversal (In-Place)
// ============================================================================

TEST_F(GlobalVariablesE2ETest, StringReversal) {
    std::string cppCode = R"(
        void reverseString(char str[], int len) {
            int i = 0;
            int j = len - 1;
            while (i < j) {
                char tmp = str[i];
                str[i] = str[j];
                str[j] = tmp;
                i = i + 1;
                j = j - 1;
            }
        }

        int main() {
            char text[] = {'a', 'b', 'c', 'd', '\0'};
            reverseString(text, 4);
            // text is now "dcba"
            // Return ASCII value difference to verify
            return text[0] - 'a';  // 'd' - 'a' = 3
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 3)) << "Expected exit code 3 (reversed string)";
}

// ============================================================================
// E2E Test 9: Array Sorting (Bubble Sort)
// ============================================================================

TEST_F(GlobalVariablesE2ETest, BubbleSort) {
    std::string cppCode = R"(
        void bubbleSort(int arr[], int size) {
            for (int i = 0; i < size - 1; i++) {
                for (int j = 0; j < size - i - 1; j++) {
                    if (arr[j] > arr[j + 1]) {
                        int tmp = arr[j];
                        arr[j] = arr[j + 1];
                        arr[j + 1] = tmp;
                    }
                }
            }
        }

        int main() {
            int numbers[] = {5, 2, 8, 1, 9};
            bubbleSort(numbers, 5);
            // After sorting: {1, 2, 5, 8, 9}
            // Return middle element
            return numbers[2];  // Returns 5
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 5)) << "Expected exit code 5 (bubble sort middle)";
}

// ============================================================================
// E2E Test 10: Character Literal Operations
// ============================================================================

TEST_F(GlobalVariablesE2ETest, CharacterOperations) {
    std::string cppCode = R"(
        int charDifference(char a, char b) {
            return b - a;
        }

        int main() {
            char start = 'A';
            char end = 'Z';
            return charDifference(start, end);  // 'Z' - 'A' = 25
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 25)) << "Expected exit code 25 (Z - A)";
}

// ============================================================================
// Basic Sanity Test (infrastructure verification)
// ============================================================================

TEST_F(GlobalVariablesE2ETest, BasicSanity) {
    // Just verify test infrastructure works
    EXPECT_TRUE(true);
}
