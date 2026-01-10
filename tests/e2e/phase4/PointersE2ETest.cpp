/**
 * @file PointersE2ETest.cpp
 * @brief End-to-end tests for pointers, references, and pointer operations
 *
 * Tests the full pipeline with Phase 42 features:
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
#include "dispatch/InitListExprHandler.h"
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
 * @class PointersE2ETest
 * @brief Test fixture for end-to-end pointers testing
 */
class PointersE2ETest : public ::testing::Test {
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

        // Register handlers needed for pointer tests
        // Base handlers first
        TypeHandler::registerWith(*pipeline.dispatcher);
        ParameterHandler::registerWith(*pipeline.dispatcher);

        // Expression handlers (including pointer operations)
        LiteralHandler::registerWith(*pipeline.dispatcher);
        DeclRefExprHandler::registerWith(*pipeline.dispatcher);
        BinaryOperatorHandler::registerWith(*pipeline.dispatcher);
        UnaryOperatorHandler::registerWith(*pipeline.dispatcher);  // Handles * (dereference) and & (address-of)
        ImplicitCastExprHandler::registerWith(*pipeline.dispatcher);
        ParenExprHandler::registerWith(*pipeline.dispatcher);
        CallExprHandler::registerWith(*pipeline.dispatcher);
        ArraySubscriptExprHandler::registerWith(*pipeline.dispatcher);
        InitListExprHandler::registerWith(*pipeline.dispatcher);  // Handles array initializers like {1, 2, 3}

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
        int actualExitCode = cpptoc::test::compileAndRun(cCode, "e2e_pointers");

        if (actualExitCode == -1) {
            std::cerr << "Compilation failed!\n";
            std::cerr << "Generated C code:\n" << cCode << "\n";
            return false;
        }

        return actualExitCode == expectedExitCode;
    }
};

// ============================================================================
// E2E Test 1: Pointer Swap
// ============================================================================

TEST_F(PointersE2ETest, PointerSwap) {
    std::string cppCode = R"(
        void swap(int* a, int* b) {
            int temp = *a;
            *a = *b;
            *b = temp;
        }

        int main() {
            int x = 3;
            int y = 7;
            swap(&x, &y);
            return x;  // Returns 7 (swapped value)
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 7)) << "Expected exit code 7 (swapped value)";
}

// ============================================================================
// E2E Test 2: Simple Pointer Usage
// ============================================================================

TEST_F(PointersE2ETest, SimplePointerUsage) {
    std::string cppCode = R"(
        int main() {
            int value = 42;
            int* ptr = &value;
            *ptr = *ptr + 8;
            return value;  // Returns 50
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 50)) << "Expected exit code 50 (modified via pointer)";
}

// ============================================================================
// E2E Test 3: Array Reversal with Pointers
// ============================================================================

TEST_F(PointersE2ETest, ArrayReversalPointers) {
    std::string cppCode = R"(
        void reverse(int* arr, int size) {
            int* left = arr;
            int* right = arr + size - 1;

            while (left < right) {
                int temp = *left;
                *left = *right;
                *right = temp;
                left = left + 1;
                right = right - 1;
            }
        }

        int main() {
            int arr[] = {1, 2, 3, 4, 5};
            reverse(arr, 5);
            // After reversal: {5, 4, 3, 2, 1}
            return arr[0];  // Returns 5
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 5)) << "Expected exit code 5 (first element after reversal)";
}

// ============================================================================
// E2E Test 4: String Manipulation with Pointers
// ============================================================================

TEST_F(PointersE2ETest, StringLengthPointer) {
    std::string cppCode = R"(
        int stringLength(const char* str) {
            const char* ptr = str;
            while (*ptr != '\0') {
                ptr = ptr + 1;
            }
            return ptr - str;
        }

        int main() {
            const char* text = "Hello";
            return stringLength(text);  // Returns 5
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 5)) << "Expected exit code 5 (string length)";
}

// ============================================================================
// E2E Test 5: Pointer-Based Search
// ============================================================================

TEST_F(PointersE2ETest, PointerSearch) {
    std::string cppCode = R"(
        int* findValue(int* arr, int size, int target) {
            int* end = arr + size;
            for (int* ptr = arr; ptr < end; ptr = ptr + 1) {
                if (*ptr == target) {
                    return ptr;
                }
            }
            return 0;
        }

        int main() {
            int arr[] = {10, 20, 30, 40, 50};
            int* result = findValue(arr, 5, 30);
            if (result != 0) {
                return result - arr;  // Returns 2 (index of 30)
            }
            return -1;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 2)) << "Expected exit code 2 (index of found element)";
}

// ============================================================================
// E2E Test 6: Reference-Based Swap
// ============================================================================

TEST_F(PointersE2ETest, ReferenceSwap) {
    std::string cppCode = R"(
        void swapRef(int& a, int& b) {
            int temp = a;
            a = b;
            b = temp;
        }

        int main() {
            int x = 5;
            int y = 9;
            swapRef(x, y);
            return x;  // Returns 9
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 9)) << "Expected exit code 9 (swapped via reference)";
}

// ============================================================================
// E2E Test 7: Pointer Arithmetic Sum
// ============================================================================

TEST_F(PointersE2ETest, PointerArithmeticSum) {
    std::string cppCode = R"(
        int sumArray(int* arr, int size) {
            int sum = 0;
            int* end = arr + size;
            for (int* ptr = arr; ptr < end; ptr = ptr + 1) {
                sum = sum + *ptr;
            }
            return sum;
        }

        int main() {
            int values[] = {1, 2, 3, 4, 5};
            return sumArray(values, 5);  // Returns 15
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 15)) << "Expected exit code 15 (array sum)";
}

// ============================================================================
// E2E Test 8: Find Maximum with Pointer
// ============================================================================

TEST_F(PointersE2ETest, FindMaxPointer) {
    std::string cppCode = R"(
        int* findMax(int* arr, int size) {
            if (size <= 0) {
                return 0;
            }

            int* maxPtr = arr;
            for (int i = 1; i < size; i = i + 1) {
                if (arr[i] > *maxPtr) {
                    maxPtr = &arr[i];
                }
            }
            return maxPtr;
        }

        int main() {
            int values[] = {3, 7, 2, 9, 1};
            int* max = findMax(values, 5);
            if (max != 0) {
                return *max;  // Returns 9
            }
            return -1;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 9)) << "Expected exit code 9 (maximum value)";
}

// ============================================================================
// E2E Test 9: Array Copy with Pointers
// ============================================================================

TEST_F(PointersE2ETest, ArrayCopyPointers) {
    std::string cppCode = R"(
        void copyArray(int* dest, const int* src, int size) {
            int* destEnd = dest + size;
            while (dest < destEnd) {
                *dest = *src;
                dest = dest + 1;
                src = src + 1;
            }
        }

        int main() {
            int source[] = {1, 2, 3, 4, 5};
            int destination[5];
            copyArray(destination, source, 5);
            return destination[2];  // Returns 3
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 3)) << "Expected exit code 3 (copied element)";
}

// ============================================================================
// E2E Test 10: Two Pointer Technique
// ============================================================================

TEST_F(PointersE2ETest, TwoPointerSum) {
    std::string cppCode = R"(
        int findPairSum(int* arr, int size, int target) {
            int* left = arr;
            int* right = arr + size - 1;

            while (left < right) {
                int sum = *left + *right;
                if (sum == target) {
                    return 1;  // Found
                } else if (sum < target) {
                    left = left + 1;
                } else {
                    right = right - 1;
                }
            }
            return 0;  // Not found
        }

        int main() {
            int sorted[] = {1, 2, 3, 4, 5, 6, 7, 8, 9};
            return findPairSum(sorted, 9, 11);  // 3 + 8 = 11, returns 1
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 1)) << "Expected exit code 1 (pair found)";
}

// ============================================================================
// Basic Sanity Test (infrastructure verification)
// ============================================================================

TEST_F(PointersE2ETest, BasicSanity) {
    // Just verify test infrastructure works
    EXPECT_TRUE(true);
}
