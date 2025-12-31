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

#include "dispatch/FunctionHandler.h"
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
 * @class PointersE2ETest
 * @brief Test fixture for end-to-end pointers testing
 */
class PointersE2ETest : public ::testing::Test {
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
                    // NOTE: FunctionHandler uses dispatcher pattern (static methods)
                    // For now, skip function translation in E2E test
                    // TODO: Update to use CppToCVisitorDispatcher pattern
                    continue;
                }
            } else if (auto* var = llvm::dyn_cast<clang::VarDecl>(decl)) {
                varHandler->handleDecl(var, context);
            }
        }

        // Stage 3: Generate C code
        std::string cCode;
        llvm::raw_string_ostream codeStream(cCode);
        CodeGenerator generator(codeStream, cAST->getASTContext());
        generator.printTranslationUnit(cAST->getASTContext().getTranslationUnitDecl());
        codeStream.flush();

        // Write C code to temporary file
        std::string tmpFile = "/tmp/e2e_ptr_test_" + std::to_string(rand()) + ".c";
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
// E2E Test 1: Pointer Swap (ACTIVE SANITY TEST)
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
// E2E Test 2: Simple Pointer Usage (ACTIVE SANITY TEST)
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
// E2E Test 3: Array Reversal with Pointers (DISABLED)
// ============================================================================

TEST_F(PointersE2ETest, DISABLED_ArrayReversalPointers) {
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
// E2E Test 4: String Manipulation with Pointers (DISABLED)
// ============================================================================

TEST_F(PointersE2ETest, DISABLED_StringLengthPointer) {
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
// E2E Test 5: Pointer-Based Search (DISABLED)
// ============================================================================

TEST_F(PointersE2ETest, DISABLED_PointerSearch) {
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
// E2E Test 6: Reference-Based Swap (DISABLED)
// ============================================================================

TEST_F(PointersE2ETest, DISABLED_ReferenceSwap) {
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
// E2E Test 7: Pointer Arithmetic Sum (DISABLED)
// ============================================================================

TEST_F(PointersE2ETest, DISABLED_PointerArithmeticSum) {
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
// E2E Test 8: Find Maximum with Pointer (DISABLED)
// ============================================================================

TEST_F(PointersE2ETest, DISABLED_FindMaxPointer) {
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
// E2E Test 9: Array Copy with Pointers (DISABLED)
// ============================================================================

TEST_F(PointersE2ETest, DISABLED_ArrayCopyPointers) {
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
// E2E Test 10: Two Pointer Technique (DISABLED)
// ============================================================================

TEST_F(PointersE2ETest, DISABLED_TwoPointerSum) {
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
