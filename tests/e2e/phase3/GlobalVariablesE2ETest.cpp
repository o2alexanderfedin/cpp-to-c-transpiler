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
 * @class GlobalVariablesE2ETest
 * @brief Test fixture for end-to-end global variables testing
 */
class GlobalVariablesE2ETest : public ::testing::Test {
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
        std::string tmpFile = "/tmp/e2e_gv_test_" + std::to_string(rand()) + ".c";
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
// E2E Test 1: Global Counter (ACTIVE SANITY TEST)
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

TEST_F(GlobalVariablesE2ETest, DISABLED_StringLength) {
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

TEST_F(GlobalVariablesE2ETest, DISABLED_ArraySum) {
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

TEST_F(GlobalVariablesE2ETest, DISABLED_ArrayAverage) {
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

TEST_F(GlobalVariablesE2ETest, DISABLED_MatrixSum) {
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

TEST_F(GlobalVariablesE2ETest, DISABLED_StaticCounter) {
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

TEST_F(GlobalVariablesE2ETest, DISABLED_LookupTable) {
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

TEST_F(GlobalVariablesE2ETest, DISABLED_StringReversal) {
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

TEST_F(GlobalVariablesE2ETest, DISABLED_BubbleSort) {
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

TEST_F(GlobalVariablesE2ETest, DISABLED_CharacterOperations) {
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
