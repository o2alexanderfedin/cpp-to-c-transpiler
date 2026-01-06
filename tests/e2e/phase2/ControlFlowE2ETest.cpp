/**
 * @file ControlFlowE2ETest.cpp
 * @brief End-to-end tests for control flow with real algorithms
 *
 * Tests the full pipeline with control flow:
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
 * @class ControlFlowE2ETest
 * @brief Test fixture for end-to-end control flow testing
 */
class ControlFlowE2ETest : public ::testing::Test {
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

        // Register handlers needed for control flow tests
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
        InitListExprHandler::registerWith(*pipeline.dispatcher);

        // Statement handlers (including control flow)
        CompoundStmtHandler::registerWith(*pipeline.dispatcher);
        DeclStmtHandler::registerWith(*pipeline.dispatcher);
        ReturnStmtHandler::registerWith(*pipeline.dispatcher);
        StatementHandler::registerWith(*pipeline.dispatcher);  // Handles if, while, for, switch

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
        int actualExitCode = cpptoc::test::compileAndRun(cCode, "e2e_control_flow");

        if (actualExitCode == -1) {
            std::cerr << "Compilation failed!\n";
            std::cerr << "Generated C code:\n" << cCode << "\n";
            return false;
        }

        return actualExitCode == expectedExitCode;
    }
};

// ============================================================================
// E2E Test 1: Fibonacci (Iterative)
// ============================================================================

TEST_F(ControlFlowE2ETest, Fibonacci) {
    std::string cppCode = R"(
        int fibonacci(int n) {
            int a = 0;
            int b = 1;
            for (int i = 0; i < n; i++) {
                int tmp = a;
                a = b;
                b = tmp + b;
            }
            return a;
        }

        int main() {
            return fibonacci(10);  // 10th Fibonacci number is 55
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 55)) << "Expected exit code 55 (10th Fibonacci)";
}

// ============================================================================
// E2E Test 2: Factorial
// ============================================================================

TEST_F(ControlFlowE2ETest, Factorial) {
    std::string cppCode = R"(
        int factorial(int n) {
            int result = 1;
            for (int i = 1; i <= n; i++) {
                result = result * i;
            }
            return result;
        }

        int main() {
            return factorial(5);  // 5! = 120
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 120)) << "Expected exit code 120 (5!)";
}

// ============================================================================
// E2E Test 3: GCD (Greatest Common Divisor)
// ============================================================================

TEST_F(ControlFlowE2ETest, GCD) {
    std::string cppCode = R"(
        int gcd(int a, int b) {
            while (b != 0) {
                int tmp = b;
                b = a % b;
                a = tmp;
            }
            return a;
        }

        int main() {
            return gcd(48, 18);  // GCD(48, 18) = 6
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 6)) << "Expected exit code 6 (GCD(48, 18))";
}

// ============================================================================
// E2E Test 4: IsPrime
// ============================================================================

TEST_F(ControlFlowE2ETest, IsPrime) {
    std::string cppCode = R"(
        int isPrime(int n) {
            if (n < 2) {
                return 0;
            }
            for (int i = 2; i * i <= n; i++) {
                if (n % i == 0) {
                    return 0;
                }
            }
            return 1;
        }

        int main() {
            return isPrime(17);  // 17 is prime, returns 1
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 1)) << "Expected exit code 1 (17 is prime)";
}

// ============================================================================
// E2E Test 5: Power
// ============================================================================

TEST_F(ControlFlowE2ETest, Power) {
    std::string cppCode = R"(
        int power(int base, int exp) {
            int result = 1;
            for (int i = 0; i < exp; i++) {
                result = result * base;
            }
            return result;
        }

        int main() {
            return power(2, 6);  // 2^6 = 64
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 64)) << "Expected exit code 64 (2^6)";
}

// ============================================================================
// E2E Test 6: Sum Array
// ============================================================================

TEST_F(ControlFlowE2ETest, SumArray) {
    std::string cppCode = R"(
        int sumArray(int arr[], int size) {
            int sum = 0;
            for (int i = 0; i < size; i++) {
                sum = sum + arr[i];
            }
            return sum;
        }

        int main() {
            int numbers[] = {1, 2, 3, 4, 5};
            return sumArray(numbers, 5);  // 1+2+3+4+5 = 15
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 15)) << "Expected exit code 15 (sum of 1..5)";
}

// ============================================================================
// E2E Test 7: Find Max
// ============================================================================

TEST_F(ControlFlowE2ETest, FindMax) {
    std::string cppCode = R"(
        int findMax(int arr[], int size) {
            int max = arr[0];
            for (int i = 1; i < size; i++) {
                if (arr[i] > max) {
                    max = arr[i];
                }
            }
            return max;
        }

        int main() {
            int numbers[] = {3, 7, 2, 9, 1};
            return findMax(numbers, 5);  // Max is 9
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 9)) << "Expected exit code 9 (max element)";
}

// ============================================================================
// E2E Test 8: Linear Search
// ============================================================================

TEST_F(ControlFlowE2ETest, LinearSearch) {
    std::string cppCode = R"(
        int linearSearch(int arr[], int size, int target) {
            for (int i = 0; i < size; i++) {
                if (arr[i] == target) {
                    return i;
                }
            }
            return -1;
        }

        int main() {
            int numbers[] = {10, 20, 30, 40, 50};
            int index = linearSearch(numbers, 5, 30);
            // Found at index 2, but return adjusted value for testing
            if (index == 2) {
                return 42;  // Success indicator
            }
            return 0;
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 42)) << "Expected exit code 42 (found at index 2)";
}

// ============================================================================
// E2E Test 9: Day of Week (State Machine)
// ============================================================================

TEST_F(ControlFlowE2ETest, DayOfWeek) {
    std::string cppCode = R"(
        int dayLength(int day) {
            switch (day) {
                case 0:
                    return 6;  // Sunday
                case 1:
                    return 6;  // Monday
                case 2:
                    return 7;  // Tuesday
                case 3:
                    return 9;  // Wednesday
                case 4:
                    return 8;  // Thursday
                case 5:
                    return 6;  // Friday
                case 6:
                    return 8;  // Saturday
                default:
                    return 0;
            }
        }

        int main() {
            return dayLength(3);  // Wednesday = 9
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 9)) << "Expected exit code 9 (Wednesday length)";
}

// ============================================================================
// E2E Test 10: Calculator (State Machine)
// ============================================================================

TEST_F(ControlFlowE2ETest, Calculator) {
    std::string cppCode = R"(
        int calculate(int a, int b, int op) {
            switch (op) {
                case 1:  // Add
                    return a + b;
                case 2:  // Subtract
                    return a - b;
                case 3:  // Multiply
                    return a * b;
                case 4:  // Divide
                    if (b != 0) {
                        return a / b;
                    }
                    return 0;
                default:
                    return 0;
            }
        }

        int main() {
            return calculate(15, 3, 3);  // 15 * 3 = 45
        }
    )";

    EXPECT_TRUE(runPipeline(cppCode, 45)) << "Expected exit code 45 (15 * 3)";
}

// ============================================================================
// Basic Sanity Test (enabled)
// ============================================================================

TEST_F(ControlFlowE2ETest, BasicSanity) {
    // Just verify test infrastructure works
    EXPECT_TRUE(true);
}
