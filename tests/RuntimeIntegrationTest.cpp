// Phase 16-01: Runtime Integration Testing Framework
// Provides systematic framework for compiling and executing transpiled C code
//
// Purpose: Verify that transpiled C code compiles correctly and executes as expected
// - Extends existing ValidationTest.cpp patterns
// - Uses RuntimeTestHarness for compile/execute pipeline
// - Establishes foundation for comprehensive end-to-end testing
//
// Test Coverage:
// - Initial tests (2): Simple function, struct initialization
// - Core behaviors (10): Arithmetic, control flow, functions, structs, pointers, etc.

#include <gtest/gtest.h>
#include "RuntimeTestHarness.h"
#include <regex>
#include <memory>

// RuntimeIntegrationTest: GTest fixture for runtime integration tests
//
// Provides helper methods for:
// - Compiling C code
// - Running transpiled programs
// - Asserting output matches expected values
// - Pattern matching with regex
//
// Usage:
//   TEST_F(RuntimeIntegrationTest, MyTest) {
//       assertTranspiledRuns("int main() { return 0; }", "");
//   }
class RuntimeIntegrationTest : public ::testing::Test {
protected:
    void SetUp() override {
        harness = std::make_unique<RuntimeTestHarness>();
    }

    void TearDown() override {
        harness.reset(); // Cleanup temp files
    }

    // Helper: Assert C code compiles
    void assertCompiles(const std::string& c_code) {
        auto result = harness->compileC(c_code);
        ASSERT_TRUE(result.success)
            << "Compilation failed:\n" << result.stderr_output;
    }

    // Helper: Assert transpiled C++ compiles and runs
    // For Phase 16-01, we're testing C code directly (transpiler integration comes later)
    void assertTranspiledRuns(const std::string& cpp_code,
                             const std::string& expected_output = "") {
        auto result = harness->transpileCompileExecute(cpp_code);
        ASSERT_TRUE(result.success)
            << "Execution failed:\n" << result.stderr_output;

        if (!expected_output.empty()) {
            EXPECT_EQ(result.stdout_output, expected_output)
                << "Output mismatch";
        }
    }

    // Helper: Assert output matches regex
    void assertOutputMatches(const RuntimeTestHarness::ExecutionResult& result,
                            const std::string& regex_pattern) {
        ASSERT_TRUE(result.success);
        EXPECT_TRUE(std::regex_search(result.stdout_output,
                                     std::regex(regex_pattern)))
            << "Output '" << result.stdout_output << "' doesn't match pattern '" << regex_pattern << "'";
    }

    std::unique_ptr<RuntimeTestHarness> harness;
};

// ============================================================================
// Initial Tests (2 tests)
// ============================================================================

// Test 1: Simple function transpiles and runs
TEST_F(RuntimeIntegrationTest, SimpleFunctionTranspiles) {
    const char* code = R"(
        #include <stdio.h>
        int add(int a, int b) { return a + b; }
        int main() { printf("%d\n", add(2, 3)); return 0; }
    )";

    assertTranspiledRuns(code, "5\n");
}

// Test 2: Struct initialization works
TEST_F(RuntimeIntegrationTest, StructInitializationWorks) {
    const char* code = R"(
        #include <stdio.h>
        struct Point { int x; int y; };
        int main() {
            struct Point p = {10, 20};
            printf("%d %d\n", p.x, p.y);
            return 0;
        }
    )";

    assertTranspiledRuns(code, "10 20\n");
}

// ============================================================================
// Core Behavior Tests (10 tests)
// ============================================================================

// Test 3: Arithmetic operations work correctly
TEST_F(RuntimeIntegrationTest, ArithmeticOperations) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            int a = 10, b = 3;
            printf("%d %d %d %d %d\n", a+b, a-b, a*b, a/b, a%b);
            return 0;
        }
    )";
    assertTranspiledRuns(code, "13 7 30 3 1\n");
}

// Test 4: Control flow (if/else, loops, switch) works
TEST_F(RuntimeIntegrationTest, ControlFlow) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            // if/else
            int x = 5;
            if (x > 3) {
                printf("greater\n");
            } else {
                printf("less\n");
            }

            // for loop
            int sum = 0;
            for (int i = 1; i <= 5; i++) {
                sum += i;
            }
            printf("%d\n", sum);

            // switch
            int val = 2;
            switch(val) {
                case 1: printf("one\n"); break;
                case 2: printf("two\n"); break;
                default: printf("other\n"); break;
            }

            return 0;
        }
    )";
    assertTranspiledRuns(code, "greater\n15\ntwo\n");
}

// Test 5: Function calls with parameters and return values
TEST_F(RuntimeIntegrationTest, FunctionCalls) {
    const char* code = R"(
        #include <stdio.h>
        int multiply(int a, int b) { return a * b; }
        int divide(int a, int b) { return a / b; }
        int main() {
            printf("%d\n", multiply(6, 7));
            printf("%d\n", divide(20, 4));
            return 0;
        }
    )";
    assertTranspiledRuns(code, "42\n5\n");
}

// Test 6: Struct field access (reads/writes)
TEST_F(RuntimeIntegrationTest, StructFieldAccess) {
    const char* code = R"(
        #include <stdio.h>
        struct Rectangle { int width; int height; };
        int main() {
            struct Rectangle r = {10, 20};
            r.width = 15;
            r.height = r.height + 5;
            printf("%d %d\n", r.width, r.height);
            return 0;
        }
    )";
    assertTranspiledRuns(code, "15 25\n");
}

// Test 7: Pointer arithmetic and array indexing
TEST_F(RuntimeIntegrationTest, PointerArithmetic) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            int arr[5] = {10, 20, 30, 40, 50};
            printf("%d\n", arr[2]);
            printf("%d\n", *(arr + 3));
            int *ptr = arr;
            printf("%d\n", ptr[4]);
            return 0;
        }
    )";
    assertTranspiledRuns(code, "30\n40\n50\n");
}

// Test 8: String operations (basic manipulation)
TEST_F(RuntimeIntegrationTest, StringOperations) {
    const char* code = R"(
        #include <stdio.h>
        #include <string.h>
        int main() {
            char str1[20] = "Hello";
            char str2[20] = "World";
            strcat(str1, " ");
            strcat(str1, str2);
            printf("%s\n", str1);
            printf("%zu\n", strlen(str1));
            return 0;
        }
    )";
    assertTranspiledRuns(code, "Hello World\n11\n");
}

// Test 9: Static variables (initialization and persistence)
TEST_F(RuntimeIntegrationTest, StaticVariables) {
    const char* code = R"(
        #include <stdio.h>
        int counter() {
            static int count = 0;
            count++;
            return count;
        }
        int main() {
            printf("%d\n", counter());
            printf("%d\n", counter());
            printf("%d\n", counter());
            return 0;
        }
    )";
    assertTranspiledRuns(code, "1\n2\n3\n");
}

// Test 10: Recursion (factorial)
TEST_F(RuntimeIntegrationTest, RecursiveFactorial) {
    const char* code = R"(
        #include <stdio.h>
        int factorial(int n) {
            return n <= 1 ? 1 : n * factorial(n-1);
        }
        int main() {
            printf("%d\n", factorial(5));
            printf("%d\n", factorial(6));
            return 0;
        }
    )";
    assertTranspiledRuns(code, "120\n720\n");
}

// Test 11: Multiple return paths (early returns)
TEST_F(RuntimeIntegrationTest, MultipleReturnPaths) {
    const char* code = R"(
        #include <stdio.h>
        int check_value(int x) {
            if (x < 0) return -1;
            if (x == 0) return 0;
            return 1;
        }
        int main() {
            printf("%d\n", check_value(-5));
            printf("%d\n", check_value(0));
            printf("%d\n", check_value(10));
            return 0;
        }
    )";
    assertTranspiledRuns(code, "-1\n0\n1\n");
}

// Test 12: Non-zero exit codes
TEST_F(RuntimeIntegrationTest, NonZeroExitCode) {
    const char* code = R"(
        int main() { return 42; }
    )";
    auto result = harness->transpileCompileExecute(code);
    ASSERT_TRUE(result.success);
    EXPECT_EQ(result.exit_code, 42);
}
