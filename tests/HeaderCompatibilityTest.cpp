// Phase 16-02: Header Compatibility Testing - C and C++ Headers
// Provides systematic testing for header integration in transpiled C code
//
// Purpose: Verify transpiled code works correctly with:
// - C standard library headers (stdio.h, stdlib.h, string.h, math.h, assert.h)
// - Multiple headers used together
// - Custom user-defined headers
//
// Test Coverage:
// - C stdlib headers (15 tests): stdio.h(5), stdlib.h(4), string.h(3), math.h(2), assert.h(1)
// - Multi-header combinations (5 tests)
// - Custom headers (3 tests)
// - Total: 23 header compatibility tests

#include <gtest/gtest.h>
#include "RuntimeTestHarness.h"
#include <filesystem>
#include <vector>
#include <string>

// HeaderCompatibilityTest: GTest fixture for header compatibility tests
//
// Extends RuntimeIntegrationTest to provide specialized helpers for:
// - Testing C standard library headers
// - Testing multiple headers together
// - Testing custom user-defined headers
//
// Usage:
//   TEST_F(HeaderCompatibilityTest, MyHeaderTest) {
//       assertCHeaderWorks("stdio.h", "int main() { printf(\"test\"); return 0; }");
//   }
class HeaderCompatibilityTest : public ::testing::Test {
protected:
    void SetUp() override {
        harness = std::make_unique<RuntimeTestHarness>();
    }

    void TearDown() override {
        harness.reset(); // Cleanup temp files
    }

    // Helper: Test C header usage
    void assertCHeaderWorks(const std::string& header,
                           const std::string& test_code,
                           const std::string& expected_output = "") {
        std::string full_code = "#include <" + header + ">\n" + test_code;
        auto result = harness->transpileCompileExecute(full_code);
        ASSERT_TRUE(result.success)
            << "Execution failed for header <" << header << ">:\n" << result.stderr_output;

        if (!expected_output.empty()) {
            EXPECT_EQ(result.stdout_output, expected_output)
                << "Output mismatch for header <" << header << ">";
        }
    }

    // Helper: Test multiple headers together
    void assertHeaderCombinationWorks(
        const std::vector<std::string>& headers,
        const std::string& test_code,
        const std::string& expected_output = "",
        const std::vector<std::string>& extra_flags = {}) {

        std::string includes;
        for (const auto& h : headers) {
            includes += "#include <" + h + ">\n";
        }

        std::string full_code = includes + test_code;

        // Compile with extra flags if needed (e.g., -lm for math.h)
        auto result = harness->transpileCompileExecute(full_code, extra_flags);

        ASSERT_TRUE(result.success)
            << "Execution failed for header combination:\n" << result.stderr_output;

        if (!expected_output.empty()) {
            EXPECT_EQ(result.stdout_output, expected_output)
                << "Output mismatch for header combination";
        }
    }

    // Helper: Test custom header file
    void assertCustomHeaderWorks(
        const std::string& header_content,
        const std::string& header_filename,
        const std::string& impl_code,
        const std::string& expected_output = "",
        const std::vector<std::string>& extra_flags = {}) {

        // Write custom header to temp file
        std::string header_file = harness->createTempHeaderFile(header_content, header_filename);
        ASSERT_FALSE(header_file.empty()) << "Failed to create temporary header file";

        // Prepare include path argument
        std::filesystem::path header_path(header_file);
        std::string include_dir = header_path.parent_path().string();

        // Build clang args with include path
        std::vector<std::string> clang_args = {"-I" + include_dir};

        // Add extra flags (like -lm for math functions)
        for (const auto& flag : extra_flags) {
            clang_args.push_back(flag);
        }

        auto result = harness->transpileCompileExecute(impl_code, clang_args);
        ASSERT_TRUE(result.success)
            << "Execution failed for custom header:\n" << result.stderr_output;

        if (!expected_output.empty()) {
            EXPECT_EQ(result.stdout_output, expected_output);
        }
    }

    std::unique_ptr<RuntimeTestHarness> harness;
};

// ============================================================================
// Task 2: C Standard Library Header Tests (15 tests)
// ============================================================================

// ----------------------------------------------------------------------------
// 1. stdio.h Tests (5 tests)
// ----------------------------------------------------------------------------

TEST_F(HeaderCompatibilityTest, StdioH_Printf) {
    const char* code = R"(
        int main() {
            printf("Hello, %s!\n", "World");
            return 0;
        }
    )";
    assertCHeaderWorks("stdio.h", code, "Hello, World!\n");
}

TEST_F(HeaderCompatibilityTest, StdioH_Sprintf) {
    const char* code = R"(
        int main() {
            char buf[100];
            sprintf(buf, "%d + %d = %d", 2, 3, 5);
            printf("%s\n", buf);
            return 0;
        }
    )";
    assertCHeaderWorks("stdio.h", code, "2 + 3 = 5\n");
}

TEST_F(HeaderCompatibilityTest, StdioH_FileOperations) {
    const char* code = R"(
        int main() {
            FILE* f = fopen("/tmp/test_header_file.txt", "w");
            if (f) {
                fprintf(f, "test content\n");
                fclose(f);
                printf("success\n");
            }
            return 0;
        }
    )";
    assertCHeaderWorks("stdio.h", code, "success\n");
}

TEST_F(HeaderCompatibilityTest, StdioH_Sscanf) {
    const char* code = R"(
        int main() {
            const char* input = "42 3.14";
            int i;
            float f;
            sscanf(input, "%d %f", &i, &f);
            printf("%d %.2f\n", i, f);
            return 0;
        }
    )";
    assertCHeaderWorks("stdio.h", code, "42 3.14\n");
}

TEST_F(HeaderCompatibilityTest, StdioH_Snprintf) {
    const char* code = R"(
        int main() {
            char buf[20];
            int written = snprintf(buf, sizeof(buf), "Value: %d", 123);
            printf("%s (length: %d)\n", buf, written);
            return 0;
        }
    )";
    assertCHeaderWorks("stdio.h", code, "Value: 123 (length: 10)\n");
}

// ----------------------------------------------------------------------------
// 2. stdlib.h Tests (4 tests)
// ----------------------------------------------------------------------------

TEST_F(HeaderCompatibilityTest, StdlibH_Malloc) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            int* p = (int*)malloc(sizeof(int) * 10);
            p[5] = 42;
            printf("%d\n", p[5]);
            free(p);
            return 0;
        }
    )";
    assertCHeaderWorks("stdlib.h", code, "42\n");
}

TEST_F(HeaderCompatibilityTest, StdlibH_Atoi) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            const char* str = "12345";
            int val = atoi(str);
            printf("%d\n", val);
            return 0;
        }
    )";
    assertCHeaderWorks("stdlib.h", code, "12345\n");
}

TEST_F(HeaderCompatibilityTest, StdlibH_Rand) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            srand(42); // Fixed seed for reproducible output
            int r1 = rand() % 100;
            int r2 = rand() % 100;
            printf("random values generated\n");
            return 0;
        }
    )";
    assertCHeaderWorks("stdlib.h", code, "random values generated\n");
}

TEST_F(HeaderCompatibilityTest, StdlibH_Exit) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            printf("before exit\n");
            exit(0);
            printf("after exit\n"); // Should not execute
            return 1;
        }
    )";
    assertCHeaderWorks("stdlib.h", code, "before exit\n");
}

// ----------------------------------------------------------------------------
// 3. string.h Tests (3 tests)
// ----------------------------------------------------------------------------

TEST_F(HeaderCompatibilityTest, StringH_Strlen) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            printf("%zu\n", strlen("Hello"));
            return 0;
        }
    )";
    assertCHeaderWorks("string.h", code, "5\n");
}

TEST_F(HeaderCompatibilityTest, StringH_Strcpy) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            char dest[20];
            strcpy(dest, "copied");
            printf("%s\n", dest);
            return 0;
        }
    )";
    assertCHeaderWorks("string.h", code, "copied\n");
}

TEST_F(HeaderCompatibilityTest, StringH_Strcat) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            char str[50] = "Hello";
            strcat(str, " ");
            strcat(str, "World");
            printf("%s\n", str);
            return 0;
        }
    )";
    assertCHeaderWorks("string.h", code, "Hello World\n");
}

// ----------------------------------------------------------------------------
// 4. math.h Tests (2 tests)
// ----------------------------------------------------------------------------

TEST_F(HeaderCompatibilityTest, MathH_Sqrt) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            printf("%.0f\n", sqrt(16.0));
            return 0;
        }
    )";
    // Need -lm flag for math library
    assertHeaderCombinationWorks({"math.h"}, code, "4\n", {"-lm"});
}

TEST_F(HeaderCompatibilityTest, MathH_Pow) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            printf("%.0f\n", pow(2.0, 3.0));
            return 0;
        }
    )";
    // Need -lm flag for math library
    assertHeaderCombinationWorks({"math.h"}, code, "8\n", {"-lm"});
}

// ----------------------------------------------------------------------------
// 5. assert.h Test (1 test)
// ----------------------------------------------------------------------------

TEST_F(HeaderCompatibilityTest, AssertH_Assert) {
    const char* code = R"(
        #include <stdio.h>
        int main() {
            int x = 5;
            assert(x == 5); // Should pass
            printf("assertion passed\n");
            return 0;
        }
    )";
    assertCHeaderWorks("assert.h", code, "assertion passed\n");
}

// ============================================================================
// Task 3: Multi-Header Combination Tests (5 tests)
// ============================================================================

TEST_F(HeaderCompatibilityTest, MultiHeader_StdioStdlib) {
    const char* code = R"(
        int main() {
            int* arr = (int*)malloc(sizeof(int) * 3);
            arr[0] = 1; arr[1] = 2; arr[2] = 3;
            for (int i = 0; i < 3; i++) {
                printf("%d ", arr[i]);
            }
            printf("\n");
            free(arr);
            return 0;
        }
    )";
    assertHeaderCombinationWorks({"stdio.h", "stdlib.h"}, code, "1 2 3 \n");
}

TEST_F(HeaderCompatibilityTest, MultiHeader_StdioString) {
    const char* code = R"(
        int main() {
            char str1[50] = "Hello";
            char str2[50] = "World";
            strcat(str1, " ");
            strcat(str1, str2);
            printf("%s (len=%zu)\n", str1, strlen(str1));
            return 0;
        }
    )";
    assertHeaderCombinationWorks({"stdio.h", "string.h"}, code, "Hello World (len=11)\n");
}

TEST_F(HeaderCompatibilityTest, MultiHeader_StdioMath) {
    const char* code = R"(
        int main() {
            double result = sqrt(pow(3.0, 2.0) + pow(4.0, 2.0));
            printf("%.0f\n", result);
            return 0;
        }
    )";
    assertHeaderCombinationWorks({"stdio.h", "math.h"}, code, "5\n", {"-lm"});
}

TEST_F(HeaderCompatibilityTest, MultiHeader_AllStdlib) {
    const char* code = R"(
        int main() {
            // stdio.h
            char buf[100];
            sprintf(buf, "Result: ");

            // stdlib.h
            int* arr = (int*)malloc(sizeof(int) * 5);
            arr[0] = 10;

            // string.h
            char temp[20];
            sprintf(temp, "%d", arr[0]);
            strcat(buf, temp);

            printf("%s\n", buf);

            free(arr);
            return 0;
        }
    )";
    assertHeaderCombinationWorks({"stdio.h", "stdlib.h", "string.h"}, code, "Result: 10\n");
}

TEST_F(HeaderCompatibilityTest, MultiHeader_StdioStdlibMath) {
    const char* code = R"(
        int main() {
            double* values = (double*)malloc(sizeof(double) * 3);
            values[0] = 1.0;
            values[1] = 4.0;
            values[2] = 9.0;

            for (int i = 0; i < 3; i++) {
                printf("%.0f ", sqrt(values[i]));
            }
            printf("\n");

            free(values);
            return 0;
        }
    )";
    assertHeaderCombinationWorks({"stdio.h", "stdlib.h", "math.h"}, code, "1 2 3 \n", {"-lm"});
}

// ============================================================================
// Task 3: Custom Header Tests (3 tests)
// ============================================================================

TEST_F(HeaderCompatibilityTest, CustomHeader_SimpleStruct) {
    const char* header = R"(
#ifndef POINT_H
#define POINT_H

struct Point {
    int x;
    int y;
};

int distance_squared(struct Point* p);

#endif
)";

    const char* impl = R"(
#include "point.h"
#include <stdio.h>

int distance_squared(struct Point* p) {
    return p->x * p->x + p->y * p->y;
}

int main() {
    struct Point p = {3, 4};
    printf("%d\n", distance_squared(&p));
    return 0;
}
)";

    assertCustomHeaderWorks(header, "point.h", impl, "25\n");
}

TEST_F(HeaderCompatibilityTest, CustomHeader_FunctionDeclarations) {
    const char* header = R"(
#ifndef CALC_H
#define CALC_H

int add(int a, int b);
int multiply(int a, int b);

#endif
)";

    const char* impl = R"(
#include "calc.h"
#include <stdio.h>

int add(int a, int b) {
    return a + b;
}

int multiply(int a, int b) {
    return a * b;
}

int main() {
    printf("%d %d\n", add(2, 3), multiply(4, 5));
    return 0;
}
)";

    assertCustomHeaderWorks(header, "calc.h", impl, "5 20\n");
}

TEST_F(HeaderCompatibilityTest, CustomHeader_WithStdlibDependency) {
    const char* header = R"(
#ifndef GEOMETRY_H
#define GEOMETRY_H

#include <math.h>

struct Circle {
    double x;
    double y;
    double radius;
};

double circle_area(struct Circle* c);

#endif
)";

    const char* impl = R"(
#include "geometry.h"
#include <stdio.h>

double circle_area(struct Circle* c) {
    return 3.14159 * c->radius * c->radius;
}

int main() {
    struct Circle c = {0.0, 0.0, 2.0};
    printf("%.2f\n", circle_area(&c));
    return 0;
}
)";

    assertCustomHeaderWorks(header, "geometry.h", impl, "12.57\n", {"-lm"});
}
