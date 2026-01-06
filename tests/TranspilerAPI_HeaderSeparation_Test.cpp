// tests/TranspilerAPI_HeaderSeparation_Test.cpp
// Phase 28: Header/Implementation File Separation Tests
// Tests that .h and .c files are generated with proper separation

#include <gtest/gtest.h>
#include <gmock/gmock.h>
#include "../include/TranspilerAPI.h"

using ::testing::HasSubstr;
using ::testing::Not;

// Test fixture for header/implementation separation tests
class TranspilerAPI_HeaderSeparation : public ::testing::Test {
protected:
    cpptoc::TranspileOptions options;

    void SetUp() override {
        // Use default options for most tests
        options = cpptoc::TranspileOptions();
    }
};

// Test 1: Simple Function - Header/Impl Split
TEST_F(TranspilerAPI_HeaderSeparation, SimpleFunctionSplit) {
    std::string cpp = R"(
        int add(int a, int b) {
            return a + b;
        }
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success);

    // Check .h file
    EXPECT_THAT(result.h, HasSubstr("#ifndef TEST_CPP_H"));
    EXPECT_THAT(result.h, HasSubstr("#define TEST_CPP_H"));
    EXPECT_THAT(result.h, HasSubstr("int add(int a, int b);"));
    EXPECT_THAT(result.h, Not(HasSubstr("return a + b")));  // No body in header
    EXPECT_THAT(result.h, HasSubstr("#endif // TEST_CPP_H"));

    // Check .c file
    EXPECT_THAT(result.c, HasSubstr("#include \"test.cpp.h\""));
    EXPECT_THAT(result.c, HasSubstr("int add(int a, int b)"));
    EXPECT_THAT(result.c, HasSubstr("return a + b"));  // Body in implementation
}

// Test 2: Struct Definition in Header
TEST_F(TranspilerAPI_HeaderSeparation, StructInHeader) {
    std::string cpp = R"(
        struct Point {
            int x;
            int y;
        };

        int getX(struct Point p) {
            return p.x;
        }
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success);

    // Struct in header
    EXPECT_THAT(result.h, HasSubstr("struct Point {"));
    EXPECT_THAT(result.h, HasSubstr("int x;"));
    EXPECT_THAT(result.h, HasSubstr("int y;"));

    // Function signature in header
    EXPECT_THAT(result.h, HasSubstr("int getX(struct Point p);"));

    // Function body in .c
    EXPECT_THAT(result.c, HasSubstr("return p.x"));
}

// Test 3: Forward Declarations
TEST_F(TranspilerAPI_HeaderSeparation, ForwardDeclarations) {
    std::string cpp = R"(
        struct Node {
            int data;
            struct Node* next;
        };
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success);

    // Forward declaration in header
    EXPECT_THAT(result.h, HasSubstr("struct Node;"));

    // Full definition after forward decl
    EXPECT_THAT(result.h, HasSubstr("struct Node {"));
}

// Test 4: Pragma Once Mode
TEST_F(TranspilerAPI_HeaderSeparation, PragmaOnceMode) {
    cpptoc::TranspileOptions opts;
    opts.usePragmaOnce = true;

    std::string cpp = "int foo() { return 42; }";

    auto result = cpptoc::transpile(cpp, "test.cpp", opts);

    EXPECT_TRUE(result.success);

    // Should use #pragma once instead of guards
    EXPECT_THAT(result.h, HasSubstr("#pragma once"));
    EXPECT_THAT(result.h, Not(HasSubstr("#ifndef")));
    EXPECT_THAT(result.h, Not(HasSubstr("#define")));
}

// Test 5: Header Only Declarations
TEST_F(TranspilerAPI_HeaderSeparation, HeaderOnlyDeclarations) {
    std::string cpp = R"(
        int foo();
        int bar();
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success);

    // Declarations in header
    EXPECT_THAT(result.h, HasSubstr("int foo();"));
    EXPECT_THAT(result.h, HasSubstr("int bar();"));

    // .c file should be minimal (just #include)
    EXPECT_THAT(result.c, HasSubstr("#include \"test.cpp.h\""));
}

// Test 6: Multiple Functions
TEST_F(TranspilerAPI_HeaderSeparation, MultipleFunctions) {
    std::string cpp = R"(
        int add(int a, int b) {
            return a + b;
        }

        int subtract(int a, int b) {
            return a - b;
        }

        int multiply(int a, int b) {
            return a * b;
        }
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success);

    // All function signatures in header
    EXPECT_THAT(result.h, HasSubstr("int add(int a, int b);"));
    EXPECT_THAT(result.h, HasSubstr("int subtract(int a, int b);"));
    EXPECT_THAT(result.h, HasSubstr("int multiply(int a, int b);"));

    // All function bodies in implementation
    EXPECT_THAT(result.c, HasSubstr("return a + b"));
    EXPECT_THAT(result.c, HasSubstr("return a - b"));
    EXPECT_THAT(result.c, HasSubstr("return a * b"));
}

// Test 7: Struct with Functions
TEST_F(TranspilerAPI_HeaderSeparation, StructWithFunctions) {
    std::string cpp = R"(
        struct Rectangle {
            int width;
            int height;
        };

        int area(struct Rectangle r) {
            return r.width * r.height;
        }

        int perimeter(struct Rectangle r) {
            return 2 * (r.width + r.height);
        }
    )";

    auto result = cpptoc::transpile(cpp, "test.cpp", options);

    EXPECT_TRUE(result.success);

    // Struct definition in header
    EXPECT_THAT(result.h, HasSubstr("struct Rectangle {"));
    EXPECT_THAT(result.h, HasSubstr("int width;"));
    EXPECT_THAT(result.h, HasSubstr("int height;"));

    // Function signatures in header
    EXPECT_THAT(result.h, HasSubstr("int area(struct Rectangle r);"));
    EXPECT_THAT(result.h, HasSubstr("int perimeter(struct Rectangle r);"));

    // Function bodies in implementation
    EXPECT_THAT(result.c, HasSubstr("return r.width * r.height"));
    EXPECT_THAT(result.c, HasSubstr("return 2 * (r.width + r.height)"));
}

// Test 8: Include Guard Format
TEST_F(TranspilerAPI_HeaderSeparation, IncludeGuardFormat) {
    std::string cpp = "void test() {}";

    auto result = cpptoc::transpile(cpp, "my-file.cpp", options);

    EXPECT_TRUE(result.success);

    // Check guard naming convention (filename converted to uppercase with underscores)
    EXPECT_THAT(result.h, HasSubstr("#ifndef MY_FILE_CPP_H"));
    EXPECT_THAT(result.h, HasSubstr("#define MY_FILE_CPP_H"));
    EXPECT_THAT(result.h, HasSubstr("#endif // MY_FILE_CPP_H"));
}
