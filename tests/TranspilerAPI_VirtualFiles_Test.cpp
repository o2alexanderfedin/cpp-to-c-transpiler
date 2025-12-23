// TDD GREEN Phase: Tests for TranspilerAPI Virtual File System support
// Phase 27-01: Core VFS Integration

#include <gtest/gtest.h>
#include <gmock/gmock.h>
#include "TranspilerAPI.h"

using namespace cpptoc;
using testing::HasSubstr;
using testing::Not;

// Test 1: Single Virtual Header File
TEST(TranspilerAPI_VFS, VirtualFileResolution_SingleHeader) {
    TranspileOptions opts;
    opts.virtualFiles = {
        {"/virtual/test.h", "#define MACRO 42\n"}
    };

    std::string cpp = R"(
        #include "/virtual/test.h"
        int x = MACRO;
    )";

    auto result = transpile(cpp, "test.cpp", opts);

    EXPECT_TRUE(result.success) << "Transpilation should succeed";
    EXPECT_THAT(result.c, HasSubstr("int x = 42")) << "MACRO should be expanded";
    EXPECT_THAT(result.c, Not(HasSubstr("MACRO"))) << "Macro name should not appear";
}

// Test 2: Multiple Virtual Headers
TEST(TranspilerAPI_VFS, VirtualFileResolution_MultipleHeaders) {
    TranspileOptions opts;
    opts.virtualFiles = {
        {"/virtual/a.h", "int foo();"},
        {"/virtual/b.h", "int bar();"}
    };

    std::string cpp = R"(
        #include "/virtual/a.h"
        #include "/virtual/b.h"
        int main() { return foo() + bar(); }
    )";

    auto result = transpile(cpp, "test.cpp", opts);

    EXPECT_TRUE(result.success) << "Transpilation should succeed";
    EXPECT_THAT(result.c, HasSubstr("foo")) << "Should have foo function";
    EXPECT_THAT(result.c, HasSubstr("bar")) << "Should have bar function";
}

// Test 3: Nested Includes
TEST(TranspilerAPI_VFS, VirtualFileResolution_NestedIncludes) {
    TranspileOptions opts;
    opts.virtualFiles = {
        {"/virtual/base.h", "#define VALUE 100"},
        {"/virtual/derived.h", "#include \"/virtual/base.h\"\n#define DOUBLE (VALUE * 2)"}
    };

    std::string cpp = R"(
        #include "/virtual/derived.h"
        int x = DOUBLE;
    )";

    auto result = transpile(cpp, "test.cpp", opts);

    EXPECT_TRUE(result.success) << "Nested includes should work";
    // Macro expansion happens during preprocessing, so we get the expression
    EXPECT_THAT(result.c, HasSubstr("int x = ")) << "Variable should be declared";
    EXPECT_THAT(result.c, HasSubstr("100")) << "Should contain base VALUE macro value";
}

// Test 4: Missing Virtual File (Error Handling)
TEST(TranspilerAPI_VFS, VirtualFileResolution_MissingFile) {
    TranspileOptions opts;
    // No virtual files provided

    std::string cpp = R"(
        #include "/virtual/missing.h"
        int x = 42;
    )";

    auto result = transpile(cpp, "test.cpp", opts);

    EXPECT_FALSE(result.success) << "Should fail with missing file";
    EXPECT_GT(result.diagnostics.size(), 0) << "Should have error diagnostics";
}

// Test 5: Empty Virtual Files List (Backward Compatibility)
TEST(TranspilerAPI_VFS, VirtualFileResolution_EmptyVirtualFiles) {
    TranspileOptions opts;
    opts.virtualFiles = {};  // Empty, no virtual files

    std::string cpp = "int add(int a, int b) { return a + b; }";

    auto result = transpile(cpp, "test.cpp", opts);

    EXPECT_TRUE(result.success) << "Should work with no virtual files";
    EXPECT_THAT(result.c, HasSubstr("int add")) << "Should transpile normally";
}

// Test 6: Virtual header with function definitions
TEST(TranspilerAPI_VFS, VirtualFileResolution_FunctionDefinitions) {
    TranspileOptions opts;
    opts.virtualFiles = {
        {"/virtual/math.h", R"(
            inline int square(int x) { return x * x; }
            inline int cube(int x) { return x * x * x; }
        )"}
    };

    std::string cpp = R"(
        #include "/virtual/math.h"
        int main() {
            return square(5) + cube(3);
        }
    )";

    auto result = transpile(cpp, "test.cpp", opts);

    EXPECT_TRUE(result.success) << "Virtual header with functions should work";
    EXPECT_THAT(result.c, HasSubstr("square")) << "Should have square function";
    EXPECT_THAT(result.c, HasSubstr("cube")) << "Should have cube function";
}

// Test 7: Virtual header with struct definitions
TEST(TranspilerAPI_VFS, VirtualFileResolution_StructDefinitions) {
    TranspileOptions opts;
    opts.virtualFiles = {
        {"/virtual/types.h", R"(
            struct Point {
                int x;
                int y;
            };
        )"}
    };

    std::string cpp = R"(
        #include "/virtual/types.h"
        int main() {
            Point p;
            p.x = 10;
            p.y = 20;
            return p.x + p.y;
        }
    )";

    auto result = transpile(cpp, "test.cpp", opts);

    EXPECT_TRUE(result.success) << "Virtual header with structs should work";
    EXPECT_THAT(result.c, HasSubstr("Point")) << "Should have Point struct";
}

// Test 8: Multiple includes of same virtual file
TEST(TranspilerAPI_VFS, VirtualFileResolution_MultipleIncludesOfSameFile) {
    TranspileOptions opts;
    opts.virtualFiles = {
        {"/virtual/common.h", R"(
            #ifndef COMMON_H
            #define COMMON_H
            #define CONSTANT 100
            #endif
        )"}
    };

    std::string cpp = R"(
        #include "/virtual/common.h"
        #include "/virtual/common.h"
        int x = CONSTANT;
    )";

    auto result = transpile(cpp, "test.cpp", opts);

    EXPECT_TRUE(result.success) << "Multiple includes of same file should work";
    EXPECT_THAT(result.c, HasSubstr("int x = 100")) << "CONSTANT should be expanded";
}
