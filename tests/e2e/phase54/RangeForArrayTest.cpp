/**
 * @file RangeForArrayTest.cpp
 * @brief E2E tests for Phase 54: Range-based for loops (Array support)
 *
 * Tests array-based range-for loop translation.
 */

#include <gtest/gtest.h>
#include "CppToCVisitor.h"
#include "CodeGenerator.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include <memory>

namespace cpptoc {
namespace test {

class RangeForArrayTest : public ::testing::Test {
protected:
    /**
     * @brief Transpile C++ code to C
     */
    std::string transpile(const std::string& cppCode) {
        // Create AST from C++ code
        std::unique_ptr<clang::ASTUnit> cppAST = clang::tooling::buildASTFromCode(cppCode);
        if (!cppAST) {
            return "ERROR: Failed to parse C++ code";
        }

        // Create C AST context (we'll reuse C++ context for simplicity in tests)
        // In real implementation, C_TU would be separate
        clang::ASTContext& cppContext = cppAST->getASTContext();
        clang::TranslationUnitDecl* cppTU = cppContext.getTranslationUnitDecl();

        // Create visitor and translate
        CppToCVisitor visitor(cppContext);
        visitor.TraverseDecl(cppTU);

        // Generate C code
        clang::TranslationUnitDecl* cTU = visitor.getC_TU();
        CodeGenerator generator(cppContext);

        std::string headerCode;
        std::string implCode;
        generator.generate(cTU, headerCode, implCode);

        return implCode;
    }
};

/**
 * Test 1: Simple array iteration (by-value)
 */
TEST_F(RangeForArrayTest, SimpleArrayByValue) {
    std::string cppCode = R"(
        void test() {
            int arr[3] = {1, 2, 3};
            for (int x : arr) {
                x = x + 1;
            }
        }
    )";

    std::string cCode = transpile(cppCode);

    // Verify generated code contains:
    // - Index variable declaration (size_t __range_i_N = 0)
    // - Loop condition (__range_i_N < 3)
    // - Loop increment (++__range_i_N)
    // - Element variable (int x = arr[__range_i_N])

    EXPECT_NE(cCode.find("size_t __range_i_"), std::string::npos)
        << "Should generate index variable";
    EXPECT_NE(cCode.find("< 3"), std::string::npos)
        << "Should use array size in condition";
    EXPECT_NE(cCode.find("++__range_i_"), std::string::npos)
        << "Should increment index variable";
    EXPECT_NE(cCode.find("int x = arr[__range_i_"), std::string::npos)
        << "Should create element variable with array subscript";
}

/**
 * Test 2: Array iteration with different types
 */
TEST_F(RangeForArrayTest, ArrayWithDifferentTypes) {
    std::string cppCode = R"(
        void test() {
            double values[5] = {1.0, 2.0, 3.0, 4.0, 5.0};
            for (double v : values) {
                v = v * 2.0;
            }
        }
    )";

    std::string cCode = transpile(cppCode);

    EXPECT_NE(cCode.find("size_t __range_i_"), std::string::npos);
    EXPECT_NE(cCode.find("< 5"), std::string::npos);
    EXPECT_NE(cCode.find("double v = values[__range_i_"), std::string::npos);
}

/**
 * Test 3: Nested array loops
 */
TEST_F(RangeForArrayTest, NestedArrayLoops) {
    std::string cppCode = R"(
        void test() {
            int outer[2] = {1, 2};
            int inner[2] = {3, 4};
            for (int x : outer) {
                for (int y : inner) {
                    int sum = x + y;
                }
            }
        }
    )";

    std::string cCode = transpile(cppCode);

    // Should have two different index variables
    EXPECT_NE(cCode.find("__range_i_"), std::string::npos);

    // Both loops should be translated
    EXPECT_NE(cCode.find("int x = outer[__range_i_"), std::string::npos);
    EXPECT_NE(cCode.find("int y = inner[__range_i_"), std::string::npos);
}

} // namespace test
} // namespace cpptoc
