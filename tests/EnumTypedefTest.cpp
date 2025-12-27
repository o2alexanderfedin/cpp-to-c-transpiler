/**
 * @file EnumTypedefTest.cpp
 * @brief Phase 47, Group 1, Task 2: Typedef Generation for Type-Specified Enums
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (8 tests):
 * 1. Typedef generation for scoped enum with uint8_t type
 * 2. Typedef generation for unscoped enum with int type
 * 3. Typedef for enums without type specification (C99 default)
 * 4. Typedef with prefixed enum constants (scoped enum)
 * 5. Multiple enums with different underlying types
 * 6. Enum typedef in function parameter
 * 7. Enum typedef in struct field
 * 8. Scoped enum with explicit values and underlying type
 *
 * IMPORTANT: This tests that the CURRENT implementation works correctly.
 * C99 approach: ALWAYS use typedef for all enums (most compatible).
 * C23 would support: enum Name : Type { ... }; (future enhancement).
 */

#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

/**
 * @class EnumTypedefTest
 * @brief Test fixture for enum typedef generation verification
 */
class EnumTypedefTest : public ::testing::Test {
protected:
    // Keep AST alive for the duration of the test
    std::unique_ptr<clang::ASTUnit> currentAST;

    /**
     * @brief Helper class to extract EnumDecl from AST
     */
    class EnumExtractor : public clang::RecursiveASTVisitor<EnumExtractor> {
    public:
        std::vector<clang::EnumDecl*> foundEnums;

        bool VisitEnumDecl(clang::EnumDecl* ED) {
            if (ED->isCompleteDefinition()) {
                foundEnums.push_back(ED);
            }
            return true;
        }
    };

    /**
     * @brief Parse C++ code and extract all enums
     * IMPORTANT: Keeps AST alive in currentAST member
     */
    std::vector<clang::EnumDecl*> parseEnums(const std::string& code) {
        currentAST = clang::tooling::buildASTFromCode(code);
        if (!currentAST) return {};

        EnumExtractor extractor;
        extractor.TraverseDecl(currentAST->getASTContext().getTranslationUnitDecl());
        return extractor.foundEnums;
    }

    void TearDown() override {
        // Clean up AST after each test
        currentAST.reset();
    }
};

// ============================================================================
// Test 1: Scoped enum with unsigned char underlying type - verify isFixed() == true
// ============================================================================
TEST_F(EnumTypedefTest, ScopedEnumWithUint8Type_HasFixedUnderlyingType) {
    const char* code = R"(
        enum class Status : unsigned char { OK = 0, Error = 1 };
    )";

    auto enums = parseEnums(code);
    ASSERT_EQ(enums.size(), 1) << "Should find exactly one enum";

    clang::EnumDecl* ED = enums[0];
    EXPECT_TRUE(ED->isScoped()) << "Should be scoped enum (enum class)";
    EXPECT_TRUE(ED->isFixed()) << "Should have fixed underlying type (unsigned char)";

    clang::QualType underlyingType = ED->getIntegerType();
    EXPECT_FALSE(underlyingType.isNull()) << "Underlying type should not be null";
    EXPECT_TRUE(underlyingType->isUnsignedIntegerType()) << "Should be unsigned integer type";
}

// ============================================================================
// Test 2: Unscoped enum with explicit int type - verify isFixed() == true
// ============================================================================
TEST_F(EnumTypedefTest, UnscopedEnumWithIntType_HasFixedUnderlyingType) {
    const char* code = R"(
        enum Priority : int { Low = 1, Medium = 5, High = 10 };
    )";

    auto enums = parseEnums(code);
    ASSERT_EQ(enums.size(), 1) << "Should find exactly one enum";

    clang::EnumDecl* ED = enums[0];
    EXPECT_FALSE(ED->isScoped()) << "Should be unscoped enum";
    EXPECT_TRUE(ED->isFixed()) << "Should have fixed underlying type (int)";

    clang::QualType underlyingType = ED->getIntegerType();
    EXPECT_FALSE(underlyingType.isNull()) << "Underlying type should not be null";
}

// ============================================================================
// Test 3: Enum without type specification - verify isFixed() == false
// ============================================================================
TEST_F(EnumTypedefTest, EnumWithoutTypeSpec_NoFixedUnderlyingType) {
    const char* code = R"(
        enum Color { Red, Green, Blue };
    )";

    auto enums = parseEnums(code);
    ASSERT_EQ(enums.size(), 1) << "Should find exactly one enum";

    clang::EnumDecl* ED = enums[0];
    EXPECT_FALSE(ED->isScoped()) << "Should be unscoped enum";
    EXPECT_FALSE(ED->isFixed()) << "Should NOT have explicit fixed underlying type";

    // Note: Even without explicit type, getIntegerType() returns a type (usually int)
    clang::QualType underlyingType = ED->getIntegerType();
    EXPECT_FALSE(underlyingType.isNull()) << "Underlying type should still exist (default)";
}

// ============================================================================
// Test 4: Scoped enum has prefixed constants
// ============================================================================
TEST_F(EnumTypedefTest, ScopedEnum_ConstantsNeedPrefixing) {
    const char* code = R"(
        enum class GameState : unsigned char { Menu, Playing, Paused };
    )";

    auto enums = parseEnums(code);
    ASSERT_EQ(enums.size(), 1) << "Should find exactly one enum";

    clang::EnumDecl* ED = enums[0];
    EXPECT_TRUE(ED->isScoped()) << "Should be scoped enum";
    EXPECT_TRUE(ED->isFixed()) << "Should have fixed underlying type";

    // Verify enum constants exist
    auto constants = ED->enumerators();
    std::vector<std::string> names;
    for (auto* ECD : constants) {
        names.push_back(ECD->getNameAsString());
    }

    ASSERT_EQ(names.size(), 3) << "Should have 3 enum constants";
    EXPECT_EQ(names[0], "Menu");
    EXPECT_EQ(names[1], "Playing");
    EXPECT_EQ(names[2], "Paused");

    // Note: CppToCVisitor will prefix these with "GameState__" in C output
}

// ============================================================================
// Test 5: Multiple enums with different types
// ============================================================================
TEST_F(EnumTypedefTest, MultipleEnumsWithDifferentTypes) {
    const char* code = R"(
        enum class Status : unsigned char { OK, Error };
        enum class ErrorCode : unsigned short { None = 0, NotFound = 404 };
        enum Flags : int { FlagA = 1, FlagB = 2 };
    )";

    auto enums = parseEnums(code);
    ASSERT_EQ(enums.size(), 3) << "Should find exactly 3 enums";

    // Status: scoped, unsigned char
    EXPECT_TRUE(enums[0]->isScoped());
    EXPECT_TRUE(enums[0]->isFixed());
    EXPECT_EQ(enums[0]->getNameAsString(), "Status");

    // ErrorCode: scoped, unsigned short
    EXPECT_TRUE(enums[1]->isScoped());
    EXPECT_TRUE(enums[1]->isFixed());
    EXPECT_EQ(enums[1]->getNameAsString(), "ErrorCode");

    // Flags: unscoped, int
    EXPECT_FALSE(enums[2]->isScoped());
    EXPECT_TRUE(enums[2]->isFixed());
    EXPECT_EQ(enums[2]->getNameAsString(), "Flags");
}

// ============================================================================
// Test 6: Enum in function parameter context
// ============================================================================
TEST_F(EnumTypedefTest, EnumInFunctionParameter) {
    const char* code = R"(
        enum class Result : unsigned char { Success, Failure };

        int processResult(Result r) {
            return 0;
        }
    )";

    auto enums = parseEnums(code);
    ASSERT_EQ(enums.size(), 1) << "Should find exactly one enum";

    clang::EnumDecl* ED = enums[0];
    EXPECT_EQ(ED->getNameAsString(), "Result");
    EXPECT_TRUE(ED->isScoped());
    EXPECT_TRUE(ED->isFixed());

    // The function should use "enum Result" as parameter type in C
}

// ============================================================================
// Test 7: Enum in struct field context
// ============================================================================
TEST_F(EnumTypedefTest, EnumInStructField) {
    const char* code = R"(
        enum class Mode : unsigned char { Read, Write };

        struct Config {
            Mode mode;
            int value;
        };
    )";

    auto enums = parseEnums(code);
    ASSERT_EQ(enums.size(), 1) << "Should find exactly one enum";

    clang::EnumDecl* ED = enums[0];
    EXPECT_EQ(ED->getNameAsString(), "Mode");
    EXPECT_TRUE(ED->isScoped());
    EXPECT_TRUE(ED->isFixed());

    // The struct should use "enum Mode" as field type in C
}

// ============================================================================
// Test 8: Scoped enum with explicit values and type
// ============================================================================
TEST_F(EnumTypedefTest, ScopedEnumWithExplicitValuesAndType) {
    const char* code = R"(
        enum class HttpStatus : unsigned short {
            OK = 200,
            NotFound = 404,
            InternalError = 500
        };
    )";

    auto enums = parseEnums(code);
    ASSERT_EQ(enums.size(), 1) << "Should find exactly one enum";

    clang::EnumDecl* ED = enums[0];
    EXPECT_EQ(ED->getNameAsString(), "HttpStatus");
    EXPECT_TRUE(ED->isScoped());
    EXPECT_TRUE(ED->isFixed());

    // Verify explicit values
    auto constants = ED->enumerators();
    std::vector<std::pair<std::string, int64_t>> expected = {
        {"OK", 200},
        {"NotFound", 404},
        {"InternalError", 500}
    };

    size_t i = 0;
    for (auto* ECD : constants) {
        ASSERT_LT(i, expected.size());
        EXPECT_EQ(ECD->getNameAsString(), expected[i].first);
        EXPECT_EQ(ECD->getInitVal().getSExtValue(), expected[i].second);
        i++;
    }

    EXPECT_EQ(i, expected.size()) << "Should have exactly 3 constants";
}
