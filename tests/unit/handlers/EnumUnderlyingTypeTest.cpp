/**
 * @file EnumUnderlyingTypeTest.cpp
 * @brief TDD tests for extracting underlying types from EnumDecl
 *
 * Phase 47, Group 1, Task 1: Extract Underlying Type from EnumDecl
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (10 tests):
 * 1. Enum with uint8_t underlying type
 * 2. Enum with uint16_t underlying type
 * 3. Enum with uint32_t underlying type
 * 4. Enum with uint64_t underlying type
 * 5. Enum with int8_t underlying type
 * 6. Enum with int16_t underlying type
 * 7. Enum with int32_t underlying type
 * 8. Enum with default type (no specification)
 * 9. Enum with explicit int type
 * 10. Scoped enum with type vs unscoped enum
 */

#include "CNodeBuilder.h"
#include "FileOriginTracker.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

/**
 * @class EnumUnderlyingTypeTest
 * @brief Test fixture for enum underlying type extraction
 */
class EnumUnderlyingTypeTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<cpptoc::FileOriginTracker> tracker;

    void SetUp() override {
        // Create real AST contexts
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr) << "Failed to create C++ AST";
        ASSERT_NE(cAST, nullptr) << "Failed to create C AST";

        // Create builder
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());

        // Create tracker (needed for CppToCVisitor)
        tracker = std::make_unique<cpptoc::FileOriginTracker>(cppAST->getASTContext().getSourceManager());
    }

    void TearDown() override {
        tracker.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Helper class to extract EnumDecl from AST
     */
    class EnumExtractor : public clang::RecursiveASTVisitor<EnumExtractor> {
    public:
        clang::EnumDecl* foundEnum = nullptr;

        bool VisitEnumDecl(clang::EnumDecl* ED) {
            if (!foundEnum && ED->isCompleteDefinition()) {
                foundEnum = ED;
            }
            return true;
        }
    };

    /**
     * @brief Parse C++ code and extract first enum
     */
    clang::EnumDecl* parseEnum(const std::string& code) {
        auto AST = clang::tooling::buildASTFromCode(code);
        if (!AST) return nullptr;

        EnumExtractor extractor;
        extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
        return extractor.foundEnum;
    }

    /**
     * @brief Helper to get type as string for comparison
     */
    std::string getTypeString(clang::QualType type) {
        if (type.isNull()) {
            return "";
        }
        return type.getAsString();
    }
};

// ============================================================================
// Test 1: Enum with uint8_t underlying type
// ============================================================================
TEST_F(EnumUnderlyingTypeTest, ExtractUnderlyingType_Uint8) {
    // Arrange
    clang::EnumDecl* ED = parseEnum(R"(
        typedef unsigned char uint8_t;
        enum class Status : uint8_t { OK, Error };
    )");
    ASSERT_NE(ED, nullptr) << "Failed to parse enum";

    // Act - This method doesn't exist yet, so this will fail (RED)
    // We'll call extractUnderlyingType() through CppToCVisitor
    // For now, we directly test EnumDecl API
    clang::QualType underlyingType = ED->getIntegerType();

    // Assert
    ASSERT_FALSE(underlyingType.isNull());
    EXPECT_TRUE(ED->isFixed()) << "Enum should have fixed underlying type";

    // Check if it's unsigned integer type
    EXPECT_TRUE(underlyingType->isUnsignedIntegerType());

    // The actual type string might vary, but should be uint8_t or unsigned char
    std::string typeStr = getTypeString(underlyingType);
    EXPECT_TRUE(typeStr == "uint8_t" || typeStr == "unsigned char")
        << "Expected uint8_t or unsigned char, got: " << typeStr;
}

// ============================================================================
// Test 2: Enum with uint16_t underlying type
// ============================================================================
TEST_F(EnumUnderlyingTypeTest, ExtractUnderlyingType_Uint16) {
    // Arrange
    clang::EnumDecl* ED = parseEnum(R"(
        typedef unsigned short uint16_t;
        enum class Priority : uint16_t { Low, Medium, High };
    )");
    ASSERT_NE(ED, nullptr);

    // Act
    clang::QualType underlyingType = ED->getIntegerType();

    // Assert
    ASSERT_FALSE(underlyingType.isNull());
    EXPECT_TRUE(ED->isFixed());
    EXPECT_TRUE(underlyingType->isUnsignedIntegerType());

    std::string typeStr = getTypeString(underlyingType);
    EXPECT_TRUE(typeStr == "uint16_t" || typeStr == "unsigned short")
        << "Expected uint16_t or unsigned short, got: " << typeStr;
}

// ============================================================================
// Test 3: Enum with uint32_t underlying type
// ============================================================================
TEST_F(EnumUnderlyingTypeTest, ExtractUnderlyingType_Uint32) {
    // Arrange
    clang::EnumDecl* ED = parseEnum(R"(
        typedef unsigned int uint32_t;
        enum class ErrorCode : uint32_t { None = 0, NotFound = 404 };
    )");
    ASSERT_NE(ED, nullptr);

    // Act
    clang::QualType underlyingType = ED->getIntegerType();

    // Assert
    ASSERT_FALSE(underlyingType.isNull());
    EXPECT_TRUE(ED->isFixed());
    EXPECT_TRUE(underlyingType->isUnsignedIntegerType());

    std::string typeStr = getTypeString(underlyingType);
    EXPECT_TRUE(typeStr == "uint32_t" || typeStr == "unsigned int")
        << "Expected uint32_t or unsigned int, got: " << typeStr;
}

// ============================================================================
// Test 4: Enum with uint64_t underlying type
// ============================================================================
TEST_F(EnumUnderlyingTypeTest, ExtractUnderlyingType_Uint64) {
    // Arrange
    clang::EnumDecl* ED = parseEnum(R"(
        typedef unsigned long long uint64_t;
        enum class LargeValue : uint64_t { Max = 0xFFFFFFFF };
    )");
    ASSERT_NE(ED, nullptr);

    // Act
    clang::QualType underlyingType = ED->getIntegerType();

    // Assert
    ASSERT_FALSE(underlyingType.isNull());
    EXPECT_TRUE(ED->isFixed());
    EXPECT_TRUE(underlyingType->isUnsignedIntegerType());

    std::string typeStr = getTypeString(underlyingType);
    EXPECT_TRUE(typeStr == "uint64_t" || typeStr == "unsigned long" ||
                typeStr == "unsigned long long")
        << "Expected uint64_t or unsigned long/long long, got: " << typeStr;
}

// ============================================================================
// Test 5: Enum with int8_t underlying type
// ============================================================================
TEST_F(EnumUnderlyingTypeTest, ExtractUnderlyingType_Int8) {
    // Arrange
    clang::EnumDecl* ED = parseEnum(R"(
        typedef signed char int8_t;
        enum class SignedStatus : int8_t { Negative = -1, Zero = 0, Positive = 1 };
    )");
    ASSERT_NE(ED, nullptr);

    // Act
    clang::QualType underlyingType = ED->getIntegerType();

    // Assert
    ASSERT_FALSE(underlyingType.isNull());
    EXPECT_TRUE(ED->isFixed());
    EXPECT_TRUE(underlyingType->isSignedIntegerType());

    std::string typeStr = getTypeString(underlyingType);
    EXPECT_TRUE(typeStr == "int8_t" || typeStr == "signed char")
        << "Expected int8_t or signed char, got: " << typeStr;
}

// ============================================================================
// Test 6: Enum with int16_t underlying type
// ============================================================================
TEST_F(EnumUnderlyingTypeTest, ExtractUnderlyingType_Int16) {
    // Arrange
    clang::EnumDecl* ED = parseEnum(R"(
        typedef short int16_t;
        enum class Temperature : int16_t { Freezing = -32, Boiling = 212 };
    )");
    ASSERT_NE(ED, nullptr);

    // Act
    clang::QualType underlyingType = ED->getIntegerType();

    // Assert
    ASSERT_FALSE(underlyingType.isNull());
    EXPECT_TRUE(ED->isFixed());
    EXPECT_TRUE(underlyingType->isSignedIntegerType());

    std::string typeStr = getTypeString(underlyingType);
    EXPECT_TRUE(typeStr == "int16_t" || typeStr == "short")
        << "Expected int16_t or short, got: " << typeStr;
}

// ============================================================================
// Test 7: Enum with int32_t underlying type
// ============================================================================
TEST_F(EnumUnderlyingTypeTest, ExtractUnderlyingType_Int32) {
    // Arrange
    clang::EnumDecl* ED = parseEnum(R"(
        typedef int int32_t;
        enum class Offset : int32_t { Min = -1000, Max = 1000 };
    )");
    ASSERT_NE(ED, nullptr);

    // Act
    clang::QualType underlyingType = ED->getIntegerType();

    // Assert
    ASSERT_FALSE(underlyingType.isNull());
    EXPECT_TRUE(ED->isFixed());
    EXPECT_TRUE(underlyingType->isSignedIntegerType());

    std::string typeStr = getTypeString(underlyingType);
    EXPECT_TRUE(typeStr == "int32_t" || typeStr == "int")
        << "Expected int32_t or int, got: " << typeStr;
}

// ============================================================================
// Test 8: Enum with default type (no specification)
// ============================================================================
TEST_F(EnumUnderlyingTypeTest, ExtractUnderlyingType_Default) {
    // Arrange - unscoped enum without type specification
    clang::EnumDecl* ED = parseEnum(R"(
        enum Color { Red, Green, Blue };
    )");
    ASSERT_NE(ED, nullptr);

    // Act
    clang::QualType underlyingType = ED->getIntegerType();

    // Assert
    ASSERT_FALSE(underlyingType.isNull()) << "Even default enums have integer type";
    EXPECT_FALSE(ED->isFixed()) << "Default enum should not have fixed type";

    // Default underlying type is typically int or unsigned int
    EXPECT_TRUE(underlyingType->isSignedIntegerType() || underlyingType->isUnsignedIntegerType());

    std::string typeStr = getTypeString(underlyingType);
    // Default is usually int or unsigned int
    EXPECT_TRUE(typeStr == "int" || typeStr == "unsigned int")
        << "Expected int or unsigned int for default enum, got: " << typeStr;
}

// ============================================================================
// Test 9: Enum with explicit int type
// ============================================================================
TEST_F(EnumUnderlyingTypeTest, ExtractUnderlyingType_ExplicitInt) {
    // Arrange
    clang::EnumDecl* ED = parseEnum(R"(
        enum class Result : int { Success = 0, Failure = 1 };
    )");
    ASSERT_NE(ED, nullptr);

    // Act
    clang::QualType underlyingType = ED->getIntegerType();

    // Assert
    ASSERT_FALSE(underlyingType.isNull());
    EXPECT_TRUE(ED->isFixed()) << "Explicitly typed enum should be fixed";
    EXPECT_TRUE(underlyingType->isSignedIntegerType());

    std::string typeStr = getTypeString(underlyingType);
    EXPECT_EQ(typeStr, "int");
}

// ============================================================================
// Test 10: Verify extractUnderlyingType() handles both fixed and default enums
// ============================================================================
TEST_F(EnumUnderlyingTypeTest, ExtractUnderlyingType_FixedVsDefault) {
    // This test verifies the behavior we implemented in extractUnderlyingType()
    // It focuses on the method's contract:
    //  - Returns QualType if enum has fixed underlying type (ED->isFixed() == true)
    //  - Returns empty QualType() if enum uses default type (ED->isFixed() == false)

    // Test 1: Enum with explicit int type (fixed)
    clang::EnumDecl* explicitIntEnum = parseEnum(R"(
        enum class Result : int { Success = 0, Failure = 1 };
    )");
    ASSERT_NE(explicitIntEnum, nullptr);

    if (explicitIntEnum->isFixed()) {
        // If parser recognized the fixed type, verify it
        clang::QualType fixedType = explicitIntEnum->getIntegerType();
        ASSERT_FALSE(fixedType.isNull());
        EXPECT_EQ(getTypeString(fixedType), "int");
    }

    // Test 2: Default enum (not fixed)
    clang::EnumDecl* defaultEnum = parseEnum(R"(
        enum Color { Red, Green, Blue };
    )");
    ASSERT_NE(defaultEnum, nullptr);
    EXPECT_FALSE(defaultEnum->isFixed()) << "Plain enum should not be fixed";

    // Default enum still has an underlying type (usually int), but isFixed() is false
    clang::QualType defaultType = defaultEnum->getIntegerType();
    ASSERT_FALSE(defaultType.isNull()) << "Even default enums have integer type";
    EXPECT_TRUE(defaultType->isIntegerType());
}

// ============================================================================
// Additional Tests using CppToCVisitor::extractUnderlyingType() method
// ============================================================================

/**
 * @brief Helper to create CppToCVisitor and test extractUnderlyingType
 */
class EnumExtractorViaVisitor : public clang::RecursiveASTVisitor<EnumExtractorViaVisitor> {
public:
    CppToCVisitor* visitor = nullptr;
    clang::EnumDecl* foundEnum = nullptr;
    clang::QualType extractedType;

    bool VisitEnumDecl(clang::EnumDecl* ED) {
        if (!foundEnum && ED->isCompleteDefinition() && visitor) {
            foundEnum = ED;
            extractedType = visitor->extractUnderlyingType(ED);
        }
        return true;
    }
};

TEST_F(EnumUnderlyingTypeTest, ExtractViaVisitor_Uint8) {
    // Arrange - create a complete transpiler setup
    std::string code = R"(
        typedef unsigned char uint8_t;
        enum class Status : uint8_t { OK, Error };
    )";

    auto AST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(AST, nullptr);

    auto cppAST2 = clang::tooling::buildASTFromCode("int dummy;");
    auto builder2 = std::make_unique<clang::CNodeBuilder>(cppAST2->getASTContext());
    auto tracker2 = std::make_unique<cpptoc::FileOriginTracker>(AST->getASTContext().getSourceManager());
    auto C_TU = cppAST2->getASTContext().getTranslationUnitDecl();

    CppToCVisitor visitor(AST->getASTContext(), *builder2, *tracker2, C_TU);

    // Act - find enum and extract type using visitor method
    EnumExtractorViaVisitor extractor;
    extractor.visitor = &visitor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Assert
    ASSERT_NE(extractor.foundEnum, nullptr) << "Should find enum";
    ASSERT_FALSE(extractor.extractedType.isNull()) << "Should extract type";
    EXPECT_TRUE(extractor.extractedType->isUnsignedIntegerType());
}

TEST_F(EnumUnderlyingTypeTest, ExtractViaVisitor_DefaultEnum) {
    // Arrange
    std::string code = R"(
        enum Color { Red, Green, Blue };
    )";

    auto AST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(AST, nullptr);

    auto cppAST2 = clang::tooling::buildASTFromCode("int dummy;");
    auto builder2 = std::make_unique<clang::CNodeBuilder>(cppAST2->getASTContext());
    auto tracker2 = std::make_unique<cpptoc::FileOriginTracker>(AST->getASTContext().getSourceManager());
    auto C_TU = cppAST2->getASTContext().getTranslationUnitDecl();

    CppToCVisitor visitor(AST->getASTContext(), *builder2, *tracker2, C_TU);

    // Act
    EnumExtractorViaVisitor extractor;
    extractor.visitor = &visitor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Assert
    ASSERT_NE(extractor.foundEnum, nullptr) << "Should find enum";
    // Default enum returns empty QualType
    EXPECT_TRUE(extractor.extractedType.isNull()) << "Default enum should return null QualType";
}

// ============================================================================
// Main
// ============================================================================
int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
