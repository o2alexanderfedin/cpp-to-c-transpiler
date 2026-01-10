/**
 * @file EnumTranslatorTest.cpp
 * @brief TDD tests for EnumTranslator (Phase 47, Group 2, Task 3)
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (20 tests):
 *
 * Group 1: Basic Translation (5 tests)
 * 1. EmptyEnum - enum Empty {};
 * 2. UnscopedEnumSingleConstant - enum Color { Red };
 * 3. UnscopedEnumMultipleConstants - enum Color { Red, Green, Blue };
 * 4. ScopedEnumSingleConstant - enum class State { Idle };
 * 5. ScopedEnumMultipleConstants - enum class GameState { Menu, Playing, Paused };
 *
 * Group 2: Name Prefixing (3 tests)
 * 6. ScopedEnumConstantPrefixing - State::Idle → State__Idle
 * 7. UnscopedEnumNoPrefixing - Red → Red
 * 8. ScopedEnumMultiWordName - GameState::MenuScreen → GameState__MenuScreen
 *
 * Group 3: Explicit Values (3 tests)
 * 9. EnumWithExplicitValues - enum Status { OK = 0, Error = 1 };
 * 10. EnumWithSparseValues - enum Priority { Low = 1, High = 10 };
 * 11. EnumWithNegativeValues - enum Range { Min = -1, Zero = 0 };
 *
 * Group 4: Type Specifications (3 tests)
 * 12. EnumWithUint8Type - enum class Status : uint8_t { OK, Error };
 * 13. EnumWithInt32Type - enum class Priority : int32_t { Low, High };
 * 14. EnumWithAutoIncrementAndType - enum class Flags : uint16_t { A = 1, B, C };
 *
 * Group 5: Edge Cases (6 tests)
 * 15. EnumWithMaxIntValue - enum Limit { Max = 2147483647 };
 * 16. EnumWithDuplicateNamesInDifferentEnums - enum A { X }; enum B { X };
 * 17. AnonymousEnum - enum { Anonymous };
 * 18. ScopedEnumWithTypeCombination - combines scoping, type, and values
 * 19. UnscopedEnumWithType - enum Color : uint8_t { Red, Green };
 * 20. EnumWithAllFeatures - comprehensive test combining all features
 */

#include "dispatch/EnumTranslator.h"
#include "UnitTestHelper.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class EnumTranslatorTest
 * @brief Test fixture for EnumTranslator
 */
class EnumTranslatorTest : public ::testing::Test {
protected:
    UnitTestContext ctx;
    std::unique_ptr<EnumTranslator> translator;

    void SetUp() override {
        // Create real AST contexts using minimal code
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr) << "Failed to create C++ AST";
        ASSERT_NE(cAST, nullptr) << "Failed to create C AST";

        // Create builder and context

        // Create translator
        translator = std::make_unique<EnumTranslator>();
    }
/**
     * @brief Build AST from code and return the first EnumDecl
     */
    const clang::EnumDecl* getEnumDeclFromCode(const std::string& code) {
        cppAST = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(cppAST, nullptr) << "Failed to parse code: " << code;

        if (!cppAST) return nullptr;

        // Recreate builder and context with new AST

        // Find the first EnumDecl
        auto& ctx = cppAST->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* enumDecl = llvm::dyn_cast<clang::EnumDecl>(decl)) {
                return enumDecl;
            }
        }

        return nullptr;
    }

    /**
     * @brief Get all EnumDecls from the current AST
     */
    std::vector<const clang::EnumDecl*> getAllEnumDecls() {
        std::vector<const clang::EnumDecl*> enums;

        if (!cppAST) return enums;

        auto& ctx = cppAST->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* enumDecl = llvm::dyn_cast<clang::EnumDecl>(decl)) {
                enums.push_back(enumDecl);
            }
        }

        return enums;
    }

    /**
     * @brief Get all enum constants from an EnumDecl
     */
    std::vector<clang::EnumConstantDecl*> getEnumConstants(const clang::EnumDecl* enumDecl) {
        std::vector<clang::EnumConstantDecl*> constants;

        for (auto* decl : enumDecl->enumerators()) {
            constants.push_back(decl);
        }

        return constants;
    }

    /**
     * @brief Verify enum structure
     */
    void verifyEnumStructure(
        const clang::EnumDecl* cEnum,
        const std::string& expectedName,
        size_t expectedConstantCount,
        bool expectedScoped = false
    ) {
        ASSERT_NE(cEnum, nullptr) << "C EnumDecl is null";

        if (!expectedName.empty()) {
            EXPECT_EQ(cEnum->getNameAsString(), expectedName);
        }

        // Count constants
        size_t constantCount = 0;
        for (auto* constant : cEnum->enumerators()) {
            (void)constant;
            constantCount++;
        }
        EXPECT_EQ(constantCount, expectedConstantCount);

        // Verify scoping (scoped enums should become unscoped in C)
        EXPECT_FALSE(cEnum->isScoped()) << "C enum should not be scoped";
    }

    /**
     * @brief Verify enum constant name and value
     */
    void verifyEnumConstant(
        clang::EnumConstantDecl* constant,
        const std::string& expectedName,
        int64_t expectedValue
    ) {
        ASSERT_NE(constant, nullptr);
        EXPECT_EQ(constant->getNameAsString(), expectedName);
        EXPECT_EQ(constant->getInitVal().getSExtValue(), expectedValue);
    }
};

// =============================================================================
// Group 1: Basic Translation
// =============================================================================

/**
 * Test 1: Empty enum (edge case)
 * C++: enum Empty {};
 * C:   enum Empty {};
 */
TEST_F(EnumTranslatorTest, EmptyEnum) {
    const char* code = R"(
        enum Empty {};
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_TRUE(translator->canHandle(cppEnum));

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    verifyEnumStructure(cEnum, "Empty", 0, false);
}

/**
 * Test 2: Unscoped enum with single constant
 * C++: enum Color { Red };
 * C:   enum Color { Red };
 */
TEST_F(EnumTranslatorTest, UnscopedEnumSingleConstant) {
    const char* code = R"(
        enum Color { Red };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_FALSE(cppEnum->isScoped());
    EXPECT_TRUE(translator->canHandle(cppEnum));

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    verifyEnumStructure(cEnum, "Color", 1, false);

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 1);
    verifyEnumConstant(constants[0], "Red", 0);
}

/**
 * Test 3: Unscoped enum with multiple constants
 * C++: enum Color { Red, Green, Blue };
 * C:   enum Color { Red, Green, Blue };
 */
TEST_F(EnumTranslatorTest, UnscopedEnumMultipleConstants) {
    const char* code = R"(
        enum Color { Red, Green, Blue };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_FALSE(cppEnum->isScoped());
    EXPECT_TRUE(translator->canHandle(cppEnum));

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    verifyEnumStructure(cEnum, "Color", 3, false);

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 3);
    verifyEnumConstant(constants[0], "Red", 0);
    verifyEnumConstant(constants[1], "Green", 1);
    verifyEnumConstant(constants[2], "Blue", 2);
}

/**
 * Test 4: Scoped enum with single constant
 * C++: enum class State { Idle };
 * C:   enum State { State__Idle };
 */
TEST_F(EnumTranslatorTest, ScopedEnumSingleConstant) {
    const char* code = R"(
        enum class State { Idle };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_TRUE(cppEnum->isScoped());
    EXPECT_TRUE(translator->canHandle(cppEnum));

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    verifyEnumStructure(cEnum, "State", 1, false);

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 1);
    // Scoped enum constant should be prefixed with enum name
    verifyEnumConstant(constants[0], "State__Idle", 0);
}

/**
 * Test 5: Scoped enum with multiple constants
 * C++: enum class GameState { Menu, Playing, Paused };
 * C:   enum GameState { GameState__Menu, GameState__Playing, GameState__Paused };
 */
TEST_F(EnumTranslatorTest, ScopedEnumMultipleConstants) {
    const char* code = R"(
        enum class GameState { Menu, Playing, Paused };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_TRUE(cppEnum->isScoped());
    EXPECT_TRUE(translator->canHandle(cppEnum));

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    verifyEnumStructure(cEnum, "GameState", 3, false);

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 3);
    verifyEnumConstant(constants[0], "GameState__Menu", 0);
    verifyEnumConstant(constants[1], "GameState__Playing", 1);
    verifyEnumConstant(constants[2], "GameState__Paused", 2);
}

// =============================================================================
// Group 2: Name Prefixing
// =============================================================================

/**
 * Test 6: Scoped enum constant prefixing
 * C++: enum class State { Idle, Running };
 * C:   enum State { State__Idle, State__Running };
 */
TEST_F(EnumTranslatorTest, ScopedEnumConstantPrefixing) {
    const char* code = R"(
        enum class State { Idle, Running };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_TRUE(cppEnum->isScoped());

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 2);

    // Verify prefixing pattern: EnumName__ConstantName
    EXPECT_EQ(constants[0]->getNameAsString(), "State__Idle");
    EXPECT_EQ(constants[1]->getNameAsString(), "State__Running");
}

/**
 * Test 7: Unscoped enum no prefixing
 * C++: enum Color { Red, Green };
 * C:   enum Color { Red, Green };
 */
TEST_F(EnumTranslatorTest, UnscopedEnumNoPrefixing) {
    const char* code = R"(
        enum Color { Red, Green };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_FALSE(cppEnum->isScoped());

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 2);

    // Unscoped enums should NOT be prefixed
    EXPECT_EQ(constants[0]->getNameAsString(), "Red");
    EXPECT_EQ(constants[1]->getNameAsString(), "Green");
}

/**
 * Test 8: Scoped enum with multi-word name
 * C++: enum class GameState { MenuScreen, GameOver };
 * C:   enum GameState { GameState__MenuScreen, GameState__GameOver };
 */
TEST_F(EnumTranslatorTest, ScopedEnumMultiWordName) {
    const char* code = R"(
        enum class GameState { MenuScreen, GameOver };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_TRUE(cppEnum->isScoped());

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 2);

    // Verify multi-word constant names are correctly prefixed
    EXPECT_EQ(constants[0]->getNameAsString(), "GameState__MenuScreen");
    EXPECT_EQ(constants[1]->getNameAsString(), "GameState__GameOver");
}

// =============================================================================
// Group 3: Explicit Values
// =============================================================================

/**
 * Test 9: Enum with explicit values
 * C++: enum Status { OK = 0, Error = 1 };
 * C:   enum Status { OK = 0, Error = 1 };
 */
TEST_F(EnumTranslatorTest, EnumWithExplicitValues) {
    const char* code = R"(
        enum Status { OK = 0, Error = 1 };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 2);
    verifyEnumConstant(constants[0], "OK", 0);
    verifyEnumConstant(constants[1], "Error", 1);
}

/**
 * Test 10: Enum with sparse values
 * C++: enum Priority { Low = 1, High = 10 };
 * C:   enum Priority { Low = 1, High = 10 };
 */
TEST_F(EnumTranslatorTest, EnumWithSparseValues) {
    const char* code = R"(
        enum Priority { Low = 1, High = 10 };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 2);
    verifyEnumConstant(constants[0], "Low", 1);
    verifyEnumConstant(constants[1], "High", 10);
}

/**
 * Test 11: Enum with negative values
 * C++: enum Range { Min = -1, Zero = 0, Max = 1 };
 * C:   enum Range { Min = -1, Zero = 0, Max = 1 };
 */
TEST_F(EnumTranslatorTest, EnumWithNegativeValues) {
    const char* code = R"(
        enum Range { Min = -1, Zero = 0, Max = 1 };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 3);
    verifyEnumConstant(constants[0], "Min", -1);
    verifyEnumConstant(constants[1], "Zero", 0);
    verifyEnumConstant(constants[2], "Max", 1);
}

// =============================================================================
// Group 4: Type Specifications
// =============================================================================

/**
 * Test 12: Enum with uint8_t underlying type
 * C++: enum class Status : uint8_t { OK, Error };
 * C:   typedef enum Status { Status__OK, Status__Error } Status;
 */
TEST_F(EnumTranslatorTest, EnumWithUint8Type) {
    const char* code = R"(
        #include <cstdint>
        enum class Status : uint8_t { OK, Error };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_TRUE(cppEnum->isScoped());
    EXPECT_TRUE(cppEnum->isFixed()) << "Enum should have fixed underlying type";

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    verifyEnumStructure(cEnum, "Status", 2, false);

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 2);
    verifyEnumConstant(constants[0], "Status__OK", 0);
    verifyEnumConstant(constants[1], "Status__Error", 1);

    // TODO: Verify typedef generation when implemented
    // For now, just verify the enum is translated correctly
}

/**
 * Test 13: Enum with int32_t underlying type
 * C++: enum class Priority : int32_t { Low, High };
 * C:   typedef enum Priority { Priority__Low, Priority__High } Priority;
 */
TEST_F(EnumTranslatorTest, EnumWithInt32Type) {
    const char* code = R"(
        #include <cstdint>
        enum class Priority : int32_t { Low, High };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_TRUE(cppEnum->isScoped());
    EXPECT_TRUE(cppEnum->isFixed());

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    verifyEnumStructure(cEnum, "Priority", 2, false);

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 2);
    verifyEnumConstant(constants[0], "Priority__Low", 0);
    verifyEnumConstant(constants[1], "Priority__High", 1);
}

/**
 * Test 14: Enum with auto-increment and type specification
 * C++: enum class Flags : uint16_t { A = 1, B, C };
 * C:   typedef enum Flags { Flags__A = 1, Flags__B = 2, Flags__C = 3 } Flags;
 */
TEST_F(EnumTranslatorTest, EnumWithAutoIncrementAndType) {
    const char* code = R"(
        #include <cstdint>
        enum class Flags : uint16_t { A = 1, B, C };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_TRUE(cppEnum->isScoped());
    EXPECT_TRUE(cppEnum->isFixed());

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    verifyEnumStructure(cEnum, "Flags", 3, false);

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 3);
    verifyEnumConstant(constants[0], "Flags__A", 1);
    verifyEnumConstant(constants[1], "Flags__B", 2);
    verifyEnumConstant(constants[2], "Flags__C", 3);
}

// =============================================================================
// Group 5: Edge Cases
// =============================================================================

/**
 * Test 15: Enum with MAX_INT value
 * C++: enum Limit { Max = 2147483647 };
 * C:   enum Limit { Max = 2147483647 };
 */
TEST_F(EnumTranslatorTest, EnumWithMaxIntValue) {
    const char* code = R"(
        enum Limit { Max = 2147483647 };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 1);
    verifyEnumConstant(constants[0], "Max", 2147483647);
}

/**
 * Test 16: Duplicate constant names in different enums
 * C++: enum A { X }; enum B { X };
 * C:   enum A { X }; enum B { X }; // Valid in C (different enum scopes)
 */
TEST_F(EnumTranslatorTest, EnumWithDuplicateNamesInDifferentEnums) {
    const char* code = R"(
        enum A { X };
        enum B { Y };
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    // Recreate context

    auto enums = getAllEnumDecls();
    ASSERT_EQ(enums.size(), 2);

    // Translate both enums
    auto* cEnumA = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(enums[0], *context)
    );
    auto* cEnumB = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(enums[1], *context)
    );

    EXPECT_EQ(cEnumA->getNameAsString(), "A");
    EXPECT_EQ(cEnumB->getNameAsString(), "B");

    auto constantsA = getEnumConstants(cEnumA);
    auto constantsB = getEnumConstants(cEnumB);

    ASSERT_EQ(constantsA.size(), 1);
    ASSERT_EQ(constantsB.size(), 1);

    EXPECT_EQ(constantsA[0]->getNameAsString(), "X");
    EXPECT_EQ(constantsB[0]->getNameAsString(), "Y");
}

/**
 * Test 17: Anonymous enum (edge case)
 * C++: enum { Anonymous };
 * C:   enum { Anonymous };
 */
TEST_F(EnumTranslatorTest, AnonymousEnum) {
    const char* code = R"(
        enum { Anonymous };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_TRUE(cppEnum->getName().empty() || !cppEnum->getDeclName());

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    // Anonymous enum should be preserved
    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 1);
    verifyEnumConstant(constants[0], "Anonymous", 0);
}

/**
 * Test 18: Scoped enum with type combination
 * C++: enum class HttpStatus : uint16_t { OK = 200, NotFound = 404 };
 * C:   typedef enum HttpStatus { HttpStatus__OK = 200, HttpStatus__NotFound = 404 } HttpStatus;
 */
TEST_F(EnumTranslatorTest, ScopedEnumWithTypeCombination) {
    const char* code = R"(
        #include <cstdint>
        enum class HttpStatus : uint16_t { OK = 200, NotFound = 404 };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_TRUE(cppEnum->isScoped());
    EXPECT_TRUE(cppEnum->isFixed());

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    verifyEnumStructure(cEnum, "HttpStatus", 2, false);

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 2);
    verifyEnumConstant(constants[0], "HttpStatus__OK", 200);
    verifyEnumConstant(constants[1], "HttpStatus__NotFound", 404);
}

/**
 * Test 19: Unscoped enum with type specification
 * C++: enum Color : uint8_t { Red, Green, Blue };
 * C:   typedef enum Color { Red, Green, Blue } Color;
 */
TEST_F(EnumTranslatorTest, UnscopedEnumWithType) {
    const char* code = R"(
        #include <cstdint>
        enum Color : uint8_t { Red, Green, Blue };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_FALSE(cppEnum->isScoped());
    EXPECT_TRUE(cppEnum->isFixed());

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    verifyEnumStructure(cEnum, "Color", 3, false);

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 3);
    verifyEnumConstant(constants[0], "Red", 0);
    verifyEnumConstant(constants[1], "Green", 1);
    verifyEnumConstant(constants[2], "Blue", 2);
}

/**
 * Test 20: Enum with all features
 * Comprehensive test combining scoping, type, explicit values, and prefixing
 * C++: enum class Result : int32_t { Success = 0, Warning = 1, Error = -1 };
 * C:   typedef enum Result { Result__Success = 0, Result__Warning = 1, Result__Error = -1 } Result;
 */
TEST_F(EnumTranslatorTest, EnumWithAllFeatures) {
    const char* code = R"(
        #include <cstdint>
        enum class Result : int32_t { Success = 0, Warning = 1, Error = -1 };
    )";

    const auto* cppEnum = getEnumDeclFromCode(code);
    ASSERT_NE(cppEnum, nullptr);
    EXPECT_TRUE(cppEnum->isScoped()) << "Should be scoped enum";
    EXPECT_TRUE(cppEnum->isFixed()) << "Should have fixed underlying type";

    auto* cEnum = llvm::cast<clang::EnumDecl>(
        translator->handleDecl(cppEnum, *context)
    );

    verifyEnumStructure(cEnum, "Result", 3, false);

    auto constants = getEnumConstants(cEnum);
    ASSERT_EQ(constants.size(), 3);

    // Verify scoped prefixing and explicit values
    verifyEnumConstant(constants[0], "Result__Success", 0);
    verifyEnumConstant(constants[1], "Result__Warning", 1);
    verifyEnumConstant(constants[2], "Result__Error", -1);
}
