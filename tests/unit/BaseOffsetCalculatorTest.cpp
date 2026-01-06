/**
 * @file BaseOffsetCalculatorTest.cpp
 * @brief Unit tests for BaseOffsetCalculator
 *
 * Phase 46, Group 2, Task 4: Base Offset Calculator
 *
 * Tests the calculation of base class offsets for this-pointer adjustment thunks.
 * This is critical for multiple inheritance where non-primary base method calls
 * need to adjust the this pointer.
 */

#include "BaseOffsetCalculator.h"
#include "gtest/gtest.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <memory>

using namespace clang;

class BaseOffsetCalculatorTest : public ::testing::Test {
protected:
    /**
     * @brief Helper to parse C++ code and get AST
     */
    std::unique_ptr<ASTUnit> parseCode(const std::string& code) {
        return tooling::buildASTFromCode(code);
    }

    /**
     * @brief Helper to find a record by name in the AST
     */
    const CXXRecordDecl* findRecord(ASTContext& Ctx, const std::string& name) {
        auto decls = Ctx.getTranslationUnitDecl()->decls();
        for (auto it = decls.begin(); it != decls.end(); ++it) {
            if (auto* record = dyn_cast<CXXRecordDecl>(*it)) {
                if (record->getNameAsString() == name && record->isCompleteDefinition()) {
                    return record;
                }
            }
        }
        return nullptr;
    }
};

/**
 * Test 1: Calculate offset for first non-primary base (lpVtbl2)
 *
 * Given: Class with 2 polymorphic bases
 * When: Calculate offset for second base
 * Then: Offset equals sizeof(void*) (one vtable pointer)
 */
TEST_F(BaseOffsetCalculatorTest, CalculateOffsetForFirstNonPrimaryBase) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };

        class ISerializable {
        public:
            virtual void serialize() = 0;
        };

        class Shape : public IDrawable, public ISerializable {
        public:
            int x;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST != nullptr);

    auto& Ctx = AST->getASTContext();
    const CXXRecordDecl* Shape = findRecord(Ctx, "Shape");
    const CXXRecordDecl* ISerializable = findRecord(Ctx, "ISerializable");

    ASSERT_TRUE(Shape != nullptr);
    ASSERT_TRUE(ISerializable != nullptr);

    BaseOffsetCalculator calculator(Ctx);

    // ISerializable is the first non-primary base (second base overall)
    uint64_t offset = calculator.getBaseOffset(Shape, ISerializable);

    // On most platforms, offset should be sizeof(void*) = 8 bytes
    EXPECT_EQ(offset, 8u);
}

/**
 * Test 2: Calculate offset for second non-primary base (lpVtbl3)
 *
 * Given: Class with 3 polymorphic bases
 * When: Calculate offset for third base
 * Then: Offset equals 2 * sizeof(void*) (two vtable pointers)
 */
TEST_F(BaseOffsetCalculatorTest, CalculateOffsetForSecondNonPrimaryBase) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };

        class ISerializable {
        public:
            virtual void serialize() = 0;
        };

        class IUpdatable {
        public:
            virtual void update() = 0;
        };

        class GameObject : public IDrawable, public ISerializable, public IUpdatable {
        public:
            int id;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST != nullptr);

    auto& Ctx = AST->getASTContext();
    const CXXRecordDecl* GameObject = findRecord(Ctx, "GameObject");
    const CXXRecordDecl* IUpdatable = findRecord(Ctx, "IUpdatable");

    ASSERT_TRUE(GameObject != nullptr);
    ASSERT_TRUE(IUpdatable != nullptr);

    BaseOffsetCalculator calculator(Ctx);

    // IUpdatable is the second non-primary base (third base overall)
    uint64_t offset = calculator.getBaseOffset(GameObject, IUpdatable);

    // Offset should be 2 * sizeof(void*) = 16 bytes
    EXPECT_EQ(offset, 16u);
}

/**
 * Test 3: Primary base has offset 0
 *
 * Given: Class with multiple polymorphic bases
 * When: Calculate offset for first base (primary)
 * Then: Offset equals 0 (no adjustment needed)
 */
TEST_F(BaseOffsetCalculatorTest, PrimaryBaseHasOffsetZero) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };

        class ISerializable {
        public:
            virtual void serialize() = 0;
        };

        class Shape : public IDrawable, public ISerializable {
        };
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST != nullptr);

    auto& Ctx = AST->getASTContext();
    const CXXRecordDecl* Shape = findRecord(Ctx, "Shape");
    const CXXRecordDecl* IDrawable = findRecord(Ctx, "IDrawable");

    ASSERT_TRUE(Shape != nullptr);
    ASSERT_TRUE(IDrawable != nullptr);

    BaseOffsetCalculator calculator(Ctx);

    // IDrawable is the primary base
    uint64_t offset = calculator.getBaseOffset(Shape, IDrawable);

    EXPECT_EQ(offset, 0u);
}

/**
 * Test 4: isPrimaryBase correctly identifies primary base
 *
 * Given: Class with multiple polymorphic bases
 * When: Check if first base is primary
 * Then: Returns true for first base, false for others
 */
TEST_F(BaseOffsetCalculatorTest, IsPrimaryBaseIdentification) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };

        class ISerializable {
        public:
            virtual void serialize() = 0;
        };

        class Shape : public IDrawable, public ISerializable {
        };
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST != nullptr);

    auto& Ctx = AST->getASTContext();
    const CXXRecordDecl* Shape = findRecord(Ctx, "Shape");
    const CXXRecordDecl* IDrawable = findRecord(Ctx, "IDrawable");
    const CXXRecordDecl* ISerializable = findRecord(Ctx, "ISerializable");

    ASSERT_TRUE(Shape != nullptr);
    ASSERT_TRUE(IDrawable != nullptr);
    ASSERT_TRUE(ISerializable != nullptr);

    BaseOffsetCalculator calculator(Ctx);

    // IDrawable is primary
    EXPECT_TRUE(calculator.isPrimaryBase(Shape, IDrawable));

    // ISerializable is not primary
    EXPECT_FALSE(calculator.isPrimaryBase(Shape, ISerializable));
}

/**
 * Test 5: getLpVtblFieldOffset calculates lpVtbl field offset
 *
 * Given: Class with multiple polymorphic bases
 * When: Get lpVtbl field offset for non-primary base
 * Then: Returns correct offset for the lpVtbl field
 */
TEST_F(BaseOffsetCalculatorTest, GetLpVtblFieldOffset) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };

        class ISerializable {
        public:
            virtual void serialize() = 0;
        };

        class Shape : public IDrawable, public ISerializable {
        public:
            int x, y;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST != nullptr);

    auto& Ctx = AST->getASTContext();
    const CXXRecordDecl* Shape = findRecord(Ctx, "Shape");
    const CXXRecordDecl* ISerializable = findRecord(Ctx, "ISerializable");

    ASSERT_TRUE(Shape != nullptr);
    ASSERT_TRUE(ISerializable != nullptr);

    BaseOffsetCalculator calculator(Ctx);

    // lpVtbl2 field offset should be sizeof(void*)
    uint64_t offset = calculator.getLpVtblFieldOffset(Shape, ISerializable);

    EXPECT_EQ(offset, 8u);
}

/**
 * Test 6: Handle nested multiple inheritance
 *
 * Given: Class hierarchy with multiple levels
 * When: Calculate offset for inherited base
 * Then: Returns correct offset accounting for hierarchy
 */
TEST_F(BaseOffsetCalculatorTest, HandleNestedMultipleInheritance) {
    std::string code = R"(
        class IBase1 {
        public:
            virtual void method1() = 0;
        };

        class IBase2 {
        public:
            virtual void method2() = 0;
        };

        class Intermediate : public IBase1, public IBase2 {
        };

        class IBase3 {
        public:
            virtual void method3() = 0;
        };

        class Derived : public Intermediate, public IBase3 {
        };
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST != nullptr);

    auto& Ctx = AST->getASTContext();
    const CXXRecordDecl* Derived = findRecord(Ctx, "Derived");
    const CXXRecordDecl* IBase3 = findRecord(Ctx, "IBase3");

    ASSERT_TRUE(Derived != nullptr);
    ASSERT_TRUE(IBase3 != nullptr);

    BaseOffsetCalculator calculator(Ctx);

    // IBase3 is a direct base of Derived
    // Intermediate contributes its own size (2 vtable pointers for IBase1 and IBase2)
    uint64_t offset = calculator.getBaseOffset(Derived, IBase3);

    // Should be at least sizeof(void*) * 2 (for Intermediate's two vtables)
    EXPECT_GE(offset, 16u);
}

/**
 * Test 7: Edge case - no non-primary bases
 *
 * Given: Class with single polymorphic base
 * When: Calculate offset for the only base
 * Then: Returns 0 (primary base)
 */
TEST_F(BaseOffsetCalculatorTest, EdgeCaseNoNonPrimaryBases) {
    std::string code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };

        class Shape : public IDrawable {
        public:
            int x, y;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST != nullptr);

    auto& Ctx = AST->getASTContext();
    const CXXRecordDecl* Shape = findRecord(Ctx, "Shape");
    const CXXRecordDecl* IDrawable = findRecord(Ctx, "IDrawable");

    ASSERT_TRUE(Shape != nullptr);
    ASSERT_TRUE(IDrawable != nullptr);

    BaseOffsetCalculator calculator(Ctx);

    // Only one base, so it's primary with offset 0
    uint64_t offset = calculator.getBaseOffset(Shape, IDrawable);

    EXPECT_EQ(offset, 0u);
    EXPECT_TRUE(calculator.isPrimaryBase(Shape, IDrawable));
}

/**
 * Test 8: Null input handling
 *
 * Given: Null pointers
 * When: Call methods with null
 * Then: Returns 0 and doesn't crash
 */
TEST_F(BaseOffsetCalculatorTest, NullInputHandling) {
    std::string code = R"(
        class IBase {
        public:
            virtual void method() = 0;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST != nullptr);

    auto& Ctx = AST->getASTContext();

    BaseOffsetCalculator calculator(Ctx);

    // Null derived
    EXPECT_EQ(calculator.getBaseOffset(nullptr, nullptr), 0u);

    // Null base
    const CXXRecordDecl* IBase = findRecord(Ctx, "IBase");
    EXPECT_EQ(calculator.getBaseOffset(IBase, nullptr), 0u);

    // isPrimaryBase with nulls
    EXPECT_FALSE(calculator.isPrimaryBase(nullptr, nullptr));
    EXPECT_FALSE(calculator.isPrimaryBase(IBase, nullptr));
    EXPECT_FALSE(calculator.isPrimaryBase(nullptr, IBase));
}
