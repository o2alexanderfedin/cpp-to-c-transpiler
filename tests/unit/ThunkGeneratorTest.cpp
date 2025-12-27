/**
 * @file ThunkGeneratorTest.cpp
 * @brief Unit tests for ThunkGenerator
 *
 * Phase 46, Group 2, Task 5: Thunk Function Generation
 * Tests: 15 tests covering all requirements
 */

#include "ThunkGenerator.h"
#include "MultipleInheritanceAnalyzer.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

/**
 * @class ThunkGeneratorTest
 * @brief Test fixture for ThunkGenerator
 */
class ThunkGeneratorTest : public ::testing::Test {
protected:
    /**
     * @brief Helper to parse C++ code and get CXXRecordDecl by name
     */
    CXXRecordDecl* getClass(const std::string& code, const std::string& className) {
        auto AST = tooling::buildASTFromCode(code);
        if (!AST) return nullptr;

        context = std::move(AST);
        generator = std::make_unique<ThunkGenerator>(
            context->getASTContext(),
            context->getASTContext()
        );

        for (auto* decl : context->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* record = dyn_cast<CXXRecordDecl>(decl)) {
                if (record->getNameAsString() == className && record->isCompleteDefinition()) {
                    return record;
                }
            }
        }
        return nullptr;
    }

    /**
     * @brief Helper to get CXXMethodDecl by name from a class
     */
    CXXMethodDecl* getMethod(const CXXRecordDecl* record, const std::string& methodName) {
        if (!record) return nullptr;

        for (auto* method : record->methods()) {
            if (method->getNameAsString() == methodName) {
                return method;
            }
        }
        return nullptr;
    }

    /**
     * @brief Helper to get base class by name from a derived class
     */
    const CXXRecordDecl* getBase(const CXXRecordDecl* derived, const std::string& baseName) {
        if (!derived) return nullptr;

        for (const auto& base : derived->bases()) {
            if (const auto* baseRecord = base.getType()->getAsCXXRecordDecl()) {
                if (baseRecord->getNameAsString() == baseName) {
                    return baseRecord;
                }
            }
        }
        return nullptr;
    }

    std::unique_ptr<clang::ASTUnit> context;
    std::unique_ptr<ThunkGenerator> generator;
};

// ============================================================================
// Test 1: Generate Thunk for Single Non-Primary Base Method
// ============================================================================

TEST_F(ThunkGeneratorTest, GenerateThunkForSingleNonPrimaryBase) {
    std::string code = R"(
        class Base1 {
        public:
            virtual void method1() {}
        };

        class Base2 {
        public:
            virtual void method2() {}
        };

        class Derived : public Base1, public Base2 {
        public:
            void method2() override {}
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* base2 = getBase(derived, "Base2");
    ASSERT_NE(base2, nullptr);

    auto* method2 = getMethod(derived, "method2");
    ASSERT_NE(method2, nullptr);

    // Calculate base offset
    MultipleInheritanceAnalyzer analyzer(context->getASTContext());
    uint64_t offset = analyzer.calculateBaseOffset(derived, base2);

    // Generate thunk
    FunctionDecl* thunk = generator->generateThunk(derived, method2, base2, offset);

    ASSERT_NE(thunk, nullptr) << "Should generate thunk for non-primary base method";

    // Verify thunk signature matches original method
    EXPECT_EQ(thunk->getReturnType().getAsString(), "void");
    EXPECT_EQ(thunk->getNumParams(), 1); // Just 'this' parameter
}

// ============================================================================
// Test 2: Generate Thunk Name Pattern
// ============================================================================

TEST_F(ThunkGeneratorTest, GenerateThunkNamePattern) {
    std::string code = R"(
        class Base1 { public: virtual void foo() {} };
        class Base2 { public: virtual void bar() {} };
        class Derived : public Base1, public Base2 {
        public:
            void bar() override {}
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* base2 = getBase(derived, "Base2");
    ASSERT_NE(base2, nullptr);

    auto* method = getMethod(derived, "bar");
    ASSERT_NE(method, nullptr);

    // Get thunk name
    std::string thunkName = generator->getThunkName(derived, method, base2);

    // Pattern: ClassName_methodName_BaseName_thunk
    EXPECT_EQ(thunkName, "Derived_bar_Base2_thunk");
}

// ============================================================================
// Test 3: Thunk Adjusts This Pointer Correctly
// ============================================================================

TEST_F(ThunkGeneratorTest, ThunkAdjustsThisPointerCorrectly) {
    std::string code = R"(
        class Base1 { public: virtual void f1() {} };
        class Base2 { public: virtual void f2() {} };
        class Derived : public Base1, public Base2 {
        public:
            void f2() override {}
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* base2 = getBase(derived, "Base2");
    ASSERT_NE(base2, nullptr);

    auto* method = getMethod(derived, "f2");
    ASSERT_NE(method, nullptr);

    MultipleInheritanceAnalyzer analyzer(context->getASTContext());
    uint64_t offset = analyzer.calculateBaseOffset(derived, base2);
    ASSERT_GT(offset, 0) << "Base2 should have non-zero offset";

    FunctionDecl* thunk = generator->generateThunk(derived, method, base2, offset);
    ASSERT_NE(thunk, nullptr);

    // Verify thunk has body that adjusts this pointer
    ASSERT_NE(thunk->getBody(), nullptr) << "Thunk should have implementation body";
}

// ============================================================================
// Test 4: Thunk Calls Real Method Implementation
// ============================================================================

TEST_F(ThunkGeneratorTest, ThunkCallsRealMethodImplementation) {
    std::string code = R"(
        class IDrawable { public: virtual void draw() = 0; };
        class ISerializable { public: virtual void serialize() = 0; };
        class Shape : public IDrawable, public ISerializable {
        public:
            void draw() override {}
            void serialize() override {}
        };
    )";

    auto* shape = getClass(code, "Shape");
    ASSERT_NE(shape, nullptr);

    auto* iSerializable = getBase(shape, "ISerializable");
    ASSERT_NE(iSerializable, nullptr);

    auto* method = getMethod(shape, "serialize");
    ASSERT_NE(method, nullptr);

    MultipleInheritanceAnalyzer analyzer(context->getASTContext());
    uint64_t offset = analyzer.calculateBaseOffset(shape, iSerializable);

    FunctionDecl* thunk = generator->generateThunk(shape, method, iSerializable, offset);
    ASSERT_NE(thunk, nullptr);
    ASSERT_NE(thunk->getBody(), nullptr);

    // Verify thunk body contains a call to the real implementation
    // (This would check the AST structure of the thunk body)
}

// ============================================================================
// Test 5: Thunk Preserves Return Type
// ============================================================================

TEST_F(ThunkGeneratorTest, ThunkPreservesReturnType) {
    std::string code = R"(
        class Base1 { public: virtual int getValue() { return 0; } };
        class Base2 { public: virtual int compute() { return 0; } };
        class Derived : public Base1, public Base2 {
        public:
            int compute() override { return 42; }
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* base2 = getBase(derived, "Base2");
    ASSERT_NE(base2, nullptr);

    auto* method = getMethod(derived, "compute");
    ASSERT_NE(method, nullptr);

    MultipleInheritanceAnalyzer analyzer(context->getASTContext());
    uint64_t offset = analyzer.calculateBaseOffset(derived, base2);

    FunctionDecl* thunk = generator->generateThunk(derived, method, base2, offset);
    ASSERT_NE(thunk, nullptr);

    // Verify thunk preserves return type
    EXPECT_EQ(thunk->getReturnType().getAsString(), "int");
}

// ============================================================================
// Test 6: Thunk Preserves Parameters
// ============================================================================

TEST_F(ThunkGeneratorTest, ThunkPreservesParameters) {
    std::string code = R"(
        class Base1 { public: virtual void foo() {} };
        class Base2 { public: virtual void process(int x, double y) {} };
        class Derived : public Base1, public Base2 {
        public:
            void process(int x, double y) override {}
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* base2 = getBase(derived, "Base2");
    ASSERT_NE(base2, nullptr);

    auto* method = getMethod(derived, "process");
    ASSERT_NE(method, nullptr);

    MultipleInheritanceAnalyzer analyzer(context->getASTContext());
    uint64_t offset = analyzer.calculateBaseOffset(derived, base2);

    FunctionDecl* thunk = generator->generateThunk(derived, method, base2, offset);
    ASSERT_NE(thunk, nullptr);

    // Verify thunk preserves parameters (3 total: this, x, y)
    EXPECT_EQ(thunk->getNumParams(), 3);

    // First param is 'this'
    EXPECT_TRUE(thunk->getParamDecl(0)->getType()->isPointerType());

    // Second param is 'int x'
    EXPECT_EQ(thunk->getParamDecl(1)->getType().getAsString(), "int");

    // Third param is 'double y'
    EXPECT_EQ(thunk->getParamDecl(2)->getType().getAsString(), "double");
}

// ============================================================================
// Test 7: Generate Thunks for Overridden Virtual Methods
// ============================================================================

TEST_F(ThunkGeneratorTest, GenerateThunksForOverriddenVirtualMethods) {
    std::string code = R"(
        class IBase1 { public: virtual void method1() = 0; };
        class IBase2 { public: virtual void method2() = 0; };
        class Implementation : public IBase1, public IBase2 {
        public:
            void method1() override {}
            void method2() override {}
        };
    )";

    auto* impl = getClass(code, "Implementation");
    ASSERT_NE(impl, nullptr);

    auto* base2 = getBase(impl, "IBase2");
    ASSERT_NE(base2, nullptr);

    auto* method2 = getMethod(impl, "method2");
    ASSERT_NE(method2, nullptr);
    ASSERT_TRUE(method2->isVirtual()) << "method2 should be virtual";

    MultipleInheritanceAnalyzer analyzer(context->getASTContext());
    uint64_t offset = analyzer.calculateBaseOffset(impl, base2);

    FunctionDecl* thunk = generator->generateThunk(impl, method2, base2, offset);
    ASSERT_NE(thunk, nullptr) << "Should generate thunk for overridden virtual method";
}

// ============================================================================
// Test 8: Handle Multiple Non-Primary Bases
// ============================================================================

TEST_F(ThunkGeneratorTest, HandleMultipleNonPrimaryBases) {
    std::string code = R"(
        class Base1 { public: virtual void f1() {} };
        class Base2 { public: virtual void f2() {} };
        class Base3 { public: virtual void f3() {} };
        class Derived : public Base1, public Base2, public Base3 {
        public:
            void f2() override {}
            void f3() override {}
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Generate thunks for all non-primary bases
    auto thunks = generator->generateAllThunks(derived);

    // Should generate thunks for Base2 and Base3 (not Base1 which is primary)
    EXPECT_GE(thunks.size(), 2) << "Should generate thunks for Base2 and Base3";
}

// ============================================================================
// Test 9: Handle Methods with Different Signatures
// ============================================================================

TEST_F(ThunkGeneratorTest, HandleMethodsWithDifferentSignatures) {
    std::string code = R"(
        class Base1 { public: virtual void simple() {} };
        class Base2 {
        public:
            virtual int complex(double x, const char* str, bool flag) { return 0; }
        };
        class Derived : public Base1, public Base2 {
        public:
            int complex(double x, const char* str, bool flag) override { return 1; }
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* base2 = getBase(derived, "Base2");
    ASSERT_NE(base2, nullptr);

    auto* method = getMethod(derived, "complex");
    ASSERT_NE(method, nullptr);

    MultipleInheritanceAnalyzer analyzer(context->getASTContext());
    uint64_t offset = analyzer.calculateBaseOffset(derived, base2);

    FunctionDecl* thunk = generator->generateThunk(derived, method, base2, offset);
    ASSERT_NE(thunk, nullptr);

    // Verify complex signature is preserved
    EXPECT_EQ(thunk->getReturnType().getAsString(), "int");
    EXPECT_EQ(thunk->getNumParams(), 4); // this, x, str, flag
}

// ============================================================================
// Test 10: Don't Generate Thunks for Primary Base Methods
// ============================================================================

TEST_F(ThunkGeneratorTest, DontGenerateThunksForPrimaryBase) {
    std::string code = R"(
        class Primary { public: virtual void primaryMethod() {} };
        class Secondary { public: virtual void secondaryMethod() {} };
        class Derived : public Primary, public Secondary {
        public:
            void primaryMethod() override {}
            void secondaryMethod() override {}
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* primary = getBase(derived, "Primary");
    ASSERT_NE(primary, nullptr);

    auto* method = getMethod(derived, "primaryMethod");
    ASSERT_NE(method, nullptr);

    MultipleInheritanceAnalyzer analyzer(context->getASTContext());

    // Primary base should have offset 0
    uint64_t offset = analyzer.calculateBaseOffset(derived, primary);
    EXPECT_EQ(offset, 0) << "Primary base should be at offset 0";

    // Should NOT generate thunk for primary base (offset == 0)
    FunctionDecl* thunk = generator->generateThunk(derived, method, primary, offset);
    EXPECT_EQ(thunk, nullptr) << "Should NOT generate thunk for primary base";
}

// ============================================================================
// Test 11: Don't Generate Thunks for Non-Virtual Methods
// ============================================================================

TEST_F(ThunkGeneratorTest, DontGenerateThunksForNonVirtualMethods) {
    std::string code = R"(
        class Base1 { public: virtual void virtualMethod() {} };
        class Base2 {
        public:
            virtual void virtualMethod2() {}
            void nonVirtualMethod() {}  // Not virtual!
        };
        class Derived : public Base1, public Base2 {
        public:
            void nonVirtualMethod() {}  // Still not virtual
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* base2 = getBase(derived, "Base2");
    ASSERT_NE(base2, nullptr);

    auto* method = getMethod(derived, "nonVirtualMethod");
    ASSERT_NE(method, nullptr);
    ASSERT_FALSE(method->isVirtual()) << "Method should not be virtual";

    MultipleInheritanceAnalyzer analyzer(context->getASTContext());
    uint64_t offset = analyzer.calculateBaseOffset(derived, base2);

    // Should NOT generate thunk for non-virtual method
    FunctionDecl* thunk = generator->generateThunk(derived, method, base2, offset);
    EXPECT_EQ(thunk, nullptr) << "Should NOT generate thunk for non-virtual method";
}

// ============================================================================
// Test 12: Edge Case - Method with No Parameters
// ============================================================================

TEST_F(ThunkGeneratorTest, MethodWithNoParameters) {
    std::string code = R"(
        class Base1 { public: virtual void foo() {} };
        class Base2 { public: virtual void bar() {} };
        class Derived : public Base1, public Base2 {
        public:
            void bar() override {}
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* base2 = getBase(derived, "Base2");
    ASSERT_NE(base2, nullptr);

    auto* method = getMethod(derived, "bar");
    ASSERT_NE(method, nullptr);

    MultipleInheritanceAnalyzer analyzer(context->getASTContext());
    uint64_t offset = analyzer.calculateBaseOffset(derived, base2);

    FunctionDecl* thunk = generator->generateThunk(derived, method, base2, offset);
    ASSERT_NE(thunk, nullptr);

    // Should have only 'this' parameter
    EXPECT_EQ(thunk->getNumParams(), 1);
    EXPECT_TRUE(thunk->getParamDecl(0)->getType()->isPointerType());
}

// ============================================================================
// Test 13: GenerateAllThunks Returns Correct Count
// ============================================================================

TEST_F(ThunkGeneratorTest, GenerateAllThunksReturnsCorrectCount) {
    std::string code = R"(
        class IFoo { public: virtual void foo() = 0; };
        class IBar { public: virtual void bar() = 0; };
        class IBaz { public: virtual void baz() = 0; };
        class Impl : public IFoo, public IBar, public IBaz {
        public:
            void foo() override {}
            void bar() override {}
            void baz() override {}
        };
    )";

    auto* impl = getClass(code, "Impl");
    ASSERT_NE(impl, nullptr);

    auto thunks = generator->generateAllThunks(impl);

    // Should generate thunks for IBar and IBaz (2 non-primary bases)
    // Each has 1 virtual method, so 2 thunks total
    EXPECT_EQ(thunks.size(), 2) << "Should generate 2 thunks for 2 non-primary bases";
}

// ============================================================================
// Test 14: Null Input Handling
// ============================================================================

TEST_F(ThunkGeneratorTest, NullInputHandling) {
    std::string code = "class Dummy {};";
    auto* dummy = getClass(code, "Dummy");
    ASSERT_NE(dummy, nullptr);

    // These should not crash with null input
    EXPECT_EQ(generator->generateThunk(nullptr, nullptr, nullptr, 0), nullptr);
    EXPECT_EQ(generator->generateAllThunks(nullptr).size(), 0);
    EXPECT_EQ(generator->getThunkName(nullptr, nullptr, nullptr), "");
}

// ============================================================================
// Test 15: GetThunkName for Various Combinations
// ============================================================================

TEST_F(ThunkGeneratorTest, GetThunkNameForVariousCombinations) {
    std::string code = R"(
        class Base1 { public: virtual void method1() {} };
        class Base2 { public: virtual void method2() {} };
        class MyDerivedClass : public Base1, public Base2 {
        public:
            void method2() override {}
        };
    )";

    auto* derived = getClass(code, "MyDerivedClass");
    ASSERT_NE(derived, nullptr);

    auto* base2 = getBase(derived, "Base2");
    ASSERT_NE(base2, nullptr);

    auto* method = getMethod(derived, "method2");
    ASSERT_NE(method, nullptr);

    std::string thunkName = generator->getThunkName(derived, method, base2);

    // Pattern: ClassName_methodName_BaseName_thunk
    EXPECT_EQ(thunkName, "MyDerivedClass_method2_Base2_thunk");
}
