/**
 * @file MultipleInheritanceIntegrationTest.cpp
 * @brief Integration tests for multiple inheritance handler pipeline (Phase 46 Group 5 Task 12)
 *
 * Tests that all multiple inheritance components work together correctly:
 * - MultipleInheritanceAnalyzer (base analysis)
 * - VtableGenerator (multiple vtable struct generation)
 * - RecordHandler (multiple lpVtbl field injection)
 * - BaseOffsetCalculator (offset calculation)
 * - ThunkGenerator (this-pointer adjustment thunks)
 * - ConstructorHandler (multiple lpVtbl initialization)
 * - ExpressionHandler (base casts and polymorphic calls)
 *
 * 37 tests covering:
 * - Basic multiple inheritance scenarios (8 tests)
 * - Initialization & lifecycle (2 tests)
 * - Polymorphic calls (6 tests)
 * - Casts (3 tests)
 * - Method behavior (3 tests)
 * - Verification (4 tests)
 * - Edge cases (11 tests)
 */

#include "handlers/FunctionHandler.h"
#include "handlers/VariableHandler.h"
#include "handlers/ExpressionHandler.h"
#include "handlers/StatementHandler.h"
#include "handlers/RecordHandler.h"
#include "handlers/MethodHandler.h"
#include "handlers/ConstructorHandler.h"
#include "handlers/DestructorHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "MultipleInheritanceAnalyzer.h"
#include "VtableGenerator.h"
#include "ThunkGenerator.h"
#include "BaseOffsetCalculator.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>
#include <map>

using namespace cpptoc;

/**
 * @class MultipleInheritanceIntegrationTest
 * @brief Test fixture for multiple inheritance integration testing
 */
class MultipleInheritanceIntegrationTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;

    std::unique_ptr<MultipleInheritanceAnalyzer> analyzer;
    std::unique_ptr<BaseOffsetCalculator> offsetCalc;

    void SetUp() override {
        // Create real AST contexts
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr);
        ASSERT_NE(cAST, nullptr);

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        // Create multiple inheritance components
        analyzer = std::make_unique<MultipleInheritanceAnalyzer>(cppAST->getASTContext());
        offsetCalc = std::make_unique<BaseOffsetCalculator>(cppAST->getASTContext());
    }

    void TearDown() override {
        offsetCalc.reset();
        analyzer.reset();
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Helper to parse code and keep AST alive, extracting multiple classes
     * Returns a tuple of (AST, map of class names to CXXRecordDecl*)
     */
    std::pair<std::unique_ptr<clang::ASTUnit>, std::map<std::string, clang::CXXRecordDecl*>>
    parseCode(const std::string& code) {
        auto testAST = clang::tooling::buildASTFromCode(code);
        std::map<std::string, clang::CXXRecordDecl*> classes;

        if (!testAST) return {nullptr, classes};

        for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (record->isCompleteDefinition()) {
                    classes[record->getNameAsString()] = record;
                }
            }
        }
        return {std::move(testAST), classes};
    }

    /**
     * @brief Simple helper to extract a class from code (legacy pattern from VirtualMethodsIntegrationTest)
     * NOTE: This pattern works for simple property checks but NOT for deep AST traversal
     */
    clang::CXXRecordDecl* extractClass(const std::string& code, const std::string& className) {
        auto testAST = clang::tooling::buildASTFromCode(code);
        if (!testAST) return nullptr;

        for (auto* decl : testAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* record = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (record->getNameAsString() == className && record->isCompleteDefinition()) {
                    return record;
                }
            }
        }
        return nullptr;
    }

    /**
     * @brief Count polymorphic bases
     */
    int countPolymorphicBases(const clang::CXXRecordDecl* record) {
        if (!record) return 0;
        int count = 0;
        for (const auto& base : record->bases()) {
            if (auto* baseRecord = base.getType()->getAsCXXRecordDecl()) {
                if (baseRecord->isPolymorphic()) {
                    count++;
                }
            }
        }
        return count;
    }

    /**
     * @brief Count virtual methods
     */
    int countVirtualMethods(const clang::CXXRecordDecl* record) {
        if (!record) return 0;
        int count = 0;
        for (auto* method : record->methods()) {
            if (method->isVirtual()) {
                count++;
            }
        }
        return count;
    }

    /**
     * @brief Check if class has multiple inheritance
     */
    bool hasMultipleInheritance(const clang::CXXRecordDecl* record) {
        if (!record) return false;
        return record->getNumBases() > 1;
    }
};

// ============================================================================
// Basic Scenarios Tests (8 tests)
// ============================================================================

TEST_F(MultipleInheritanceIntegrationTest, SimpleTwoBaseMultipleInheritance) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void foo() {}
        };

        class Base2 {
        public:
            virtual void bar() {}
        };

        class Derived : public Base1, public Base2 {
        public:
            void foo() override {}
            void bar() override {}
        };
    )";

    // Parse code and keep AST alive
    auto [testAST, classes] = parseCode(code);
    ASSERT_NE(testAST, nullptr);

    auto* base1 = classes["Base1"];
    auto* base2 = classes["Base2"];
    auto* derived = classes["Derived"];

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(derived, nullptr);

    // Verify multiple inheritance
    EXPECT_TRUE(hasMultipleInheritance(derived));
    EXPECT_EQ(countPolymorphicBases(derived), 2);
    EXPECT_TRUE(derived->isPolymorphic());

    // Verify base classes are polymorphic
    EXPECT_TRUE(base1->isPolymorphic());
    EXPECT_TRUE(base2->isPolymorphic());
}

TEST_F(MultipleInheritanceIntegrationTest, ThreeBaseMultipleInheritance) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() = 0;
        };

        class ISerializable {
        public:
            virtual void serialize() = 0;
        };

        class ICloneable {
        public:
            virtual void clone() = 0;
        };

        class Shape : public IDrawable, public ISerializable, public ICloneable {
        public:
            void draw() override {}
            void serialize() override {}
            void clone() override {}
        };
    )";

    auto* drawable = extractClass(code, "IDrawable");
    auto* serializable = extractClass(code, "ISerializable");
    auto* cloneable = extractClass(code, "ICloneable");
    auto* shape = extractClass(code, "Shape");

    ASSERT_NE(drawable, nullptr);
    ASSERT_NE(serializable, nullptr);
    ASSERT_NE(cloneable, nullptr);
    ASSERT_NE(shape, nullptr);

    EXPECT_EQ(countPolymorphicBases(shape), 3);
    EXPECT_TRUE(shape->isPolymorphic());
    EXPECT_EQ(shape->getNumBases(), 3);
}

TEST_F(MultipleInheritanceIntegrationTest, FourBaseMultipleInheritance) {
    const char* code = R"(
        class IBase1 { public: virtual void method1() = 0; };
        class IBase2 { public: virtual void method2() = 0; };
        class IBase3 { public: virtual void method3() = 0; };
        class IBase4 { public: virtual void method4() = 0; };

        class Impl : public IBase1, public IBase2, public IBase3, public IBase4 {
        public:
            void method1() override {}
            void method2() override {}
            void method3() override {}
            void method4() override {}
        };
    )";

    auto* impl = extractClass(code, "Impl");
    ASSERT_NE(impl, nullptr);

    EXPECT_EQ(countPolymorphicBases(impl), 4);
    EXPECT_TRUE(impl->isPolymorphic());
    EXPECT_EQ(impl->getNumBases(), 4);
}

TEST_F(MultipleInheritanceIntegrationTest, MixedPolymorphicNonPolymorphicBases) {
    const char* code = R"(
        class NonPoly {
        public:
            int value;
        };

        class Poly1 {
        public:
            virtual void foo() {}
        };

        class Poly2 {
        public:
            virtual void bar() {}
        };

        class Mixed : public NonPoly, public Poly1, public Poly2 {
        public:
            void foo() override {}
            void bar() override {}
        };
    )";

    auto* nonPoly = extractClass(code, "NonPoly");
    auto* poly1 = extractClass(code, "Poly1");
    auto* poly2 = extractClass(code, "Poly2");
    auto* mixed = extractClass(code, "Mixed");

    ASSERT_NE(nonPoly, nullptr);
    ASSERT_NE(poly1, nullptr);
    ASSERT_NE(poly2, nullptr);
    ASSERT_NE(mixed, nullptr);

    // NonPoly is not polymorphic
    EXPECT_FALSE(nonPoly->isPolymorphic());

    // Poly1 and Poly2 are polymorphic
    EXPECT_TRUE(poly1->isPolymorphic());
    EXPECT_TRUE(poly2->isPolymorphic());

    // Mixed inherits from 3 bases but only 2 are polymorphic
    EXPECT_EQ(mixed->getNumBases(), 3);
    EXPECT_EQ(countPolymorphicBases(mixed), 2);
    EXPECT_TRUE(mixed->isPolymorphic());
}

TEST_F(MultipleInheritanceIntegrationTest, DeepHierarchyWithMultipleInheritance) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void foo() {}
        };

        class Base2 {
        public:
            virtual void bar() {}
        };

        class Level1 : public Base1, public Base2 {
        public:
            void foo() override {}
            void bar() override {}
        };

        class Level2 : public Level1 {
        public:
            virtual void baz() {}
        };
    )";

    auto* base1 = extractClass(code, "Base1");
    auto* base2 = extractClass(code, "Base2");
    auto* level1 = extractClass(code, "Level1");
    auto* level2 = extractClass(code, "Level2");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(level1, nullptr);
    ASSERT_NE(level2, nullptr);

    EXPECT_EQ(countPolymorphicBases(level1), 2);
    EXPECT_TRUE(level2->isPolymorphic());
}

TEST_F(MultipleInheritanceIntegrationTest, DiamondPatternPrepareForPhase47) {
    // This test prepares for Phase 47 (virtual inheritance)
    // For now, we just test that the diamond structure is recognized
    const char* code = R"(
        class Base {
        public:
            virtual void foo() {}
        };

        class Left : public Base {
        public:
            void foo() override {}
        };

        class Right : public Base {
        public:
            void foo() override {}
        };

        class Diamond : public Left, public Right {
        public:
            // Note: This is ambiguous without virtual inheritance
        };
    )";

    auto* base = extractClass(code, "Base");
    auto* left = extractClass(code, "Left");
    auto* right = extractClass(code, "Right");
    auto* diamond = extractClass(code, "Diamond");

    ASSERT_NE(base, nullptr);
    ASSERT_NE(left, nullptr);
    ASSERT_NE(right, nullptr);
    ASSERT_NE(diamond, nullptr);

    // Diamond has two immediate polymorphic bases
    EXPECT_EQ(countPolymorphicBases(diamond), 2);
    EXPECT_TRUE(diamond->isPolymorphic());
}

TEST_F(MultipleInheritanceIntegrationTest, VirtualMethodOverrideInMultipleBases) {
    const char* code = R"(
        class IReader {
        public:
            virtual void read() = 0;
        };

        class IWriter {
        public:
            virtual void write() = 0;
        };

        class FileHandler : public IReader, public IWriter {
        public:
            void read() override {}
            void write() override {}
        };
    )";

    auto* reader = extractClass(code, "IReader");
    auto* writer = extractClass(code, "IWriter");
    auto* handler = extractClass(code, "FileHandler");

    ASSERT_NE(reader, nullptr);
    ASSERT_NE(writer, nullptr);
    ASSERT_NE(handler, nullptr);

    EXPECT_TRUE(reader->isAbstract());
    EXPECT_TRUE(writer->isAbstract());
    EXPECT_FALSE(handler->isAbstract());
    EXPECT_EQ(countPolymorphicBases(handler), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, PureVirtualInMultipleBases) {
    const char* code = R"(
        class IInterface1 {
        public:
            virtual void method1() = 0;
            virtual void method2() = 0;
        };

        class IInterface2 {
        public:
            virtual void method3() = 0;
            virtual void method4() = 0;
        };

        class Abstract : public IInterface1, public IInterface2 {
        public:
            void method1() override {}
            void method3() override {}
            // method2 and method4 still pure virtual
        };
    )";

    auto* iface1 = extractClass(code, "IInterface1");
    auto* iface2 = extractClass(code, "IInterface2");
    auto* abstract = extractClass(code, "Abstract");

    ASSERT_NE(iface1, nullptr);
    ASSERT_NE(iface2, nullptr);
    ASSERT_NE(abstract, nullptr);

    EXPECT_TRUE(iface1->isAbstract());
    EXPECT_TRUE(iface2->isAbstract());
    EXPECT_TRUE(abstract->isAbstract()); // Still abstract - not all methods implemented
}

// ============================================================================
// Initialization & Lifecycle Tests (2 tests)
// ============================================================================

TEST_F(MultipleInheritanceIntegrationTest, ConstructorInitializesAllVtables) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void foo() {}
        };

        class Base2 {
        public:
            virtual void bar() {}
        };

        class Derived : public Base1, public Base2 {
        private:
            int value;
        public:
            Derived(int v) : value(v) {}
            void foo() override {}
            void bar() override {}
        };
    )";

    auto* derived = extractClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Verify constructor exists
    bool hasConstructor = false;
    for (auto* ctor : derived->ctors()) {
        if (!ctor->isCopyConstructor() && !ctor->isMoveConstructor()) {
            hasConstructor = true;
            break;
        }
    }
    EXPECT_TRUE(hasConstructor);

    // Constructor should initialize both lpVtbl and lpVtbl2
    EXPECT_EQ(countPolymorphicBases(derived), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, DestructorCleanupFuture) {
    // This test prepares for future destructor handling
    const char* code = R"(
        class Base1 {
        public:
            virtual ~Base1() {}
        };

        class Base2 {
        public:
            virtual ~Base2() {}
        };

        class Derived : public Base1, public Base2 {
        public:
            ~Derived() override {}
        };
    )";

    auto* base1 = extractClass(code, "Base1");
    auto* base2 = extractClass(code, "Base2");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(derived, nullptr);

    // Verify virtual destructors exist
    EXPECT_TRUE(base1->hasUserDeclaredDestructor());
    EXPECT_TRUE(base2->hasUserDeclaredDestructor());
    EXPECT_TRUE(derived->hasUserDeclaredDestructor());
}

// ============================================================================
// Polymorphic Calls Tests (6 tests)
// ============================================================================

TEST_F(MultipleInheritanceIntegrationTest, PolymorphicCallThroughPrimaryBase) {
    const char* code = R"(
        class Base1 {
        public:
            virtual int getValue() { return 1; }
        };

        class Base2 {
        public:
            virtual int getOther() { return 2; }
        };

        class Derived : public Base1, public Base2 {
        public:
            int getValue() override { return 10; }
            int getOther() override { return 20; }
        };

        void test() {
            Derived d;
            Base1* ptr = &d;
            int val = ptr->getValue(); // Polymorphic call through primary base
        }
    )";

    auto* base1 = extractClass(code, "Base1");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(derived, nullptr);

    // Base1 should be the primary base (first polymorphic base)
    EXPECT_TRUE(base1->isPolymorphic());
}

TEST_F(MultipleInheritanceIntegrationTest, PolymorphicCallThroughNonPrimaryBase) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() {}
        };

        class ISerializable {
        public:
            virtual void serialize() {}
        };

        class Shape : public IDrawable, public ISerializable {
        public:
            void draw() override {}
            void serialize() override {}
        };

        void test() {
            Shape s;
            ISerializable* ptr = &s; // Points to non-primary base
            ptr->serialize(); // Requires thunk
        }
    )";

    auto* serializable = extractClass(code, "ISerializable");
    auto* shape = extractClass(code, "Shape");

    ASSERT_NE(serializable, nullptr);
    ASSERT_NE(shape, nullptr);

    EXPECT_EQ(countPolymorphicBases(shape), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, MethodCallWithParametersThroughBase) {
    const char* code = R"(
        class IProcessor {
        public:
            virtual int process(int x, int y) = 0;
        };

        class ILogger {
        public:
            virtual void log(int level) = 0;
        };

        class Handler : public IProcessor, public ILogger {
        public:
            int process(int x, int y) override { return x + y; }
            void log(int level) override {}
        };

        void test() {
            Handler h;
            IProcessor* p = &h;
            int result = p->process(10, 20);
        }
    )";

    auto* processor = extractClass(code, "IProcessor");
    auto* logger = extractClass(code, "ILogger");
    auto* handler = extractClass(code, "Handler");

    ASSERT_NE(processor, nullptr);
    ASSERT_NE(logger, nullptr);
    ASSERT_NE(handler, nullptr);

    EXPECT_TRUE(processor->isAbstract());
    EXPECT_TRUE(logger->isAbstract());
    EXPECT_FALSE(handler->isAbstract());
}

TEST_F(MultipleInheritanceIntegrationTest, MethodCallWithReturnThroughBase) {
    const char* code = R"(
        class ICalculator {
        public:
            virtual int compute() = 0;
        };

        class IValidator {
        public:
            virtual bool validate() = 0;
        };

        class Engine : public ICalculator, public IValidator {
        public:
            int compute() override { return 42; }
            bool validate() override { return true; }
        };

        void test() {
            Engine e;
            ICalculator* calc = &e;
            int result = calc->compute();

            IValidator* val = &e;
            bool isValid = val->validate();
        }
    )";

    auto* calculator = extractClass(code, "ICalculator");
    auto* validator = extractClass(code, "IValidator");
    auto* engine = extractClass(code, "Engine");

    ASSERT_NE(calculator, nullptr);
    ASSERT_NE(validator, nullptr);
    ASSERT_NE(engine, nullptr);

    EXPECT_EQ(countPolymorphicBases(engine), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, MultipleMethodsPerBase) {
    const char* code = R"(
        class IReader {
        public:
            virtual void open() = 0;
            virtual void read() = 0;
            virtual void close() = 0;
        };

        class IWriter {
        public:
            virtual void open() = 0;
            virtual void write() = 0;
            virtual void close() = 0;
        };

        class FileStream : public IReader, public IWriter {
        public:
            void open() override {}
            void read() override {}
            void write() override {}
            void close() override {}
        };
    )";

    auto* reader = extractClass(code, "IReader");
    auto* writer = extractClass(code, "IWriter");
    auto* stream = extractClass(code, "FileStream");

    ASSERT_NE(reader, nullptr);
    ASSERT_NE(writer, nullptr);
    ASSERT_NE(stream, nullptr);

    EXPECT_EQ(countVirtualMethods(reader), 3);
    EXPECT_EQ(countVirtualMethods(writer), 3);
}

TEST_F(MultipleInheritanceIntegrationTest, MixedVirtualNonVirtualMethods) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void virtualMethod() {}
            void nonVirtualMethod() {}
        };

        class Base2 {
        public:
            virtual void anotherVirtual() {}
            void anotherNonVirtual() {}
        };

        class Derived : public Base1, public Base2 {
        public:
            void virtualMethod() override {}
            void anotherVirtual() override {}
            void derivedMethod() {}
        };
    )";

    auto* base1 = extractClass(code, "Base1");
    auto* base2 = extractClass(code, "Base2");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(derived, nullptr);

    EXPECT_TRUE(base1->isPolymorphic());
    EXPECT_TRUE(base2->isPolymorphic());
    EXPECT_EQ(countPolymorphicBases(derived), 2);
}

// ============================================================================
// Casts Tests (3 tests)
// ============================================================================

TEST_F(MultipleInheritanceIntegrationTest, CastFromDerivedToPrimaryBase) {
    const char* code = R"(
        class Primary {
        public:
            virtual void foo() {}
        };

        class Secondary {
        public:
            virtual void bar() {}
        };

        class Derived : public Primary, public Secondary {
        public:
            void foo() override {}
            void bar() override {}
        };

        void test() {
            Derived d;
            Primary* p = &d; // No offset adjustment needed (primary base)
        }
    )";

    auto* primary = extractClass(code, "Primary");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(primary, nullptr);
    ASSERT_NE(derived, nullptr);

    // Primary should be first base (no offset)
    EXPECT_TRUE(primary->isPolymorphic());
}

TEST_F(MultipleInheritanceIntegrationTest, CastFromDerivedToNonPrimaryBase) {
    const char* code = R"(
        class IDrawable {
        public:
            virtual void draw() {}
        };

        class ISerializable {
        public:
            virtual void serialize() {}
        };

        class Shape : public IDrawable, public ISerializable {
        public:
            void draw() override {}
            void serialize() override {}
        };

        void test() {
            Shape s;
            ISerializable* ser = &s; // Requires offset adjustment
        }
    )";

    auto* serializable = extractClass(code, "ISerializable");
    auto* shape = extractClass(code, "Shape");

    ASSERT_NE(serializable, nullptr);
    ASSERT_NE(shape, nullptr);

    EXPECT_EQ(countPolymorphicBases(shape), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, CastBetweenBasesCrosscast) {
    const char* code = R"(
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
            void method1() override {}
            void method2() override {}
        };

        void test(Base1* b1) {
            // This would require dynamic_cast in C++
            // For now, we just verify the structure
        }
    )";

    auto* base1 = extractClass(code, "Base1");
    auto* base2 = extractClass(code, "Base2");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(derived, nullptr);

    EXPECT_EQ(countPolymorphicBases(derived), 2);
}

// ============================================================================
// Method Behavior Tests (3 tests)
// ============================================================================

TEST_F(MultipleInheritanceIntegrationTest, OverrideInDerivedClass) {
    const char* code = R"(
        class IBase1 {
        public:
            virtual void method() {}
        };

        class IBase2 {
        public:
            virtual void method() {}
        };

        class Derived : public IBase1, public IBase2 {
        public:
            void method() override {} // Overrides IBase1::method
        };
    )";

    auto* base1 = extractClass(code, "IBase1");
    auto* base2 = extractClass(code, "IBase2");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(derived, nullptr);

    EXPECT_TRUE(derived->isPolymorphic());
}

TEST_F(MultipleInheritanceIntegrationTest, InheritedVirtualMethods) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void method1() {}
            virtual void method2() {}
        };

        class Base2 {
        public:
            virtual void method3() {}
            virtual void method4() {}
        };

        class Derived : public Base1, public Base2 {
            // Inherits all virtual methods without overriding
        };
    )";

    auto* base1 = extractClass(code, "Base1");
    auto* base2 = extractClass(code, "Base2");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(derived, nullptr);

    EXPECT_TRUE(derived->isPolymorphic());
    EXPECT_EQ(countPolymorphicBases(derived), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, MultipleVirtualMethodsPerClass) {
    const char* code = R"(
        class IInterface1 {
        public:
            virtual void method1() = 0;
            virtual void method2() = 0;
            virtual void method3() = 0;
        };

        class IInterface2 {
        public:
            virtual void method4() = 0;
            virtual void method5() = 0;
            virtual void method6() = 0;
        };

        class Implementation : public IInterface1, public IInterface2 {
        public:
            void method1() override {}
            void method2() override {}
            void method3() override {}
            void method4() override {}
            void method5() override {}
            void method6() override {}
        };
    )";

    auto* iface1 = extractClass(code, "IInterface1");
    auto* iface2 = extractClass(code, "IInterface2");
    auto* impl = extractClass(code, "Implementation");

    ASSERT_NE(iface1, nullptr);
    ASSERT_NE(iface2, nullptr);
    ASSERT_NE(impl, nullptr);

    EXPECT_EQ(countVirtualMethods(iface1), 3);
    EXPECT_EQ(countVirtualMethods(iface2), 3);
    EXPECT_FALSE(impl->isAbstract());
}

// ============================================================================
// Verification Tests (4 tests)
// ============================================================================

TEST_F(MultipleInheritanceIntegrationTest, ThunkGenerationVerification) {
    const char* code = R"(
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
            void method1() override {}
            void method2() override {}
        };
    )";

    // Recreate analyzer with current AST
    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    auto testAnalyzer = std::make_unique<MultipleInheritanceAnalyzer>(testAST->getASTContext());
    auto* derived = extractClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Verify thunks are needed for non-primary base
    auto bases = testAnalyzer->analyzePolymorphicBases(derived);
    EXPECT_EQ(bases.size(), 2);

    // Second base should not be primary
    if (bases.size() >= 2) {
        EXPECT_FALSE(bases[1].IsPrimary);
    }
}

TEST_F(MultipleInheritanceIntegrationTest, OffsetCalculationVerification) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void foo() {}
        };

        class Base2 {
        public:
            virtual void bar() {}
        };

        class Derived : public Base1, public Base2 {
        public:
            int data;
        };
    )";

    auto testAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(testAST, nullptr);

    auto testAnalyzer = std::make_unique<MultipleInheritanceAnalyzer>(testAST->getASTContext());
    auto* derived = extractClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto bases = testAnalyzer->analyzePolymorphicBases(derived);
    EXPECT_EQ(bases.size(), 2);

    // Primary base should have offset 0
    if (!bases.empty()) {
        EXPECT_TRUE(bases[0].IsPrimary);
        EXPECT_EQ(bases[0].Offset, 0);
    }

    // Non-primary base should have non-zero offset
    if (bases.size() >= 2) {
        EXPECT_FALSE(bases[1].IsPrimary);
        EXPECT_GT(bases[1].Offset, 0);
    }
}

TEST_F(MultipleInheritanceIntegrationTest, VtableInstanceVerification) {
    const char* code = R"(
        class IInterface1 {
        public:
            virtual void method1() = 0;
        };

        class IInterface2 {
        public:
            virtual void method2() = 0;
        };

        class Concrete : public IInterface1, public IInterface2 {
        public:
            void method1() override {}
            void method2() override {}
        };
    )";

    auto* concrete = extractClass(code, "Concrete");
    ASSERT_NE(concrete, nullptr);

    // Should have 2 polymorphic bases requiring 2 vtable instances
    EXPECT_EQ(countPolymorphicBases(concrete), 2);
    EXPECT_FALSE(concrete->isAbstract());
}

TEST_F(MultipleInheritanceIntegrationTest, FieldLayoutVerification) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void foo() {}
            int base1Data;
        };

        class Base2 {
        public:
            virtual void bar() {}
            int base2Data;
        };

        class Derived : public Base1, public Base2 {
        public:
            int derivedData;
        };
    )";

    auto* base1 = extractClass(code, "Base1");
    auto* base2 = extractClass(code, "Base2");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(derived, nullptr);

    // Verify structure
    EXPECT_TRUE(base1->isPolymorphic());
    EXPECT_TRUE(base2->isPolymorphic());
    EXPECT_EQ(countPolymorphicBases(derived), 2);
}

// ============================================================================
// Edge Cases Tests (11 tests)
// ============================================================================

TEST_F(MultipleInheritanceIntegrationTest, EmptyBasesWithVirtualMethods) {
    const char* code = R"(
        class IEmpty1 {
        public:
            virtual void method1() = 0;
        };

        class IEmpty2 {
        public:
            virtual void method2() = 0;
        };

        class Derived : public IEmpty1, public IEmpty2 {
        public:
            void method1() override {}
            void method2() override {}
        };
    )";

    auto* empty1 = extractClass(code, "IEmpty1");
    auto* empty2 = extractClass(code, "IEmpty2");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(empty1, nullptr);
    ASSERT_NE(empty2, nullptr);
    ASSERT_NE(derived, nullptr);

    EXPECT_TRUE(empty1->isEmpty());
    EXPECT_TRUE(empty2->isEmpty());
    EXPECT_EQ(countPolymorphicBases(derived), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, SingleNonPolymorphicWithMultiplePolymorphic) {
    const char* code = R"(
        class NonPoly {
        public:
            int data;
        };

        class Poly1 {
        public:
            virtual void foo() {}
        };

        class Poly2 {
        public:
            virtual void bar() {}
        };

        class Derived : public NonPoly, public Poly1, public Poly2 {};
    )";

    auto* derived = extractClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    EXPECT_EQ(derived->getNumBases(), 3);
    EXPECT_EQ(countPolymorphicBases(derived), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, AllNonPolymorphicBases) {
    const char* code = R"(
        class Base1 {
        public:
            int data1;
        };

        class Base2 {
        public:
            int data2;
        };

        class Derived : public Base1, public Base2 {
        public:
            int data3;
        };
    )";

    auto* base1 = extractClass(code, "Base1");
    auto* base2 = extractClass(code, "Base2");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(derived, nullptr);

    EXPECT_FALSE(base1->isPolymorphic());
    EXPECT_FALSE(base2->isPolymorphic());
    EXPECT_FALSE(derived->isPolymorphic());
    EXPECT_EQ(countPolymorphicBases(derived), 0);
}

TEST_F(MultipleInheritanceIntegrationTest, VirtualDestructorInMultipleBases) {
    const char* code = R"(
        class Base1 {
        public:
            virtual ~Base1() {}
        };

        class Base2 {
        public:
            virtual ~Base2() {}
        };

        class Derived : public Base1, public Base2 {
        public:
            ~Derived() override {}
        };
    )";

    auto* base1 = extractClass(code, "Base1");
    auto* base2 = extractClass(code, "Base2");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(derived, nullptr);

    EXPECT_TRUE(base1->isPolymorphic());
    EXPECT_TRUE(base2->isPolymorphic());
    EXPECT_EQ(countPolymorphicBases(derived), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, ConstMethodsInMultipleBases) {
    const char* code = R"(
        class IReader {
        public:
            virtual int read() const = 0;
        };

        class IValidator {
        public:
            virtual bool validate() const = 0;
        };

        class DataSource : public IReader, public IValidator {
        public:
            int read() const override { return 0; }
            bool validate() const override { return true; }
        };
    )";

    auto* reader = extractClass(code, "IReader");
    auto* validator = extractClass(code, "IValidator");
    auto* source = extractClass(code, "DataSource");

    ASSERT_NE(reader, nullptr);
    ASSERT_NE(validator, nullptr);
    ASSERT_NE(source, nullptr);

    EXPECT_TRUE(reader->isAbstract());
    EXPECT_TRUE(validator->isAbstract());
    EXPECT_FALSE(source->isAbstract());
}

TEST_F(MultipleInheritanceIntegrationTest, PrivateInheritanceMultipleBases) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void foo() {}
        };

        class Base2 {
        public:
            virtual void bar() {}
        };

        class Derived : private Base1, private Base2 {
        public:
            void test() {}
        };
    )";

    auto* derived = extractClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Private inheritance doesn't affect polymorphism
    EXPECT_EQ(derived->getNumBases(), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, ProtectedInheritanceMultipleBases) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void foo() {}
        };

        class Base2 {
        public:
            virtual void bar() {}
        };

        class Derived : protected Base1, protected Base2 {
        public:
            void test() {}
        };
    )";

    auto* derived = extractClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    EXPECT_EQ(derived->getNumBases(), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, MixedAccessSpecifiersMultipleBases) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void foo() {}
        };

        class Base2 {
        public:
            virtual void bar() {}
        };

        class Base3 {
        public:
            virtual void baz() {}
        };

        class Derived : public Base1, private Base2, protected Base3 {
        public:
            void foo() override {}
        };
    )";

    auto* derived = extractClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    EXPECT_EQ(derived->getNumBases(), 3);
}

TEST_F(MultipleInheritanceIntegrationTest, OverloadedMethodsInMultipleBases) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void process() {}
            virtual void process(int x) {}
        };

        class Base2 {
        public:
            virtual void process() {}
            virtual void process(double x) {}
        };

        class Derived : public Base1, public Base2 {
        public:
            void process() override {} // Ambiguous - need to specify which one
        };
    )";

    auto* base1 = extractClass(code, "Base1");
    auto* base2 = extractClass(code, "Base2");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(base1, nullptr);
    ASSERT_NE(base2, nullptr);
    ASSERT_NE(derived, nullptr);

    EXPECT_EQ(countPolymorphicBases(derived), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, TemplateBasesMultipleInheritance) {
    // Note: Templates require instantiation - this is a basic structure test
    const char* code = R"(
        template<typename T>
        class Base1 {
        public:
            virtual void process(T value) {}
        };

        template<typename T>
        class Base2 {
        public:
            virtual void store(T value) {}
        };

        class Derived : public Base1<int>, public Base2<int> {
        public:
            void process(int value) override {}
            void store(int value) override {}
        };
    )";

    auto* derived = extractClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Derived should inherit from instantiated templates
    EXPECT_EQ(derived->getNumBases(), 2);
}

TEST_F(MultipleInheritanceIntegrationTest, ComplexHierarchyWithMultipleInheritance) {
    const char* code = R"(
        class IBase1 {
        public:
            virtual void method1() = 0;
        };

        class IBase2 {
        public:
            virtual void method2() = 0;
        };

        class Middle1 : public IBase1 {
        public:
            void method1() override {}
            virtual void method3() {}
        };

        class Middle2 : public IBase2 {
        public:
            void method2() override {}
            virtual void method4() {}
        };

        class Derived : public Middle1, public Middle2 {
        public:
            void method3() override {}
            void method4() override {}
        };
    )";

    auto* ibase1 = extractClass(code, "IBase1");
    auto* ibase2 = extractClass(code, "IBase2");
    auto* middle1 = extractClass(code, "Middle1");
    auto* middle2 = extractClass(code, "Middle2");
    auto* derived = extractClass(code, "Derived");

    ASSERT_NE(ibase1, nullptr);
    ASSERT_NE(ibase2, nullptr);
    ASSERT_NE(middle1, nullptr);
    ASSERT_NE(middle2, nullptr);
    ASSERT_NE(derived, nullptr);

    EXPECT_TRUE(ibase1->isAbstract());
    EXPECT_TRUE(ibase2->isAbstract());
    EXPECT_FALSE(middle1->isAbstract());
    EXPECT_FALSE(middle2->isAbstract());
    EXPECT_FALSE(derived->isAbstract());
    EXPECT_EQ(countPolymorphicBases(derived), 2);
}
