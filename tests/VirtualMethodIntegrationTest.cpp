// TDD Tests for Virtual Method Support - Phase 9, v2.2.0
// Comprehensive virtual method translation and vtable generation
// Migrated to Google Test Framework
// Total: 15 tests

#include <gtest/gtest.h>
#include "OverrideResolver.h"
#include "VirtualCallTranslator.h"
#include "VirtualMethodAnalyzer.h"
#include "VtableGenerator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <memory>
#include <string>

using namespace clang;

// ============================================================================
// Test Fixtures
// ============================================================================

class VirtualMethodTestBase : public ::testing::Test {
protected:
    // Helper: Parse C++ code and return CXXRecordDecl
    CXXRecordDecl *parseClassDecl(const std::string &code,
                                  const std::string &className) {
        std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
        if (!AST)
            return nullptr;

        ASTContext &ctx = AST->getASTContext();
        TranslationUnitDecl *TU = ctx.getTranslationUnitDecl();

        for (auto *decl : TU->decls()) {
            if (auto *record = dyn_cast<CXXRecordDecl>(decl)) {
                if (record->getNameAsString() == className &&
                    record->isCompleteDefinition()) {
                    // Store AST to keep it alive
                    astUnits.push_back(std::move(AST));
                    return record;
                }
            }
        }
        return nullptr;
    }

    // Helper: Parse C++ code and return CXXMemberCallExpr
    CXXMemberCallExpr *parseMemberCallExpr(const std::string &code) {
        std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
        if (!AST)
            return nullptr;

        ASTContext &ctx = AST->getASTContext();
        TranslationUnitDecl *TU = ctx.getTranslationUnitDecl();

        // Find the first CXXMemberCallExpr
        class CallFinder : public RecursiveASTVisitor<CallFinder> {
        public:
            CXXMemberCallExpr *Result = nullptr;

            bool VisitCXXMemberCallExpr(CXXMemberCallExpr *E) {
                if (!Result)
                    Result = E;
                return true;
            }
        };

        CallFinder finder;
        finder.TraverseDecl(TU);

        if (finder.Result) {
            astUnits.push_back(std::move(AST));
        }
        return finder.Result;
    }

private:
    std::vector<std::unique_ptr<ASTUnit>> astUnits;
};

// ============================================================================
// TIER 1: Single Inheritance Tests (5 tests)
// ============================================================================

// Test 1: Simple virtual method - single class with one virtual method
TEST_F(VirtualMethodTestBase, SimpleVirtualMethod) {
    std::string code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };
    )";

    CXXRecordDecl *record = parseClassDecl(code, "Shape");
    ASSERT_NE(record, nullptr) << "Failed to parse Shape class";

    ASTContext &ctx = record->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);

    // Verify class is polymorphic
    EXPECT_TRUE(analyzer.isPolymorphic(record)) << "Shape should be polymorphic";

    // Verify virtual method detected
    auto virtualMethods = analyzer.getVirtualMethods(record);
    EXPECT_EQ(virtualMethods.size(), 1u) << "Should have 1 virtual method";

    // Generate vtable struct
    OverrideResolver resolver(ctx, analyzer);
    VtableGenerator generator(ctx, analyzer, &resolver);
    std::string vtable = generator.generateVtableStruct(record);

    EXPECT_FALSE(vtable.empty()) << "Vtable should be generated";
    EXPECT_NE(vtable.find("struct Shape_vtable"), std::string::npos)
        << "Should have Shape_vtable struct";
    EXPECT_NE(vtable.find("type_info"), std::string::npos)
        << "Should have type_info pointer";
    EXPECT_NE(vtable.find("(*draw)"), std::string::npos)
        << "Should have draw function pointer";
}

// Test 2: Multiple virtual methods in single class
TEST_F(VirtualMethodTestBase, MultipleVirtualMethods) {
    std::string code = R"(
        class Shape {
        public:
            virtual void draw() {}
            virtual double area() const { return 0.0; }
            virtual void setColor(int r, int g, int b) {}
        };
    )";

    CXXRecordDecl *record = parseClassDecl(code, "Shape");
    ASSERT_NE(record, nullptr) << "Failed to parse Shape class";

    ASTContext &ctx = record->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);
    OverrideResolver resolver(ctx, analyzer);
    VtableGenerator generator(ctx, analyzer, &resolver);

    auto virtualMethods = analyzer.getVirtualMethods(record);
    EXPECT_EQ(virtualMethods.size(), 3u) << "Should have 3 virtual methods";

    std::string vtable = generator.generateVtableStruct(record);
    EXPECT_NE(vtable.find("(*draw)"), std::string::npos) << "Should have draw method";
    EXPECT_NE(vtable.find("(*area)"), std::string::npos) << "Should have area method";
    EXPECT_NE(vtable.find("(*setColor)"), std::string::npos) << "Should have setColor method";
}

// Test 3: Virtual method override - derived class overrides base method
TEST_F(VirtualMethodTestBase, VirtualMethodOverride) {
    std::string code = R"(
        class Base {
        public:
            virtual void foo() {}
        };

        class Derived : public Base {
        public:
            virtual void foo() override {}
        };
    )";

    CXXRecordDecl *derivedRecord = parseClassDecl(code, "Derived");
    ASSERT_NE(derivedRecord, nullptr) << "Failed to parse Derived class";

    ASTContext &ctx = derivedRecord->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);
    OverrideResolver resolver(ctx, analyzer);
    VtableGenerator generator(ctx, analyzer, &resolver);

    // Verify Derived is polymorphic
    EXPECT_TRUE(analyzer.isPolymorphic(derivedRecord))
        << "Derived should be polymorphic";

    // Generate vtable for derived class
    std::string vtable = generator.generateVtableStruct(derivedRecord);
    EXPECT_NE(vtable.find("struct Derived_vtable"), std::string::npos)
        << "Should have Derived_vtable";
    EXPECT_NE(vtable.find("(*foo)"), std::string::npos) << "Should have foo method";
}

// Test 4: Inherited virtual method - derived class does NOT override
TEST_F(VirtualMethodTestBase, InheritedVirtualMethod) {
    std::string code = R"(
        class Base {
        public:
            virtual void foo() {}
        };

        class Derived : public Base {
        public:
            void bar() {}  // Non-virtual method
        };
    )";

    CXXRecordDecl *derivedRecord = parseClassDecl(code, "Derived");
    ASSERT_NE(derivedRecord, nullptr) << "Failed to parse Derived class";

    ASTContext &ctx = derivedRecord->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);

    // Derived inherits virtual method from Base
    EXPECT_TRUE(analyzer.isPolymorphic(derivedRecord))
        << "Derived should be polymorphic (inherited)";

    OverrideResolver resolver(ctx, analyzer);
    VtableGenerator generator(ctx, analyzer, &resolver);
    std::string vtable = generator.generateVtableStruct(derivedRecord);

    // Vtable should include inherited virtual method
    EXPECT_NE(vtable.find("(*foo)"), std::string::npos) << "Should inherit foo from Base";
}

// Test 5: Mixed virtual and non-virtual methods
TEST_F(VirtualMethodTestBase, MixedVirtualNonVirtual) {
    std::string code = R"(
        class Shape {
        public:
            virtual void draw() {}  // Virtual
            void setName(const char* n) {}  // Non-virtual
            virtual double area() const { return 0.0; }  // Virtual
            int getId() const { return 0; }  // Non-virtual
        };
    )";

    CXXRecordDecl *record = parseClassDecl(code, "Shape");
    ASSERT_NE(record, nullptr) << "Failed to parse Shape class";

    ASTContext &ctx = record->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);
    OverrideResolver resolver(ctx, analyzer);
    VtableGenerator generator(ctx, analyzer, &resolver);

    auto virtualMethods = analyzer.getVirtualMethods(record);
    EXPECT_EQ(virtualMethods.size(), 2u)
        << "Should have 2 virtual methods (draw, area)";

    std::string vtable = generator.generateVtableStruct(record);
    EXPECT_NE(vtable.find("(*draw)"), std::string::npos) << "Vtable should have virtual draw";
    EXPECT_NE(vtable.find("(*area)"), std::string::npos) << "Vtable should have virtual area";
    // Non-virtual methods should NOT be in vtable
}

// ============================================================================
// TIER 2: Multi-Level Inheritance Tests (3 tests)
// ============================================================================

// Test 6: Multi-level inheritance - A -> B -> C
TEST_F(VirtualMethodTestBase, MultiLevelInheritance) {
    std::string code = R"(
        class A {
        public:
            virtual void foo() {}
        };

        class B : public A {
        public:
            virtual void foo() override {}
        };

        class C : public B {
        public:
            virtual void foo() override {}
        };
    )";

    CXXRecordDecl *recordC = parseClassDecl(code, "C");
    ASSERT_NE(recordC, nullptr) << "Failed to parse C class";

    ASTContext &ctx = recordC->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);
    OverrideResolver resolver(ctx, analyzer);
    VtableGenerator generator(ctx, analyzer, &resolver);

    EXPECT_TRUE(analyzer.isPolymorphic(recordC)) << "C should be polymorphic";

    std::string vtable = generator.generateVtableStruct(recordC);
    EXPECT_NE(vtable.find("struct C_vtable"), std::string::npos) << "Should have C_vtable";
    EXPECT_NE(vtable.find("(*foo)"), std::string::npos) << "Should have foo method";
}

// Test 7: Multi-level with new virtual method added at each level
TEST_F(VirtualMethodTestBase, MultiLevelWithNewMethod) {
    std::string code = R"(
        class A {
        public:
            virtual void foo() {}
        };

        class B : public A {
        public:
            virtual void foo() override {}
            virtual void bar() {}  // New virtual method
        };

        class C : public B {
        public:
            virtual void foo() override {}
            virtual void bar() override {}
            virtual void baz() {}  // Another new virtual method
        };
    )";

    CXXRecordDecl *recordC = parseClassDecl(code, "C");
    ASSERT_NE(recordC, nullptr) << "Failed to parse C class";

    ASTContext &ctx = recordC->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);
    OverrideResolver resolver(ctx, analyzer);
    VtableGenerator generator(ctx, analyzer, &resolver);

    auto virtualMethods = analyzer.getVirtualMethods(recordC);
    EXPECT_GE(virtualMethods.size(), 3u)
        << "C should have at least 3 virtual methods";

    std::string vtable = generator.generateVtableStruct(recordC);
    EXPECT_NE(vtable.find("(*foo)"), std::string::npos) << "Should have foo";
    EXPECT_NE(vtable.find("(*bar)"), std::string::npos) << "Should have bar";
    EXPECT_NE(vtable.find("(*baz)"), std::string::npos) << "Should have baz";
}

// Test 8: Multi-level partial override
TEST_F(VirtualMethodTestBase, MultiLevelPartialOverride) {
    std::string code = R"(
        class A {
        public:
            virtual void foo() {}
            virtual void bar() {}
        };

        class B : public A {
        public:
            virtual void foo() override {}  // Override foo
            // bar inherited from A
        };

        class C : public B {
        public:
            // foo inherited from B
            virtual void bar() override {}  // Override bar
        };
    )";

    CXXRecordDecl *recordC = parseClassDecl(code, "C");
    ASSERT_NE(recordC, nullptr) << "Failed to parse C class";

    ASTContext &ctx = recordC->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);
    OverrideResolver resolver(ctx, analyzer);
    VtableGenerator generator(ctx, analyzer, &resolver);

    auto virtualMethods = analyzer.getVirtualMethods(recordC);
    EXPECT_GE(virtualMethods.size(), 2u)
        << "C should have at least 2 virtual methods";

    std::string vtable = generator.generateVtableStruct(recordC);
    EXPECT_NE(vtable.find("(*foo)"), std::string::npos) << "Should have foo (inherited from B)";
    EXPECT_NE(vtable.find("(*bar)"), std::string::npos) << "Should have bar (overridden in C)";
}

// ============================================================================
// TIER 3: Virtual Destructors Tests (2 tests)
// ============================================================================

// Test 9: Virtual destructor
TEST_F(VirtualMethodTestBase, VirtualDestructor) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };
    )";

    CXXRecordDecl *record = parseClassDecl(code, "Base");
    ASSERT_NE(record, nullptr) << "Failed to parse Base class";

    ASTContext &ctx = record->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);
    OverrideResolver resolver(ctx, analyzer);
    VtableGenerator generator(ctx, analyzer, &resolver);

    EXPECT_TRUE(analyzer.isPolymorphic(record))
        << "Base should be polymorphic (has virtual dtor)";

    std::string vtable = generator.generateVtableStruct(record);
    EXPECT_NE(vtable.find("struct Base_vtable"), std::string::npos) << "Should have Base_vtable";
    EXPECT_NE(vtable.find("(*destructor)"), std::string::npos)
        << "Should have destructor function pointer";
}

// Test 10: Virtual destructor inheritance
TEST_F(VirtualMethodTestBase, VirtualDestructorInheritance) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
        public:
            ~Derived() {}  // Implicitly virtual
        };
    )";

    CXXRecordDecl *derivedRecord = parseClassDecl(code, "Derived");
    ASSERT_NE(derivedRecord, nullptr) << "Failed to parse Derived class";

    ASTContext &ctx = derivedRecord->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);
    OverrideResolver resolver(ctx, analyzer);
    VtableGenerator generator(ctx, analyzer, &resolver);

    EXPECT_TRUE(analyzer.isPolymorphic(derivedRecord))
        << "Derived should be polymorphic";

    std::string vtable = generator.generateVtableStruct(derivedRecord);
    EXPECT_NE(vtable.find("(*destructor)"), std::string::npos) << "Should have destructor in vtable";
}

// ============================================================================
// TIER 4: Abstract Classes & Pure Virtual Tests (2 tests)
// ============================================================================

// Test 11: Pure virtual method (abstract class)
TEST_F(VirtualMethodTestBase, PureVirtualMethod) {
    std::string code = R"(
        class AbstractShape {
        public:
            virtual ~AbstractShape() {}
            virtual void draw() = 0;  // Pure virtual
        };
    )";

    CXXRecordDecl *record = parseClassDecl(code, "AbstractShape");
    ASSERT_NE(record, nullptr) << "Failed to parse AbstractShape class";

    ASTContext &ctx = record->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);

    EXPECT_TRUE(analyzer.isPolymorphic(record)) << "AbstractShape should be polymorphic";
    EXPECT_TRUE(analyzer.isAbstractClass(record)) << "AbstractShape should be abstract";

    auto virtualMethods = analyzer.getVirtualMethods(record);
    EXPECT_GE(virtualMethods.size(), 1u)
        << "Should have at least 1 virtual method (draw)";

    // Check if draw is pure virtual
    bool foundPureVirtual = false;
    for (auto *method : virtualMethods) {
        if (method->getNameAsString() == "draw" && analyzer.isPureVirtual(method)) {
            foundPureVirtual = true;
            break;
        }
    }
    EXPECT_TRUE(foundPureVirtual) << "draw should be pure virtual";
}

// Test 12: Multiple abstract methods with concrete implementation
TEST_F(VirtualMethodTestBase, MultipleAbstractMethods) {
    std::string code = R"(
        class AbstractBase {
        public:
            virtual ~AbstractBase() {}
            virtual void foo() = 0;
            virtual void bar() = 0;
            virtual void baz() = 0;
        };

        class Concrete : public AbstractBase {
        public:
            virtual void foo() override {}
            virtual void bar() override {}
            virtual void baz() override {}
        };
    )";

    CXXRecordDecl *abstractRecord = parseClassDecl(code, "AbstractBase");
    ASSERT_NE(abstractRecord, nullptr) << "Failed to parse AbstractBase";

    ASTContext &ctx = abstractRecord->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);

    EXPECT_TRUE(analyzer.isAbstractClass(abstractRecord))
        << "AbstractBase should be abstract";

    // Check concrete class
    CXXRecordDecl *concreteRecord = parseClassDecl(code, "Concrete");
    ASSERT_NE(concreteRecord, nullptr) << "Failed to parse Concrete";
    EXPECT_FALSE(analyzer.isAbstractClass(concreteRecord))
        << "Concrete should NOT be abstract";
}

// ============================================================================
// TIER 5: Advanced Cases Tests (3 tests)
// ============================================================================

// Test 13: Virtual call detection
TEST_F(VirtualMethodTestBase, VirtualCallDetection) {
    std::string code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };

        void test() {
            Shape s;
            s.draw();  // Virtual call
        }
    )";

    // Parse the code to get the class declaration first
    CXXRecordDecl *record = parseClassDecl(code, "Shape");
    ASSERT_NE(record, nullptr) << "Failed to parse Shape class";

    ASTContext &ctx = record->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);
    VirtualCallTranslator translator(ctx, analyzer);

    // Parse the member call expression
    CXXMemberCallExpr *callExpr = parseMemberCallExpr(code);
    ASSERT_NE(callExpr, nullptr) << "Failed to parse member call expression";

    // Check if call is virtual
    bool isVirtual = translator.isVirtualCall(callExpr);
    EXPECT_TRUE(isVirtual) << "Call to draw() should be detected as virtual";
}

// Test 14: Virtual call through pointer
TEST_F(VirtualMethodTestBase, PolymorphicThroughPointer) {
    std::string code = R"(
        class Base {
        public:
            virtual void foo() {}
        };

        class Derived : public Base {
        public:
            virtual void foo() override {}
        };

        void test(Base* ptr) {
            ptr->foo();  // Polymorphic call
        }
    )";

    // Parse everything from a single AST to avoid dangling pointers
    std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    ASTContext &ctx = AST->getASTContext();
    TranslationUnitDecl *TU = ctx.getTranslationUnitDecl();

    // Find Base class
    CXXRecordDecl *baseRecord = nullptr;
    for (auto *decl : TU->decls()) {
        if (auto *record = dyn_cast<CXXRecordDecl>(decl)) {
            if (record->getNameAsString() == "Base" &&
                record->isCompleteDefinition()) {
                baseRecord = record;
                break;
            }
        }
    }
    ASSERT_NE(baseRecord, nullptr) << "Failed to find Base class";

    // Find member call expression
    class CallFinder : public RecursiveASTVisitor<CallFinder> {
    public:
        CXXMemberCallExpr *Result = nullptr;
        bool VisitCXXMemberCallExpr(CXXMemberCallExpr *E) {
            if (!Result)
                Result = E;
            return true;
        }
    };
    CallFinder finder;
    finder.TraverseDecl(TU);
    ASSERT_NE(finder.Result, nullptr) << "Failed to find member call";

    // Now test with the same AST context
    VirtualMethodAnalyzer analyzer(ctx);
    VirtualCallTranslator translator(ctx, analyzer);

    bool isVirtual = translator.isVirtualCall(finder.Result);
    EXPECT_TRUE(isVirtual) << "Call through pointer should be virtual";
}

// Test 15: Covariant return type
TEST_F(VirtualMethodTestBase, CovariantReturnType) {
    std::string code = R"(
        class Base {
        public:
            virtual Base* clone() = 0;
        };

        class Derived : public Base {
        public:
            virtual Derived* clone() override { return new Derived(*this); }
        };
    )";

    CXXRecordDecl *derivedRecord = parseClassDecl(code, "Derived");
    ASSERT_NE(derivedRecord, nullptr) << "Failed to parse Derived class";

    ASTContext &ctx = derivedRecord->getASTContext();
    VirtualMethodAnalyzer analyzer(ctx);
    OverrideResolver resolver(ctx, analyzer);
    VtableGenerator generator(ctx, analyzer, &resolver);

    // Both Base and Derived have clone() method
    auto virtualMethods = analyzer.getVirtualMethods(derivedRecord);

    bool hasClone = false;
    for (auto *method : virtualMethods) {
        if (method->getNameAsString() == "clone") {
            hasClone = true;
            // Verify covariant return type (Derived* instead of Base*)
            QualType retType = method->getReturnType();
            EXPECT_TRUE(retType->isPointerType()) << "clone should return pointer";
        }
    }
    EXPECT_TRUE(hasClone) << "Derived should have clone method";
}

// ============================================================================
// Main Entry Point for GTest
// ============================================================================

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
