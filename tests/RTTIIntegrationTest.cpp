/**
 * @file RTTIIntegrationTest.cpp
 * @brief Integration test suite for RTTI features (Phase 13, v2.6.0)
 *
 * Tests the integration of VisitCXXTypeidExpr and VisitCXXDynamicCastExpr
 * with TypeidTranslator and DynamicCastTranslator in the CppToCVisitor.
 *
 * This file tests end-to-end RTTI translation from C++ AST to C code.
 *
 * SOLID Principles:
 * - Single Responsibility: Tests only RTTI integration
 * - Interface Segregation: Tests public API only
 * - Dependency Inversion: Uses abstract AST interfaces
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/CppToCVisitor.h"
#include "../include/TypeidTranslator.h"
#include "../include/DynamicCastTranslator.h"
#include "../include/TypeInfoGenerator.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/CNodeBuilder.h"
#include <cassert>
#include <sstream>
#include <vector>

using namespace clang;

// Test helper macros
    if (!(cond)) { \
        TEST_FAIL("", msg); \
    }

/**
 * @brief Build AST from C++ code snippet
 */
std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

/**
 * @brief Helper to find first CXXTypeidExpr in AST
 */
const CXXTypeidExpr* findTypeidExpr(ASTContext& Context) {
    class TypeidFinder : public RecursiveASTVisitor<TypeidFinder> {
    public:
        const CXXTypeidExpr* Found = nullptr;
        bool VisitCXXTypeidExpr(CXXTypeidExpr* E) {
            if (!Found) Found = E;
            return true;
        }
    };
    TypeidFinder Finder;
    Finder.TraverseDecl(Context.getTranslationUnitDecl());
    return Finder.Found;
}

/**
 * @brief Helper to find all CXXTypeidExpr in AST
 */
std::vector<const CXXTypeidExpr*> findAllTypeidExprs(ASTContext& Context) {
    class TypeidFinder : public RecursiveASTVisitor<TypeidFinder> {
    public:
        std::vector<const CXXTypeidExpr*> Found;
        bool VisitCXXTypeidExpr(CXXTypeidExpr* E) {
            Found.push_back(E);
            return true;
        }
    };
    TypeidFinder Finder;
    Finder.TraverseDecl(Context.getTranslationUnitDecl());
    return Finder.Found;
}

/**
 * @brief Helper to find first CXXDynamicCastExpr in AST
 */
const CXXDynamicCastExpr* findDynamicCastExpr(ASTContext& Context) {
    class DynamicCastFinder : public RecursiveASTVisitor<DynamicCastFinder> {
    public:
        const CXXDynamicCastExpr* Found = nullptr;
        bool VisitCXXDynamicCastExpr(CXXDynamicCastExpr* E) {
            if (!Found) Found = E;
            return true;
        }
    };
    DynamicCastFinder Finder;
    Finder.TraverseDecl(Context.getTranslationUnitDecl());
    return Finder.Found;
}

/**
 * @brief Helper to find all CXXDynamicCastExpr in AST
 */
std::vector<const CXXDynamicCastExpr*> findAllDynamicCastExprs(ASTContext& Context) {
    class DynamicCastFinder : public RecursiveASTVisitor<DynamicCastFinder> {
    public:
        std::vector<const CXXDynamicCastExpr*> Found;
        bool VisitCXXDynamicCastExpr(CXXDynamicCastExpr* E) {
            Found.push_back(E);
            return true;
        }
    };
    DynamicCastFinder Finder;
    Finder.TraverseDecl(Context.getTranslationUnitDecl());
    return Finder.Found;
}

// ============================================================================
// Category 1: Typeid Basic Tests (3 tests)
// ============================================================================

/**
 * Test 1: Static typeid on non-polymorphic class
 * Verifies direct reference to __ti_ClassName
 */

// Test fixture
class RTTIIntegrationTest : public ::testing::Test {
protected:
};

TEST_F(RTTIIntegrationTest, Static typeid on non-polymorphic class) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Animal {
            public:
                virtual ~Animal() {}
            };

            void test_typeid_static() {
                const std::type_info& ti = typeid(Animal);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        TypeidTranslator Translator(Context, Analyzer);

        const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
        ASSERT_TRUE(typeidExpr != nullptr) << "typeid expression not found";

        // Verify it's a static typeid
        ASSERT_TRUE(typeidExpr->isTypeOperand()) << "Expected type operand";
        ASSERT_TRUE(!Translator.isPolymorphicTypeid(typeidExpr)) << "Expected static typeid";

        // Translate
        std::string translation = Translator.translateTypeid(typeidExpr);
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
        ASSERT_TRUE(translation.find("__ti_Animal") != std::string::npos) << "Expected __ti_Animal reference";
        ASSERT_TRUE(translation.find("&") != std::string::npos) << "Expected address-of operator";
}

TEST_F(RTTIIntegrationTest, Polymorphic typeid on derived object) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Animal {
            public:
                virtual ~Animal() {}
            };

            class Dog : public Animal {
            public:
                void bark() {}
            };

            void identify(Animal* a) {
                const std::type_info& ti = typeid(*a);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        TypeidTranslator Translator(Context, Analyzer);

        const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
        ASSERT_TRUE(typeidExpr != nullptr) << "typeid expression not found";

        // Verify it's a polymorphic typeid
        ASSERT_TRUE(!typeidExpr->isTypeOperand()) << "Expected expression operand";
        ASSERT_TRUE(Translator.isPolymorphicTypeid(typeidExpr)) << "Expected polymorphic typeid";

        // Translate
        std::string translation = Translator.translateTypeid(typeidExpr);
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
        ASSERT_TRUE(translation.find("vptr") != std::string::npos) << "Expected vptr reference for polymorphic lookup";
}

TEST_F(RTTIIntegrationTest, Typeid on null polymorphic pointer) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Base {
            public:
                virtual ~Base() {}
            };

            void test() {
                Base* ptr = nullptr;
                if (ptr) {
                    const std::type_info& ti = typeid(*ptr);
                }
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        TypeidTranslator Translator(Context, Analyzer);

        const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
        ASSERT_TRUE(typeidExpr != nullptr) << "typeid expression not found";

        // Translate - should generate code (actual null check is runtime behavior)
        std::string translation = Translator.translateTypeid(typeidExpr);
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
}

TEST_F(RTTIIntegrationTest, Typeid equality comparison) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Shape {
            public:
                virtual ~Shape() {}
            };

            class Circle : public Shape {};

            void test() {
                const std::type_info& ti1 = typeid(Circle);
                const std::type_info& ti2 = typeid(Circle);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        TypeidTranslator Translator(Context, Analyzer);

        auto typeids = findAllTypeidExprs(Context);
        ASSERT_TRUE(typeids.size() >= 2) << "Expected at least 2 typeid expressions";

        // Both should be static and reference same type
        std::string trans1 = Translator.translateTypeid(typeids[0]);
        std::string trans2 = Translator.translateTypeid(typeids[1]);

        ASSERT_TRUE(trans1.find("__ti_Circle") != std::string::npos) << "First typeid should reference __ti_Circle";
        ASSERT_TRUE(trans2.find("__ti_Circle") != std::string::npos) << "Second typeid should reference __ti_Circle";
}

TEST_F(RTTIIntegrationTest, Typeid name() method translation) {
    method translation");

        const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Widget {
            public:
                virtual ~Widget() {}
            };

            void test() {
                const std::type_info& ti = typeid(Widget);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        TypeidTranslator Translator(Context, Analyzer);

        const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
        ASSERT_TRUE(typeidExpr != nullptr) << "typeid expression not found";

        std::string translation = Translator.translateTypeid(typeidExpr);
        ASSERT_TRUE(translation.find("__ti_Widget") != std::string::npos) << "Expected __ti_Widget reference";method translation");
}

TEST_F(RTTIIntegrationTest, Typeid in inheritance chain) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Grandparent {
            public:
                virtual ~Grandparent() {}
            };

            class Parent : public Grandparent {};
            class Child : public Parent {};

            void test(Grandparent* gp, Parent* p, Child* c) {
                const std::type_info& ti1 = typeid(*gp);
                const std::type_info& ti2 = typeid(*p);
                const std::type_info& ti3 = typeid(*c);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        TypeidTranslator Translator(Context, Analyzer);

        auto typeids = findAllTypeidExprs(Context);
        ASSERT_TRUE(typeids.size() >= 3) << "Expected at least 3 typeid expressions";

        // All should be polymorphic (expression operands)
        for (const auto* expr : typeids) {
            ASSERT_TRUE(Translator.isPolymorphicTypeid(expr)) << "Expected polymorphic typeid";
            std::string trans = Translator.translateTypeid(expr);
            ASSERT_TRUE(trans.find("vptr") != std::string::npos) << "Expected vptr for polymorphic lookup";
        }
}

TEST_F(RTTIIntegrationTest, Successful downcast to derived class) {
    const char* code = R"(
            class Shape {
            public:
                virtual ~Shape() {}
                virtual void draw() = 0;
            };

            class Circle : public Shape {
            public:
                void draw() override {}
                void bounce() {}
            };

            void process_shape(Shape* s) {
                Circle* c = dynamic_cast<Circle*>(s);
                if (c != nullptr) {
                    c->bounce();
                }
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        // Translate
        std::string translation = Translator.translateDynamicCast(castExpr);
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
        ASSERT_TRUE(translation.find("cxx_dynamic_cast") != std::string::npos) << "Expected cxx_dynamic_cast call";
        ASSERT_TRUE(translation.find("__ti_Shape") != std::string::npos) << "Expected source type __ti_Shape";
        ASSERT_TRUE(translation.find("__ti_Circle") != std::string::npos) << "Expected target type __ti_Circle";
}

TEST_F(RTTIIntegrationTest, Upcast to base class) {
    const char* code = R"(
            class Vehicle {
            public:
                virtual ~Vehicle() {}
            };

            class Car : public Vehicle {
            public:
                void drive() {}
            };

            void test() {
                Car* car = new Car();
                Vehicle* v = dynamic_cast<Vehicle*>(car);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        // Translate (upcast still generates dynamic_cast for uniformity)
        std::string translation = Translator.translateDynamicCast(castExpr);
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
}

TEST_F(RTTIIntegrationTest, Cast to unrelated type) {
    const char* code = R"(
            class Vehicle {
            public:
                virtual ~Vehicle() {}
            };

            class Car : public Vehicle {};
            class Boat : public Vehicle {};

            void test() {
                Vehicle* v = new Car();
                Boat* b = dynamic_cast<Boat*>(v);
                if (b == nullptr) {
                    // Not a boat
                }
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        // Translate
        std::string translation = Translator.translateDynamicCast(castExpr);
        ASSERT_TRUE(translation.find("cxx_dynamic_cast") != std::string::npos) << "Expected runtime cast function";
        ASSERT_TRUE(translation.find("__ti_Boat") != std::string::npos) << "Expected target type __ti_Boat";
}

TEST_F(RTTIIntegrationTest, Cross-cast between unrelated hierarchies) {
    const char* code = R"(
            class A { public: virtual ~A() {} };
            class B { public: virtual ~B() {} };

            void test() {
                A* a = new A();
                B* b = dynamic_cast<B*>(a);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        // Translate
        std::string translation = Translator.translateDynamicCast(castExpr);
        ASSERT_TRUE(translation.find("cxx_dynamic_cast") != std::string::npos) << "Expected runtime cast";
        ASSERT_TRUE(translation.find("__ti_A") != std::string::npos) << "Expected source type";
        ASSERT_TRUE(translation.find("__ti_B") != std::string::npos) << "Expected target type";
}

TEST_F(RTTIIntegrationTest, dynamic_cast on NULL pointer) {
    const char* code = R"(
            class Base { public: virtual ~Base() {} };
            class Derived : public Base {};

            void test() {
                Base* b = nullptr;
                Derived* d = dynamic_cast<Derived*>(b);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        // Translate (runtime will handle null check)
        std::string translation = Translator.translateDynamicCast(castExpr);
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
}

TEST_F(RTTIIntegrationTest, dynamic_cast to same type) {
    const char* code = R"(
            class MyClass { public: virtual ~MyClass() {} };

            void test() {
                MyClass* obj = new MyClass();
                MyClass* same = dynamic_cast<MyClass*>(obj);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        // Translate
        std::string translation = Translator.translateDynamicCast(castExpr);
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
}

TEST_F(RTTIIntegrationTest, RTTI with multiple inheritance) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class A { public: virtual ~A() {} };
            class B { public: virtual ~B() {} };
            class D : public A, public B { public: void foo() {} };

            void test_mi_cast() {
                A* a = new D();
                D* d = dynamic_cast<D*>(a);
                const std::type_info& ti = typeid(*a);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator DCTranslator(Context, Analyzer);
        TypeidTranslator TITranslator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
        ASSERT_TRUE(typeidExpr != nullptr) << "typeid expression not found";

        // Test both translations
        std::string castTrans = DCTranslator.translateDynamicCast(castExpr);
        std::string typeidTrans = TITranslator.translateTypeid(typeidExpr);

        ASSERT_TRUE(castTrans.find("cxx_dynamic_cast") != std::string::npos) << "Expected dynamic_cast";
        ASSERT_TRUE(typeidTrans.find("vptr") != std::string::npos) << "Expected polymorphic typeid";
}

TEST_F(RTTIIntegrationTest, Polymorphic containers) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Shape {
            public:
                virtual ~Shape() {}
                virtual void draw() = 0;
            };

            class Circle : public Shape {
            public:
                void draw() override {}
            };

            class Square : public Shape {
            public:
                void draw() override {}
            };

            void process(Shape* s) {
                const std::type_info& ti = typeid(*s);
                Circle* c = dynamic_cast<Circle*>(s);
                Square* sq = dynamic_cast<Square*>(s);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator DCTranslator(Context, Analyzer);
        TypeidTranslator TITranslator(Context, Analyzer);

        auto casts = findAllDynamicCastExprs(Context);
        ASSERT_TRUE(casts.size() >= 2) << "Expected at least 2 dynamic_cast expressions";

        const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
        ASSERT_TRUE(typeidExpr != nullptr) << "typeid expression not found";

        // Verify all translations work
        for (const auto* cast : casts) {
            std::string trans = DCTranslator.translateDynamicCast(cast);
            ASSERT_TRUE(!trans.empty()) << "dynamic_cast translation failed";
        }

        std::string typeidTrans = TITranslator.translateTypeid(typeidExpr);
        ASSERT_TRUE(!typeidTrans.empty()) << "typeid translation failed";
}
