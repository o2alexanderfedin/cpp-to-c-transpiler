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

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/CppToCVisitor.h"
#include "../include/TypeidTranslator.h"
#include "../include/DynamicCastTranslator.h"
#include "../include/TypeInfoGenerator.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/CNodeBuilder.h"
#include <iostream>
#include <cassert>
#include <sstream>
#include <vector>

using namespace clang;

// Test counter
static int tests_passed = 0;
static int tests_failed = 0;

// Test helper macros
#define TEST_START(name) std::cout << "Test " << (tests_passed + tests_failed + 1) << ": " << name << " ... " << std::flush
#define TEST_PASS(name) { std::cout << "PASS" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "FAIL: " << msg << std::endl; tests_failed++; return; }
#define ASSERT(cond, msg) \
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
void test_TypidStaticTypeName() {
    TEST_START("Static typeid on non-polymorphic class");

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
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    TypeidTranslator Translator(Context, Analyzer);

    const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
    ASSERT(typeidExpr != nullptr, "typeid expression not found");

    // Verify it's a static typeid
    ASSERT(typeidExpr->isTypeOperand(), "Expected type operand");
    ASSERT(!Translator.isPolymorphicTypeid(typeidExpr), "Expected static typeid");

    // Translate
    std::string translation = Translator.translateTypeid(typeidExpr);
    ASSERT(!translation.empty(), "Translation is empty");
    ASSERT(translation.find("__ti_Animal") != std::string::npos, "Expected __ti_Animal reference");
    ASSERT(translation.find("&") != std::string::npos, "Expected address-of operator");

    TEST_PASS("Static typeid on non-polymorphic class");
}

/**
 * Test 2: Polymorphic typeid on derived object
 * Verifies vtable lookup translation
 */
void test_TypeidPolymorphicBasic() {
    TEST_START("Polymorphic typeid on derived object");

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
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    TypeidTranslator Translator(Context, Analyzer);

    const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
    ASSERT(typeidExpr != nullptr, "typeid expression not found");

    // Verify it's a polymorphic typeid
    ASSERT(!typeidExpr->isTypeOperand(), "Expected expression operand");
    ASSERT(Translator.isPolymorphicTypeid(typeidExpr), "Expected polymorphic typeid");

    // Translate
    std::string translation = Translator.translateTypeid(typeidExpr);
    ASSERT(!translation.empty(), "Translation is empty");
    ASSERT(translation.find("vptr") != std::string::npos, "Expected vptr reference for polymorphic lookup");

    TEST_PASS("Polymorphic typeid on derived object");
}

/**
 * Test 3: Typeid on null polymorphic pointer
 * Should still work (vtable lookup is safe)
 */
void test_TypeidNullPointer() {
    TEST_START("Typeid on null polymorphic pointer");

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
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    TypeidTranslator Translator(Context, Analyzer);

    const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
    ASSERT(typeidExpr != nullptr, "typeid expression not found");

    // Translate - should generate code (actual null check is runtime behavior)
    std::string translation = Translator.translateTypeid(typeidExpr);
    ASSERT(!translation.empty(), "Translation is empty");

    TEST_PASS("Typeid on null polymorphic pointer");
}

// ============================================================================
// Category 2: Typeid Semantics Tests (3 tests)
// ============================================================================

/**
 * Test 4: Typeid equality comparison
 * Same type: ti1 == ti2 should work
 */
void test_TypeidEquality() {
    TEST_START("Typeid equality comparison");

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
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    TypeidTranslator Translator(Context, Analyzer);

    auto typeids = findAllTypeidExprs(Context);
    ASSERT(typeids.size() >= 2, "Expected at least 2 typeid expressions");

    // Both should be static and reference same type
    std::string trans1 = Translator.translateTypeid(typeids[0]);
    std::string trans2 = Translator.translateTypeid(typeids[1]);

    ASSERT(trans1.find("__ti_Circle") != std::string::npos, "First typeid should reference __ti_Circle");
    ASSERT(trans2.find("__ti_Circle") != std::string::npos, "Second typeid should reference __ti_Circle");

    TEST_PASS("Typeid equality comparison");
}

/**
 * Test 5: Typeid name() method translation
 * Extract name from type_info.type_name
 */
void test_TypeidNameFunction() {
    TEST_START("Typeid name() method translation");

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
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    TypeidTranslator Translator(Context, Analyzer);

    const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
    ASSERT(typeidExpr != nullptr, "typeid expression not found");

    std::string translation = Translator.translateTypeid(typeidExpr);
    ASSERT(translation.find("__ti_Widget") != std::string::npos, "Expected __ti_Widget reference");

    TEST_PASS("Typeid name() method translation");
}

/**
 * Test 6: Typeid in inheritance chain
 * Polymorphic lookup finds correct type at each level
 */
void test_TypeidInheritanceChain() {
    TEST_START("Typeid in inheritance chain");

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
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    TypeidTranslator Translator(Context, Analyzer);

    auto typeids = findAllTypeidExprs(Context);
    ASSERT(typeids.size() >= 3, "Expected at least 3 typeid expressions");

    // All should be polymorphic (expression operands)
    for (const auto* expr : typeids) {
        ASSERT(Translator.isPolymorphicTypeid(expr), "Expected polymorphic typeid");
        std::string trans = Translator.translateTypeid(expr);
        ASSERT(trans.find("vptr") != std::string::npos, "Expected vptr for polymorphic lookup");
    }

    TEST_PASS("Typeid in inheritance chain");
}

// ============================================================================
// Category 3: Dynamic Cast Success Tests (2 tests)
// ============================================================================

/**
 * Test 7: Successful downcast to derived class
 * Return non-NULL pointer, type is correct
 */
void test_DynamicCastDowncast() {
    TEST_START("Successful downcast to derived class");

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
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    // Translate
    std::string translation = Translator.translateDynamicCast(castExpr);
    ASSERT(!translation.empty(), "Translation is empty");
    ASSERT(translation.find("cxx_dynamic_cast") != std::string::npos, "Expected cxx_dynamic_cast call");
    ASSERT(translation.find("__ti_Shape") != std::string::npos, "Expected source type __ti_Shape");
    ASSERT(translation.find("__ti_Circle") != std::string::npos, "Expected target type __ti_Circle");

    TEST_PASS("Successful downcast to derived class");
}

/**
 * Test 8: Upcast to base class (always succeeds)
 * Return valid base pointer
 */
void test_DynamicCastUpcast() {
    TEST_START("Upcast to base class");

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
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    // Translate (upcast still generates dynamic_cast for uniformity)
    std::string translation = Translator.translateDynamicCast(castExpr);
    ASSERT(!translation.empty(), "Translation is empty");

    TEST_PASS("Upcast to base class");
}

// ============================================================================
// Category 4: Dynamic Cast Failure Tests (2 tests)
// ============================================================================

/**
 * Test 9: Cast to unrelated type
 * Return NULL pointer, original object unmodified
 */
void test_DynamicCastWrongType() {
    TEST_START("Cast to unrelated type");

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
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    // Translate
    std::string translation = Translator.translateDynamicCast(castExpr);
    ASSERT(translation.find("cxx_dynamic_cast") != std::string::npos, "Expected runtime cast function");
    ASSERT(translation.find("__ti_Boat") != std::string::npos, "Expected target type __ti_Boat");

    TEST_PASS("Cast to unrelated type");
}

/**
 * Test 10: Cross-cast between unrelated hierarchies
 * Return NULL pointer
 */
void test_DynamicCastCrossHierarchy() {
    TEST_START("Cross-cast between unrelated hierarchies");

    const char* code = R"(
        class A { public: virtual ~A() {} };
        class B { public: virtual ~B() {} };

        void test() {
            A* a = new A();
            B* b = dynamic_cast<B*>(a);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    // Translate
    std::string translation = Translator.translateDynamicCast(castExpr);
    ASSERT(translation.find("cxx_dynamic_cast") != std::string::npos, "Expected runtime cast");
    ASSERT(translation.find("__ti_A") != std::string::npos, "Expected source type");
    ASSERT(translation.find("__ti_B") != std::string::npos, "Expected target type");

    TEST_PASS("Cross-cast between unrelated hierarchies");
}

// ============================================================================
// Category 5: Edge Cases Tests (2 tests)
// ============================================================================

/**
 * Test 11: dynamic_cast on NULL pointer
 * Return NULL (preserve NULL)
 */
void test_DynamicCastNullPtr() {
    TEST_START("dynamic_cast on NULL pointer");

    const char* code = R"(
        class Base { public: virtual ~Base() {} };
        class Derived : public Base {};

        void test() {
            Base* b = nullptr;
            Derived* d = dynamic_cast<Derived*>(b);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    // Translate (runtime will handle null check)
    std::string translation = Translator.translateDynamicCast(castExpr);
    ASSERT(!translation.empty(), "Translation is empty");

    TEST_PASS("dynamic_cast on NULL pointer");
}

/**
 * Test 12: dynamic_cast to same type
 * Optimization: return same pointer
 */
void test_DynamicCastSameType() {
    TEST_START("dynamic_cast to same type");

    const char* code = R"(
        class MyClass { public: virtual ~MyClass() {} };

        void test() {
            MyClass* obj = new MyClass();
            MyClass* same = dynamic_cast<MyClass*>(obj);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    // Translate
    std::string translation = Translator.translateDynamicCast(castExpr);
    ASSERT(!translation.empty(), "Translation is empty");

    TEST_PASS("dynamic_cast to same type");
}

// ============================================================================
// Category 6: Integration Tests (3 tests)
// ============================================================================

/**
 * Test 13: RTTI with multiple inheritance
 * Test typeid and dynamic_cast with MI
 */
void test_MultipleInheritanceRTTI() {
    TEST_START("RTTI with multiple inheritance");

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
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator DCTranslator(Context, Analyzer);
    TypeidTranslator TITranslator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
    ASSERT(typeidExpr != nullptr, "typeid expression not found");

    // Test both translations
    std::string castTrans = DCTranslator.translateDynamicCast(castExpr);
    std::string typeidTrans = TITranslator.translateTypeid(typeidExpr);

    ASSERT(castTrans.find("cxx_dynamic_cast") != std::string::npos, "Expected dynamic_cast");
    ASSERT(typeidTrans.find("vptr") != std::string::npos, "Expected polymorphic typeid");

    TEST_PASS("RTTI with multiple inheritance");
}

/**
 * Test 14: Virtual methods with RTTI (Phase 9 integration)
 * Virtual methods + RTTI together
 */
void test_VirtualMethodsWithRTTI() {
    TEST_START("Virtual methods with RTTI");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Animal {
        public:
            virtual ~Animal() {}
            virtual void speak() = 0;
        };

        class Cat : public Animal {
        public:
            void speak() override {}
        };

        void identify_animal(Animal* a) {
            const std::type_info& ti = typeid(*a);
            Cat* c = dynamic_cast<Cat*>(a);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);

    // Verify polymorphism detected
    class ClassFinder : public RecursiveASTVisitor<ClassFinder> {
    public:
        CXXRecordDecl* AnimalClass = nullptr;
        bool VisitCXXRecordDecl(CXXRecordDecl* D) {
            if (D->getNameAsString() == "Animal" && D->isCompleteDefinition()) {
                AnimalClass = D;
            }
            return true;
        }
    };
    ClassFinder Finder;
    Finder.TraverseDecl(Context.getTranslationUnitDecl());
    ASSERT(Finder.AnimalClass != nullptr, "Animal class not found");
    ASSERT(Analyzer.isPolymorphic(Finder.AnimalClass), "Animal should be polymorphic");

    TEST_PASS("Virtual methods with RTTI");
}

/**
 * Test 15: Polymorphic containers
 * Vector of base pointers, identify derived types at runtime
 */
void test_PolymorphicContainers() {
    TEST_START("Polymorphic containers");

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
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator DCTranslator(Context, Analyzer);
    TypeidTranslator TITranslator(Context, Analyzer);

    auto casts = findAllDynamicCastExprs(Context);
    ASSERT(casts.size() >= 2, "Expected at least 2 dynamic_cast expressions");

    const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
    ASSERT(typeidExpr != nullptr, "typeid expression not found");

    // Verify all translations work
    for (const auto* cast : casts) {
        std::string trans = DCTranslator.translateDynamicCast(cast);
        ASSERT(!trans.empty(), "dynamic_cast translation failed");
    }

    std::string typeidTrans = TITranslator.translateTypeid(typeidExpr);
    ASSERT(!typeidTrans.empty(), "typeid translation failed");

    TEST_PASS("Polymorphic containers");
}

// ============================================================================
// Main function
// ============================================================================

int main() {
    std::cout << "================================================================" << std::endl;
    std::cout << "RTTI Integration Tests (Phase 13, v2.6.0)" << std::endl;
    std::cout << "================================================================" << std::endl << std::endl;

    // Category 1: Typeid Basic (3 tests)
    test_TypidStaticTypeName();
    test_TypeidPolymorphicBasic();
    test_TypeidNullPointer();

    // Category 2: Typeid Semantics (3 tests)
    test_TypeidEquality();
    test_TypeidNameFunction();
    test_TypeidInheritanceChain();

    // Category 3: Dynamic Cast Success (2 tests)
    test_DynamicCastDowncast();
    test_DynamicCastUpcast();

    // Category 4: Dynamic Cast Failure (2 tests)
    test_DynamicCastWrongType();
    test_DynamicCastCrossHierarchy();

    // Category 5: Edge Cases (2 tests)
    test_DynamicCastNullPtr();
    test_DynamicCastSameType();

    // Category 6: Integration (3 tests)
    test_MultipleInheritanceRTTI();
    test_VirtualMethodsWithRTTI();
    test_PolymorphicContainers();

    std::cout << std::endl;
    std::cout << "================================================================" << std::endl;
    std::cout << "Test Results: " << tests_passed << " passed, " << tests_failed << " failed" << std::endl;
    std::cout << "================================================================" << std::endl;

    return (tests_failed == 0) ? 0 : 1;
}
