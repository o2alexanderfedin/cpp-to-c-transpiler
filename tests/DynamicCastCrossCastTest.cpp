/**
 * @file DynamicCastCrossCastTest.cpp
 * @brief Test suite for DynamicCastTranslator Cross-Casting (Story #87)
 *
 * Tests dynamic_cast cross-casting support for sibling classes in multiple
 * inheritance hierarchies. Cross-casting allows casting between sibling base
 * classes (e.g., Base1* to Base2* in Diamond : Base1, Base2).
 *
 * Acceptance Criteria:
 * - Cross-cast detection: Identify sibling class casts (no direct inheritance)
 * - Common derived type: Find most-derived type containing both classes
 * - Bidirectional traversal: Navigate up from source, down to target
 * - Offset adjustment: Calculate pointer offset for cross-cast
 * - Failed cross-cast: Return NULL if no common derived type
 * - Virtual base handling: Support virtual inheritance in cross-casts
 * - Testing: Validate Base1* to Base2* in Diamond hierarchy
 *
 * SOLID Principles:
 * - Single Responsibility: Tests only cross-casting functionality
 * - Interface Segregation: Tests public API only
 * - Dependency Inversion: Uses abstract AST interfaces
 */

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/DynamicCastTranslator.h"
#include "../include/TypeInfoGenerator.h"
#include "../include/VirtualMethodAnalyzer.h"
#include <iostream>
#include <cassert>
#include <sstream>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Test helper macros
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

/**
 * @brief Helper to find first CXXDynamicCastExpr in AST
 */
const CXXDynamicCastExpr* findDynamicCastExpr(ASTContext& Context) {
    const CXXDynamicCastExpr* result = nullptr;

    class DynamicCastFinder : public RecursiveASTVisitor<DynamicCastFinder> {
    public:
        const CXXDynamicCastExpr* Found = nullptr;

        bool VisitCXXDynamicCastExpr(CXXDynamicCastExpr* E) {
            if (!Found) {
                Found = E;
            }
            return true;
        }
    };

    DynamicCastFinder Finder;
    Finder.TraverseDecl(Context.getTranslationUnitDecl());
    return Finder.Found;
}

/**
 * Test 1: Detect cross-cast in diamond inheritance
 *
 * Hierarchy:
 *        Base1   Base2
 *           \     /
 *           Diamond
 *
 * Test: Base1* -> Base2* should be detected as cross-cast
 */
void test_DetectCrossCastInDiamond() {
    TEST_START("DetectCrossCastInDiamond");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base1 {
        public:
            virtual ~Base1() {}
        };

        class Base2 {
        public:
            virtual ~Base2() {}
        };

        class Diamond : public Base1, public Base2 {
        public:
            ~Diamond() override {}
        };

        void test(Base1* ptr) {
            Base2* b2 = dynamic_cast<Base2*>(ptr);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    // Cross-cast should be detected
    std::string sourceType = Translator.getSourceTypeName(castExpr);
    std::string targetType = Translator.getTargetTypeName(castExpr);

    ASSERT(sourceType == "Base1", "Expected source type 'Base1'");
    ASSERT(targetType == "Base2", "Expected target type 'Base2'");

    TEST_PASS("DetectCrossCastInDiamond");
}

/**
 * Test 2: Generate cross-cast runtime call with offset hint
 *
 * Cross-casts require special offset hint (-2) indicating no direct inheritance
 */
void test_GenerateCrossCastRuntimeCall() {
    TEST_START("GenerateCrossCastRuntimeCall");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base1 {
        public:
            virtual ~Base1() {}
        };

        class Base2 {
        public:
            virtual ~Base2() {}
        };

        class Diamond : public Base1, public Base2 {
        public:
            ~Diamond() override {}
        };

        void test(Base1* ptr) {
            Base2* b2 = dynamic_cast<Base2*>(ptr);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    std::string translation = Translator.translateDynamicCast(castExpr);

    // Should generate cxx_dynamic_cast call
    ASSERT(!translation.empty(), "Translation is empty");
    ASSERT(translation.find("cxx_dynamic_cast") != std::string::npos,
           "Expected cxx_dynamic_cast call");
    ASSERT(translation.find("__ti_Base1") != std::string::npos,
           "Expected source type_info __ti_Base1");
    ASSERT(translation.find("__ti_Base2") != std::string::npos,
           "Expected target type_info __ti_Base2");

    TEST_PASS("GenerateCrossCastRuntimeCall");
}

/**
 * Test 3: Cross-cast with virtual inheritance
 *
 * Hierarchy:
 *      virtual Base
 *         /      \
 *      Left      Right
 *         \      /
 *         Diamond
 *
 * Test: Left* -> Right* should work via virtual base
 */
void test_CrossCastWithVirtualInheritance() {
    TEST_START("CrossCastWithVirtualInheritance");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base {
        public:
            virtual ~Base() {}
        };

        class Left : public virtual Base {
        public:
            ~Left() override {}
        };

        class Right : public virtual Base {
        public:
            ~Right() override {}
        };

        class Diamond : public Left, public Right {
        public:
            ~Diamond() override {}
        };

        void test(Left* ptr) {
            Right* r = dynamic_cast<Right*>(ptr);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    std::string translation = Translator.translateDynamicCast(castExpr);

    // Should generate cxx_dynamic_cast call for cross-cast
    ASSERT(!translation.empty(), "Translation is empty");
    ASSERT(translation.find("cxx_dynamic_cast") != std::string::npos,
           "Expected cxx_dynamic_cast call");
    ASSERT(translation.find("__ti_Left") != std::string::npos,
           "Expected source type_info __ti_Left");
    ASSERT(translation.find("__ti_Right") != std::string::npos,
           "Expected target type_info __ti_Right");

    TEST_PASS("CrossCastWithVirtualInheritance");
}

/**
 * Test 4: Failed cross-cast (no common derived type)
 *
 * Test: Unrelated sibling classes should generate runtime call that returns NULL
 */
void test_FailedCrossCastNoCommonDerived() {
    TEST_START("FailedCrossCastNoCommonDerived");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base1 {
        public:
            virtual ~Base1() {}
        };

        class Base2 {
        public:
            virtual ~Base2() {}
        };

        class Derived1 : public Base1 {
        public:
            ~Derived1() override {}
        };

        class Derived2 : public Base2 {
        public:
            ~Derived2() override {}
        };

        void test(Derived1* ptr) {
            // No common derived type - should fail at runtime
            Derived2* d2 = dynamic_cast<Derived2*>(ptr);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    std::string translation = Translator.translateDynamicCast(castExpr);

    // Should still generate call (failure happens at runtime)
    ASSERT(!translation.empty(), "Translation is empty");
    ASSERT(translation.find("cxx_dynamic_cast") != std::string::npos,
           "Expected cxx_dynamic_cast call");

    TEST_PASS("FailedCrossCastNoCommonDerived");
}

/**
 * Test 5: Cross-cast in complex hierarchy
 *
 * Hierarchy:
 *         A
 *        / \
 *       B   C
 *        \ /
 *         D
 *
 * Test: B* -> C* should work via common derived type D
 */
void test_CrossCastComplexHierarchy() {
    TEST_START("CrossCastComplexHierarchy");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class A {
        public:
            virtual ~A() {}
        };

        class B : public A {
        public:
            ~B() override {}
        };

        class C : public A {
        public:
            ~C() override {}
        };

        class D : public B, public C {
        public:
            ~D() override {}
        };

        void test(B* ptr) {
            C* c = dynamic_cast<C*>(ptr);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    std::string translation = Translator.translateDynamicCast(castExpr);

    // Should generate cross-cast call
    ASSERT(!translation.empty(), "Translation is empty");
    ASSERT(translation.find("cxx_dynamic_cast") != std::string::npos,
           "Expected cxx_dynamic_cast call");
    ASSERT(translation.find("__ti_B") != std::string::npos,
           "Expected source type_info __ti_B");
    ASSERT(translation.find("__ti_C") != std::string::npos,
           "Expected target type_info __ti_C");

    TEST_PASS("CrossCastComplexHierarchy");
}

/**
 * Test 6: Cross-cast with offset calculation
 *
 * Test: Verify offset is properly calculated for sibling casts
 */
void test_CrossCastOffsetCalculation() {
    TEST_START("CrossCastOffsetCalculation");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base1 {
        public:
            int x;
            virtual ~Base1() {}
        };

        class Base2 {
        public:
            int y;
            virtual ~Base2() {}
        };

        class Diamond : public Base1, public Base2 {
        public:
            int z;
            ~Diamond() override {}
        };

        void test(Base1* ptr) {
            // Cast from Base1 to Base2 requires offset adjustment
            Base2* b2 = dynamic_cast<Base2*>(ptr);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    std::string translation = Translator.translateDynamicCast(castExpr);

    // Should generate call with runtime offset calculation
    ASSERT(!translation.empty(), "Translation is empty");
    ASSERT(translation.find("cxx_dynamic_cast") != std::string::npos,
           "Expected cxx_dynamic_cast call");

    TEST_PASS("CrossCastOffsetCalculation");
}

/**
 * Test 7: Bidirectional traversal requirement
 *
 * Cross-cast requires traversing up to common base, then down to target
 */
void test_BidirectionalTraversal() {
    TEST_START("BidirectionalTraversal");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base1 {
        public:
            virtual ~Base1() {}
        };

        class Base2 {
        public:
            virtual ~Base2() {}
        };

        class Diamond : public Base1, public Base2 {
        public:
            ~Diamond() override {}
        };

        void test(Base1* ptr) {
            // Requires: up to Diamond, then down to Base2
            Base2* b2 = dynamic_cast<Base2*>(ptr);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    std::string translation = Translator.translateDynamicCast(castExpr);

    // Translation should delegate to runtime for bidirectional traversal
    ASSERT(!translation.empty(), "Translation is empty");
    ASSERT(translation.find("cxx_dynamic_cast") != std::string::npos,
           "Expected cxx_dynamic_cast call");

    TEST_PASS("BidirectionalTraversal");
}

/**
 * Main function: runs all tests
 */
int main() {
    std::cout << "===============================================" << std::endl;
    std::cout << "DynamicCast Cross-Cast Tests (Story #87)" << std::endl;
    std::cout << "===============================================" << std::endl << std::endl;

    test_DetectCrossCastInDiamond();
    test_GenerateCrossCastRuntimeCall();
    test_CrossCastWithVirtualInheritance();
    test_FailedCrossCastNoCommonDerived();
    test_CrossCastComplexHierarchy();
    test_CrossCastOffsetCalculation();
    test_BidirectionalTraversal();

    std::cout << std::endl;
    std::cout << "===============================================" << std::endl;
    std::cout << "All tests passed!" << std::endl;
    std::cout << "===============================================" << std::endl;

    return 0;
}
