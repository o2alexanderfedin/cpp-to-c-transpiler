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

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/DynamicCastTranslator.h"
#include "../include/TypeInfoGenerator.h"
#include "../include/VirtualMethodAnalyzer.h"
#include <cassert>
#include <sstream>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Test helper macros
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

// Test fixture
class DynamicCastCrossCastTest : public ::testing::Test {
protected:
};

TEST_F(DynamicCastCrossCastTest, DetectCrossCastInDiamond) {
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
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        // Cross-cast should be detected
        std::string sourceType = Translator.getSourceTypeName(castExpr);
        std::string targetType = Translator.getTargetTypeName(castExpr);

        ASSERT_TRUE(sourceType == "Base1") << "Expected source type 'Base1'";
        ASSERT_TRUE(targetType == "Base2") << "Expected target type 'Base2'";
}

TEST_F(DynamicCastCrossCastTest, GenerateCrossCastRuntimeCall) {
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
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        std::string translation = Translator.translateDynamicCast(castExpr);

        // Should generate cxx_dynamic_cast call
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
        ASSERT_TRUE(translation.find("cxx_dynamic_cast") != std::string::npos) << "Expected cxx_dynamic_cast call";
        ASSERT_TRUE(translation.find("__ti_Base1") != std::string::npos) << "Expected source type_info __ti_Base1";
        ASSERT_TRUE(translation.find("__ti_Base2") != std::string::npos) << "Expected target type_info __ti_Base2";
}

TEST_F(DynamicCastCrossCastTest, CrossCastWithVirtualInheritance) {
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
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        std::string translation = Translator.translateDynamicCast(castExpr);

        // Should generate cxx_dynamic_cast call for cross-cast
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
        ASSERT_TRUE(translation.find("cxx_dynamic_cast") != std::string::npos) << "Expected cxx_dynamic_cast call";
        ASSERT_TRUE(translation.find("__ti_Left") != std::string::npos) << "Expected source type_info __ti_Left";
        ASSERT_TRUE(translation.find("__ti_Right") != std::string::npos) << "Expected target type_info __ti_Right";
}

TEST_F(DynamicCastCrossCastTest, FailedCrossCastNoCommonDerived) {
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
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        std::string translation = Translator.translateDynamicCast(castExpr);

        // Should still generate call (failure happens at runtime)
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
        ASSERT_TRUE(translation.find("cxx_dynamic_cast") != std::string::npos) << "Expected cxx_dynamic_cast call";
}

TEST_F(DynamicCastCrossCastTest, CrossCastComplexHierarchy) {
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
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        std::string translation = Translator.translateDynamicCast(castExpr);

        // Should generate cross-cast call
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
        ASSERT_TRUE(translation.find("cxx_dynamic_cast") != std::string::npos) << "Expected cxx_dynamic_cast call";
        ASSERT_TRUE(translation.find("__ti_B") != std::string::npos) << "Expected source type_info __ti_B";
        ASSERT_TRUE(translation.find("__ti_C") != std::string::npos) << "Expected target type_info __ti_C";
}

TEST_F(DynamicCastCrossCastTest, CrossCastOffsetCalculation) {
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
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        std::string translation = Translator.translateDynamicCast(castExpr);

        // Should generate call with runtime offset calculation
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
        ASSERT_TRUE(translation.find("cxx_dynamic_cast") != std::string::npos) << "Expected cxx_dynamic_cast call";
}

TEST_F(DynamicCastCrossCastTest, BidirectionalTraversal) {
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
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        DynamicCastTranslator Translator(Context, Analyzer);

        const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
        ASSERT_TRUE(castExpr != nullptr) << "dynamic_cast expression not found";

        std::string translation = Translator.translateDynamicCast(castExpr);

        // Translation should delegate to runtime for bidirectional traversal
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
        ASSERT_TRUE(translation.find("cxx_dynamic_cast") != std::string::npos) << "Expected cxx_dynamic_cast call";
}
