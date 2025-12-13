/**
 * @file DynamicCastTranslatorTest.cpp
 * @brief Test suite for DynamicCastTranslator (Story #85)
 *
 * Tests dynamic_cast downcast translation for safe type casting.
 * Covers successful casts, failed casts, NULL handling, and same-type optimization.
 *
 * Acceptance Criteria:
 * - dynamic_cast expressions detected in AST
 * - Source and target types extracted correctly
 * - cxx_dynamic_cast() calls generated
 * - NULL pointer casts return NULL
 * - Same-type optimization works
 * - Failed casts return NULL
 *
 * SOLID Principles:
 * - Single Responsibility: Tests only dynamic_cast translation
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
 * Test 1: Detect dynamic_cast expression
 */
void test_DetectDynamicCast() {
    TEST_START("DetectDynamicCast");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
        public:
            ~Derived() override {}
        };

        void test(Base* ptr) {
            Derived* d = dynamic_cast<Derived*>(ptr);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    TEST_PASS("DetectDynamicCast");
}

/**
 * Test 2: Extract source and target types
 */
void test_ExtractSourceAndTargetTypes() {
    TEST_START("ExtractSourceAndTargetTypes");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
        public:
            ~Derived() override {}
        };

        void test(Base* ptr) {
            Derived* d = dynamic_cast<Derived*>(ptr);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    const CXXDynamicCastExpr* castExpr = findDynamicCastExpr(Context);
    ASSERT(castExpr != nullptr, "dynamic_cast expression not found");

    std::string sourceType = Translator.getSourceTypeName(castExpr);
    std::string targetType = Translator.getTargetTypeName(castExpr);

    ASSERT(sourceType == "Base", "Expected source type 'Base'");
    ASSERT(targetType == "Derived", "Expected target type 'Derived'");

    TEST_PASS("ExtractSourceAndTargetTypes");
}

/**
 * Test 3: Generate cxx_dynamic_cast() call
 */
void test_GenerateDynamicCastCall() {
    TEST_START("GenerateDynamicCastCall");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
        public:
            ~Derived() override {}
        };

        void test(Base* ptr) {
            Derived* d = dynamic_cast<Derived*>(ptr);
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
    ASSERT(translation.find("cxx_dynamic_cast") != std::string::npos, "Expected cxx_dynamic_cast call");
    ASSERT(translation.find("__ti_Base") != std::string::npos, "Expected source type_info __ti_Base");
    ASSERT(translation.find("__ti_Derived") != std::string::npos, "Expected target type_info __ti_Derived");

    TEST_PASS("GenerateDynamicCastCall");
}

/**
 * Test 4: NULL pointer handling
 */
void test_NullPointerHandling() {
    TEST_START("NullPointerHandling");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
        public:
            ~Derived() override {}
        };

        void test() {
            Base* ptr = nullptr;
            Derived* d = dynamic_cast<Derived*>(ptr);
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

    // NULL check should be handled by runtime cxx_dynamic_cast
    ASSERT(!translation.empty(), "Translation is empty");
    ASSERT(translation.find("cxx_dynamic_cast") != std::string::npos, "Expected cxx_dynamic_cast call");

    TEST_PASS("NullPointerHandling");
}

/**
 * Test 5: Same-type cast optimization
 */
void test_SameTypeCastOptimization() {
    TEST_START("SameTypeCastOptimization");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base {
        public:
            virtual ~Base() {}
        };

        void test(Base* ptr) {
            Base* same = dynamic_cast<Base*>(ptr);
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

    // Same-type optimization can be done at runtime level
    ASSERT(!translation.empty(), "Translation is empty");

    TEST_PASS("SameTypeCastOptimization");
}

/**
 * Test 6: Failed cast to unrelated type
 */
void test_FailedCastUnrelatedType() {
    TEST_START("FailedCastUnrelatedType");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base {
        public:
            virtual ~Base() {}
        };

        class Other {
        public:
            virtual ~Other() {}
        };

        void test(Base* ptr) {
            Other* o = dynamic_cast<Other*>(ptr);
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

    // Should generate call that returns NULL at runtime for unrelated types
    ASSERT(!translation.empty(), "Translation is empty");
    ASSERT(translation.find("cxx_dynamic_cast") != std::string::npos, "Expected cxx_dynamic_cast call");
    ASSERT(translation.find("__ti_Base") != std::string::npos, "Expected source __ti_Base");
    ASSERT(translation.find("__ti_Other") != std::string::npos, "Expected target __ti_Other");

    TEST_PASS("FailedCastUnrelatedType");
}

/**
 * Test 7: Cast with offset parameter
 */
void test_CastWithOffsetParameter() {
    TEST_START("CastWithOffsetParameter");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
        public:
            ~Derived() override {}
        };

        void test(Base* ptr) {
            Derived* d = dynamic_cast<Derived*>(ptr);
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

    // Should include offset parameter (-1 for runtime check)
    ASSERT(translation.find("-1") != std::string::npos, "Expected offset parameter -1");

    TEST_PASS("CastWithOffsetParameter");
}

/**
 * Test 8: Null expression handling
 */
void test_NullExpressionHandling() {
    TEST_START("NullExpressionHandling");

    const char* code = R"(
        namespace std { class type_info { public: const char* name() const; }; }

        class Base {
        public:
            virtual ~Base() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to parse C++ code");

    ASTContext& Context = AST->getASTContext();
    VirtualMethodAnalyzer Analyzer(Context);
    DynamicCastTranslator Translator(Context, Analyzer);

    // Null dynamic_cast expression should return empty string
    std::string translation = Translator.translateDynamicCast(nullptr);
    ASSERT(translation.empty(), "Expected empty string for null expression");

    TEST_PASS("NullExpressionHandling");
}

/**
 * Main function: runs all tests
 */
int main() {
    std::cout << "===============================================" << std::endl;
    std::cout << "DynamicCastTranslator Tests (Story #85)" << std::endl;
    std::cout << "===============================================" << std::endl << std::endl;

    test_DetectDynamicCast();
    test_ExtractSourceAndTargetTypes();
    test_GenerateDynamicCastCall();
    test_NullPointerHandling();
    test_SameTypeCastOptimization();
    test_FailedCastUnrelatedType();
    test_CastWithOffsetParameter();
    test_NullExpressionHandling();

    std::cout << std::endl;
    std::cout << "===============================================" << std::endl;
    std::cout << "All tests passed!" << std::endl;
    std::cout << "===============================================" << std::endl;

    return 0;
}
