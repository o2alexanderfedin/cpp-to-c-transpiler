/**
 * @file TypeidTranslatorTest.cpp
 * @brief Test suite for TypeidTranslator (Story #84)
 *
 * Tests typeid operator translation to type_info retrieval.
 * Covers both polymorphic (vtable lookup) and static (direct reference) scenarios.
 *
 * SOLID Principles:
 * - Single Responsibility: Tests only typeid translation
 * - Interface Segregation: Tests public API only
 * - Dependency Inversion: Uses abstract AST interfaces
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/TypeidTranslator.h"
#include "../include/TypeInfoGenerator.h"
#include "../include/VirtualMethodAnalyzer.h"
#include <cassert>
#include <sstream>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

/**
 * @brief Helper to find first CXXTypeidExpr in AST
 */
const CXXTypeidExpr* findTypeidExpr(ASTContext& Context) {
    const CXXTypeidExpr* result = nullptr;

    class TypeidFinder : public RecursiveASTVisitor<TypeidFinder> {
    public:
        const CXXTypeidExpr* Found = nullptr;

        bool VisitCXXTypeidExpr(CXXTypeidExpr* E) {
            if (!Found) {
                Found = E;
            }
            return true;
        }
    };

    TypeidFinder Finder;
    Finder.TraverseDecl(Context.getTranslationUnitDecl());
    return Finder.Found;
}

/**
 * Test 1: Detect polymorphic typeid expression
 */

// Test fixture
class TypeidTranslatorTest : public ::testing::Test {
protected:
};

TEST_F(TypeidTranslatorTest, DetectPolymorphicTypeid) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Base {
            public:
                virtual ~Base() {}
            };

            void test(Base* ptr) {
                const auto& ti = typeid(*ptr);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        TypeidTranslator Translator(Context, Analyzer);

        const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
        ASSERT_TRUE(typeidExpr != nullptr) << "typeid expression not found";

        // Verify it's a polymorphic typeid (dereferenced pointer)
        ASSERT_TRUE(!typeidExpr->isTypeOperand()) << "Expected expression operand, not type operand";
        ASSERT_TRUE(Translator.isPolymorphicTypeid(typeidExpr)) << "Expected polymorphic typeid";
}

TEST_F(TypeidTranslatorTest, DetectStaticTypeid) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Base {
            public:
                virtual ~Base() {}
            };

            void test() {
                const auto& ti = typeid(Base);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        TypeidTranslator Translator(Context, Analyzer);

        const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
        ASSERT_TRUE(typeidExpr != nullptr) << "typeid expression not found";

        // Verify it's a static typeid (type operand)
        ASSERT_TRUE(typeidExpr->isTypeOperand()) << "Expected type operand";
        ASSERT_TRUE(!Translator.isPolymorphicTypeid(typeidExpr)) << "Expected static typeid";
}

TEST_F(TypeidTranslatorTest, GeneratePolymorphicTypeidTranslation) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Base {
            public:
                virtual ~Base() {}
            };

            void test(Base* ptr) {
                const auto& ti = typeid(*ptr);
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

        // Should generate vtable lookup containing vptr reference
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
        ASSERT_TRUE(translation.find("vptr") != std::string::npos) << "Expected vptr reference in translation";
}

TEST_F(TypeidTranslatorTest, GenerateStaticTypeidTranslation) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Base {
            public:
                virtual ~Base() {}
            };

            void test() {
                const auto& ti = typeid(Base);
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

        // Should generate direct reference: &__ti_Base
        ASSERT_TRUE(!translation.empty()) << "Translation is empty";
        ASSERT_TRUE(translation.find("__ti_Base") != std::string::npos) << "Expected __ti_Base in translation";
        ASSERT_TRUE(translation.find("&") != std::string::npos) << "Expected address-of operator";
}

TEST_F(TypeidTranslatorTest, NonPolymorphicClassStaticTypeid) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class NonPoly {
            public:
                int x;
            };

            void test(NonPoly* ptr) {
                const auto& ti = typeid(*ptr);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        TypeidTranslator Translator(Context, Analyzer);

        const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
        ASSERT_TRUE(typeidExpr != nullptr) << "typeid expression not found";

        // Even though it's *ptr, non-polymorphic types use static typeid
        ASSERT_TRUE(!Translator.isPolymorphicTypeid(typeidExpr)) << "Expected static typeid for non-polymorphic class";

        std::string translation = Translator.translateTypeid(typeidExpr);
        // Should generate static reference, not vtable lookup
        ASSERT_TRUE(translation.find("__ti_") != std::string::npos) << "Expected __ti_ prefix";
        ASSERT_TRUE(translation.find("vptr") == std::string::npos) << "Should not contain vptr for non-polymorphic";
}

TEST_F(TypeidTranslatorTest, NullTypeidExpression) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Base {
            public:
                virtual ~Base() {}
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        TypeidTranslator Translator(Context, Analyzer);

        // Null typeid expression should return empty string
        std::string translation = Translator.translateTypeid(nullptr);
        ASSERT_TRUE(translation.empty()) << "Expected empty string for null expression";
}

TEST_F(TypeidTranslatorTest, PolymorphicTypeidIsExprOperand) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Derived {
            public:
                virtual ~Derived() {}
            };

            void test(Derived& ref) {
                const auto& ti = typeid(ref);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        TypeidTranslator Translator(Context, Analyzer);

        const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
        ASSERT_TRUE(typeidExpr != nullptr) << "typeid expression not found";

        // typeid(ref) where ref is polymorphic reference should be polymorphic
        ASSERT_TRUE(!typeidExpr->isTypeOperand()) << "Expected expression operand";
        ASSERT_TRUE(Translator.isPolymorphicTypeid(typeidExpr)) << "Expected polymorphic typeid for reference";
}

TEST_F(TypeidTranslatorTest, StaticTypeidForConstType) {
    const char* code = R"(
            namespace std { class type_info { public: const char* name() const; }; }

            class Shape {
            public:
                virtual ~Shape() {}
            };

            void test() {
                const auto& ti = typeid(const Shape);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST != nullptr) << "Failed to parse C++ code";

        ASTContext& Context = AST->getASTContext();
        VirtualMethodAnalyzer Analyzer(Context);
        TypeidTranslator Translator(Context, Analyzer);

        const CXXTypeidExpr* typeidExpr = findTypeidExpr(Context);
        ASSERT_TRUE(typeidExpr != nullptr) << "typeid expression not found";

        ASSERT_TRUE(typeidExpr->isTypeOperand()) << "Expected type operand";
        ASSERT_TRUE(!Translator.isPolymorphicTypeid(typeidExpr)) << "Expected static typeid";

        std::string translation = Translator.translateTypeid(typeidExpr);
        ASSERT_TRUE(translation.find("__ti_Shape") != std::string::npos) << "Expected __ti_Shape";
}
