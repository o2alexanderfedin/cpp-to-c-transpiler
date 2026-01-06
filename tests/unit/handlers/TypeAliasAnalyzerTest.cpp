/**
 * @file TypeAliasAnalyzerTest.cpp
 * @brief TDD tests for TypeAliasAnalyzer (Phase 53, Group 1, Task 1)
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (15 tests):
 *
 * Group 1: Simple Type Aliases (5 tests)
 * 1. SimpleIntAlias - using IntType = int;
 * 2. SimpleFloatAlias - using FloatType = float;
 * 3. SimplePointerAlias - using IntPtr = int*;
 * 4. SimpleConstAlias - using ConstInt = const int;
 * 5. SimpleVolatileAlias - using VolatileInt = volatile int;
 *
 * Group 2: Complex Type Aliases (5 tests)
 * 6. FunctionPointerAlias - using Callback = void (*)(int);
 * 7. ComplexFunctionPointerAlias - using Handler = int (*)(float, double);
 * 8. StructAlias - using Point = struct Point2D;
 * 9. ConstPointerAlias - using ConstIntPtr = const int*;
 * 10. PointerToConstAlias - using PtrToConst = int* const;
 *
 * Group 3: Chained Aliases (3 tests)
 * 11. ChainedSimpleAlias - using B = A; using A = int;
 * 12. ChainedPointerAlias - using C = B; using B = int*;
 * 13. TripleChainedAlias - using D = C; using C = B; using B = int;
 *
 * Group 4: Template Type Aliases (2 tests - basic recognition)
 * 14. TemplateTypeAliasDetection - template<typename T> using Vec = T*;
 * 15. NonTemplateVerification - using Regular = int; (not a template)
 */

#include "handlers/TypeAliasAnalyzer.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class TypeAliasAnalyzerTest
 * @brief Test fixture for TypeAliasAnalyzer
 */
class TypeAliasAnalyzerTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<TypeAliasAnalyzer> analyzer;

    void SetUp() override {
        // Create real AST contexts using minimal code
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr) << "Failed to create C++ AST";
        ASSERT_NE(cAST, nullptr) << "Failed to create C AST";

        // Create builder and analyzer
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        analyzer = std::make_unique<TypeAliasAnalyzer>(
            cppAST->getASTContext(),
            *builder
        );
    }

    void TearDown() override {
        analyzer.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Build AST from code and return the first TypeAliasDecl
     */
    const clang::TypeAliasDecl* getTypeAliasDeclFromCode(const std::string& code) {
        cppAST = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(cppAST, nullptr) << "Failed to parse code: " << code;

        if (!cppAST) return nullptr;

        // Recreate builder and analyzer with new AST
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        analyzer = std::make_unique<TypeAliasAnalyzer>(
            cppAST->getASTContext(),
            *builder
        );

        // Find first TypeAliasDecl
        const clang::TypeAliasDecl* result = nullptr;
        for (auto* decl : cppAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* TAD = clang::dyn_cast<clang::TypeAliasDecl>(decl)) {
                result = TAD;
                break;
            }
        }

        EXPECT_NE(result, nullptr) << "No TypeAliasDecl found in code: " << code;
        return result;
    }

    /**
     * @brief Get TypeAliasTemplateDecl from code
     */
    const clang::TypeAliasTemplateDecl* getTypeAliasTemplateDeclFromCode(
        const std::string& code
    ) {
        cppAST = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(cppAST, nullptr) << "Failed to parse code: " << code;

        if (!cppAST) return nullptr;

        // Recreate builder and analyzer with new AST
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        analyzer = std::make_unique<TypeAliasAnalyzer>(
            cppAST->getASTContext(),
            *builder
        );

        // Find first TypeAliasTemplateDecl
        const clang::TypeAliasTemplateDecl* result = nullptr;
        for (auto* decl : cppAST->getASTContext().getTranslationUnitDecl()->decls()) {
            if (auto* TATD = clang::dyn_cast<clang::TypeAliasTemplateDecl>(decl)) {
                result = TATD;
                break;
            }
        }

        EXPECT_NE(result, nullptr) << "No TypeAliasTemplateDecl found in code: " << code;
        return result;
    }
};

// ============================================================================
// Group 1: Simple Type Aliases (5 tests)
// ============================================================================

TEST_F(TypeAliasAnalyzerTest, SimpleIntAlias) {
    // TDD RED: Write failing test first
    const char* code = "using IntType = int;";
    auto* TAD = getTypeAliasDeclFromCode(code);
    ASSERT_NE(TAD, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD);

    EXPECT_EQ(info.aliasName, "IntType");
    EXPECT_FALSE(info.underlyingType.isNull());
    EXPECT_TRUE(info.underlyingType->isIntegerType());
    EXPECT_FALSE(info.isTemplateAlias);
    EXPECT_FALSE(info.isPointerType);
    EXPECT_FALSE(info.isFunctionPointer);
    EXPECT_FALSE(info.hasConstQualifier);
    EXPECT_FALSE(info.hasVolatileQualifier);
}

TEST_F(TypeAliasAnalyzerTest, SimpleFloatAlias) {
    const char* code = "using FloatType = float;";
    auto* TAD = getTypeAliasDeclFromCode(code);
    ASSERT_NE(TAD, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD);

    EXPECT_EQ(info.aliasName, "FloatType");
    EXPECT_FALSE(info.underlyingType.isNull());
    EXPECT_TRUE(info.underlyingType->isFloatingType());
    EXPECT_FALSE(info.isTemplateAlias);
    EXPECT_FALSE(info.isPointerType);
    EXPECT_FALSE(info.isFunctionPointer);
}

TEST_F(TypeAliasAnalyzerTest, SimplePointerAlias) {
    const char* code = "using IntPtr = int*;";
    auto* TAD = getTypeAliasDeclFromCode(code);
    ASSERT_NE(TAD, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD);

    EXPECT_EQ(info.aliasName, "IntPtr");
    EXPECT_FALSE(info.underlyingType.isNull());
    EXPECT_TRUE(info.isPointerType);
    EXPECT_FALSE(info.isFunctionPointer);
}

TEST_F(TypeAliasAnalyzerTest, SimpleConstAlias) {
    const char* code = "using ConstInt = const int;";
    auto* TAD = getTypeAliasDeclFromCode(code);
    ASSERT_NE(TAD, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD);

    EXPECT_EQ(info.aliasName, "ConstInt");
    EXPECT_FALSE(info.underlyingType.isNull());
    EXPECT_TRUE(info.hasConstQualifier);
    EXPECT_FALSE(info.hasVolatileQualifier);
}

TEST_F(TypeAliasAnalyzerTest, SimpleVolatileAlias) {
    const char* code = "using VolatileInt = volatile int;";
    auto* TAD = getTypeAliasDeclFromCode(code);
    ASSERT_NE(TAD, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD);

    EXPECT_EQ(info.aliasName, "VolatileInt");
    EXPECT_FALSE(info.underlyingType.isNull());
    EXPECT_FALSE(info.hasConstQualifier);
    EXPECT_TRUE(info.hasVolatileQualifier);
}

// ============================================================================
// Group 2: Complex Type Aliases (5 tests)
// ============================================================================

TEST_F(TypeAliasAnalyzerTest, FunctionPointerAlias) {
    const char* code = "using Callback = void (*)(int);";
    auto* TAD = getTypeAliasDeclFromCode(code);
    ASSERT_NE(TAD, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD);

    EXPECT_EQ(info.aliasName, "Callback");
    EXPECT_FALSE(info.underlyingType.isNull());
    EXPECT_FALSE(info.isPointerType); // Function pointer is NOT data pointer
    EXPECT_TRUE(info.isFunctionPointer);
}

TEST_F(TypeAliasAnalyzerTest, ComplexFunctionPointerAlias) {
    const char* code = "using Handler = int (*)(float, double);";
    auto* TAD = getTypeAliasDeclFromCode(code);
    ASSERT_NE(TAD, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD);

    EXPECT_EQ(info.aliasName, "Handler");
    EXPECT_FALSE(info.underlyingType.isNull());
    EXPECT_TRUE(info.isFunctionPointer);
}

TEST_F(TypeAliasAnalyzerTest, StructAlias) {
    const char* code = "struct Point2D { int x; int y; }; using Point = Point2D;";
    auto* TAD = getTypeAliasDeclFromCode(code);
    ASSERT_NE(TAD, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD);

    EXPECT_EQ(info.aliasName, "Point");
    EXPECT_FALSE(info.underlyingType.isNull());
    EXPECT_TRUE(info.underlyingType->isStructureType() ||
                info.underlyingType->isRecordType());
}

TEST_F(TypeAliasAnalyzerTest, ConstPointerAlias) {
    const char* code = "using ConstIntPtr = const int*;";
    auto* TAD = getTypeAliasDeclFromCode(code);
    ASSERT_NE(TAD, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD);

    EXPECT_EQ(info.aliasName, "ConstIntPtr");
    EXPECT_FALSE(info.underlyingType.isNull());
    EXPECT_TRUE(info.isPointerType);
    // Pointer itself is not const, pointee is const
}

TEST_F(TypeAliasAnalyzerTest, PointerToConstAlias) {
    const char* code = "using PtrToConst = int* const;";
    auto* TAD = getTypeAliasDeclFromCode(code);
    ASSERT_NE(TAD, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD);

    EXPECT_EQ(info.aliasName, "PtrToConst");
    EXPECT_FALSE(info.underlyingType.isNull());
    EXPECT_TRUE(info.isPointerType);
    EXPECT_TRUE(info.hasConstQualifier); // Pointer itself is const
}

// ============================================================================
// Group 3: Chained Aliases (3 tests)
// ============================================================================

TEST_F(TypeAliasAnalyzerTest, ChainedSimpleAlias) {
    const char* code = "using A = int; using B = A;";

    // We need to get the second TypeAliasDecl (B)
    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    analyzer = std::make_unique<TypeAliasAnalyzer>(
        cppAST->getASTContext(),
        *builder
    );

    // Find second TypeAliasDecl (B)
    const clang::TypeAliasDecl* TAD_B = nullptr;
    int count = 0;
    for (auto* decl : cppAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* TAD = clang::dyn_cast<clang::TypeAliasDecl>(decl)) {
            count++;
            if (count == 2) {
                TAD_B = TAD;
                break;
            }
        }
    }

    ASSERT_NE(TAD_B, nullptr);
    ASSERT_EQ(TAD_B->getNameAsString(), "B");

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD_B);

    EXPECT_EQ(info.aliasName, "B");
    // Should resolve through chain: B → A → int
    EXPECT_FALSE(info.underlyingType.isNull());
    EXPECT_TRUE(info.underlyingType->isIntegerType());
}

TEST_F(TypeAliasAnalyzerTest, ChainedPointerAlias) {
    const char* code = "using A = int*; using B = A;";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    analyzer = std::make_unique<TypeAliasAnalyzer>(
        cppAST->getASTContext(),
        *builder
    );

    // Find second TypeAliasDecl (B)
    const clang::TypeAliasDecl* TAD_B = nullptr;
    int count = 0;
    for (auto* decl : cppAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* TAD = clang::dyn_cast<clang::TypeAliasDecl>(decl)) {
            count++;
            if (count == 2) {
                TAD_B = TAD;
                break;
            }
        }
    }

    ASSERT_NE(TAD_B, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD_B);

    EXPECT_EQ(info.aliasName, "B");
    EXPECT_TRUE(info.isPointerType);
}

TEST_F(TypeAliasAnalyzerTest, TripleChainedAlias) {
    const char* code = "using A = int; using B = A; using C = B;";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);

    builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
    analyzer = std::make_unique<TypeAliasAnalyzer>(
        cppAST->getASTContext(),
        *builder
    );

    // Find third TypeAliasDecl (C)
    const clang::TypeAliasDecl* TAD_C = nullptr;
    int count = 0;
    for (auto* decl : cppAST->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* TAD = clang::dyn_cast<clang::TypeAliasDecl>(decl)) {
            count++;
            if (count == 3) {
                TAD_C = TAD;
                break;
            }
        }
    }

    ASSERT_NE(TAD_C, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD_C);

    EXPECT_EQ(info.aliasName, "C");
    // Should resolve through triple chain: C → B → A → int
    EXPECT_TRUE(info.underlyingType->isIntegerType());
}

// ============================================================================
// Group 4: Template Type Aliases (2 tests - basic recognition)
// ============================================================================

TEST_F(TypeAliasAnalyzerTest, TemplateTypeAliasDetection) {
    const char* code = "template<typename T> using Vec = T*;";
    auto* TATD = getTypeAliasTemplateDeclFromCode(code);
    ASSERT_NE(TATD, nullptr);

    auto optInfo = analyzer->analyzeTemplateTypeAlias(TATD);

    ASSERT_TRUE(optInfo.has_value());
    TypeAliasInfo info = optInfo.value();

    EXPECT_EQ(info.aliasName, "Vec");
    EXPECT_TRUE(info.isTemplateAlias);
}

TEST_F(TypeAliasAnalyzerTest, NonTemplateVerification) {
    const char* code = "using Regular = int;";
    auto* TAD = getTypeAliasDeclFromCode(code);
    ASSERT_NE(TAD, nullptr);

    TypeAliasInfo info = analyzer->analyzeTypeAlias(TAD);

    EXPECT_EQ(info.aliasName, "Regular");
    EXPECT_FALSE(info.isTemplateAlias);
}

// ============================================================================
// Edge Cases
// ============================================================================

TEST_F(TypeAliasAnalyzerTest, NullTypeAliasDecl) {
    // Should handle nullptr gracefully
    TypeAliasInfo info = analyzer->analyzeTypeAlias(nullptr);

    EXPECT_TRUE(info.aliasName.empty());
    EXPECT_TRUE(info.underlyingType.isNull());
}
