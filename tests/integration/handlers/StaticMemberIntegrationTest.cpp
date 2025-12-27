/**
 * @file StaticMemberIntegrationTest.cpp
 * @brief Integration tests for static data member translation (Phase 49 Stage 4)
 *
 * Tests the complete translation pipeline for static data members:
 * - Detection in RecordHandler
 * - Declaration generation
 * - Definition generation
 * - Access translation in ExpressionHandler
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/DeclCXX.h"
#include "helpers/StaticMemberTranslator.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "NameMangler.h"
#include <memory>
#include <vector>

using namespace clang;
using namespace cpptoc;

// Helper to build AST from code
std::unique_ptr<ASTUnit> buildAST(const char *code) {
    return tooling::buildASTFromCode(code);
}

// Test fixture
class StaticMemberIntegrationTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> C_AST;
    std::unique_ptr<CNodeBuilder> builder;

    HandlerContext createContext(ASTUnit* ast) {
        C_AST = tooling::buildASTFromCode("", "output.c", std::make_shared<clang::PCHContainerOperations>());
        builder = std::make_unique<CNodeBuilder>(C_AST->getASTContext());
        return HandlerContext(ast->getASTContext(), C_AST->getASTContext(), *builder);
    }
};

// ============================================================================
// Declaration & Definition Tests
// ============================================================================

// Test 1: Static int with out-of-class definition
TEST_F(StaticMemberIntegrationTest, StaticIntWithOutOfClassDefinition) {
    const char *code = R"(
        class Counter {
        public:
            static int count;
        };
        int Counter::count = 0;
    )";

    auto AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";
    auto ctx = createContext(AST.get());

    // Find Counter class
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *Counter = nullptr;
    VarDecl *countDecl = nullptr;
    VarDecl *countDef = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Counter" && RD->isCompleteDefinition()) {
                Counter = RD;
                // Find declaration in class
                for (auto *Decl : RD->decls()) {
                    if (auto *VD = dyn_cast<VarDecl>(Decl)) {
                        if (VD->getNameAsString() == "count") {
                            countDecl = VD;
                            break;
                        }
                    }
                }
            }
        }
        // Find out-of-class definition
        if (auto *VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "count" && VD->isStaticDataMember()) {
                countDef = VD;
            }
        }
    }

    ASSERT_TRUE(Counter != nullptr) << "Counter class not found";
    ASSERT_TRUE(countDecl != nullptr) << "Static member declaration not found";
    ASSERT_TRUE(countDef != nullptr) << "Static member definition not found";

    // Test detection
    auto staticMembers = StaticMemberTranslator::detectStaticMembers(Counter);
    EXPECT_EQ(1u, staticMembers.size());

    // Test declaration generation (for header)
    VarDecl* cDecl = StaticMemberTranslator::generateStaticDeclaration(countDecl, ctx);
    ASSERT_TRUE(cDecl != nullptr);
    EXPECT_EQ("Counter__count", cDecl->getNameAsString());
    EXPECT_EQ(SC_Extern, cDecl->getStorageClass());

    // Test definition generation (for implementation)
    VarDecl* cDef = StaticMemberTranslator::generateStaticDefinition(countDef, ctx);
    ASSERT_TRUE(cDef != nullptr);
    EXPECT_EQ("Counter__count", cDef->getNameAsString());
    EXPECT_EQ(SC_None, cDef->getStorageClass());
    EXPECT_TRUE(cDef->hasInit());

    // Verify names match
    EXPECT_EQ(cDecl->getNameAsString(), cDef->getNameAsString())
        << "Declaration and definition must have matching names";
}

// Test 2: Const static with in-class initializer
TEST_F(StaticMemberIntegrationTest, ConstStaticWithInClassInitializer) {
    const char *code = R"(
        class Config {
        public:
            static const int MAX_SIZE = 1024;
        };
    )";

    auto AST = buildAST(code);
    ASSERT_TRUE(AST);
    auto ctx = createContext(AST.get());

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *Config = nullptr;
    VarDecl *maxSizeMember = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Config" && RD->isCompleteDefinition()) {
                Config = RD;
                for (auto *Decl : RD->decls()) {
                    if (auto *VD = dyn_cast<VarDecl>(Decl)) {
                        if (VD->getNameAsString() == "MAX_SIZE") {
                            maxSizeMember = VD;
                            break;
                        }
                    }
                }
                break;
            }
        }
    }

    ASSERT_TRUE(Config != nullptr);
    ASSERT_TRUE(maxSizeMember != nullptr);

    // Detect static members
    auto staticMembers = StaticMemberTranslator::detectStaticMembers(Config);
    ASSERT_EQ(1u, staticMembers.size());

    // Generate declaration
    VarDecl* cDecl = StaticMemberTranslator::generateStaticDeclaration(maxSizeMember, ctx);
    ASSERT_TRUE(cDecl != nullptr);
    EXPECT_EQ("Config__MAX_SIZE", cDecl->getNameAsString());
    EXPECT_TRUE(cDecl->getType().isConstQualified()) << "Should preserve const";

    // In-class initializers can be used to generate definition too
    VarDecl* cDef = StaticMemberTranslator::generateStaticDefinition(maxSizeMember, ctx);
    ASSERT_TRUE(cDef != nullptr);
    EXPECT_EQ("Config__MAX_SIZE", cDef->getNameAsString());
    EXPECT_TRUE(cDef->hasInit()) << "Should have in-class initializer";
}

// Test 3: Static array with definition
TEST_F(StaticMemberIntegrationTest, StaticArrayWithDefinition) {
    const char *code = R"(
        class Table {
        public:
            static int lookup[10];
        };
        int Table::lookup[10] = {0};
    )";

    auto AST = buildAST(code);
    ASSERT_TRUE(AST);
    auto ctx = createContext(AST.get());

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *Table = nullptr;
    VarDecl *lookupDef = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Table" && RD->isCompleteDefinition()) {
                Table = RD;
            }
        }
        if (auto *VD = dyn_cast<VarDecl>(D)) {
            if (VD->getNameAsString() == "lookup" && VD->isStaticDataMember()) {
                lookupDef = VD;
            }
        }
    }

    ASSERT_TRUE(Table != nullptr);
    ASSERT_TRUE(lookupDef != nullptr);

    // Test definition generation
    VarDecl* cDef = StaticMemberTranslator::generateStaticDefinition(lookupDef, ctx);
    ASSERT_TRUE(cDef != nullptr);
    EXPECT_EQ("Table__lookup", cDef->getNameAsString());
    EXPECT_TRUE(cDef->getType()->isArrayType()) << "Should preserve array type";
}

// Test 4: Multiple static members in one class
TEST_F(StaticMemberIntegrationTest, MultipleStaticMembersInClass) {
    const char *code = R"(
        class Stats {
        public:
            static int count;
            static int total;
            static float average;
        };
        int Stats::count = 0;
        int Stats::total = 0;
        float Stats::average = 0.0f;
    )";

    auto AST = buildAST(code);
    ASSERT_TRUE(AST);
    auto ctx = createContext(AST.get());

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *Stats = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Stats" && RD->isCompleteDefinition()) {
                Stats = RD;
                break;
            }
        }
    }

    ASSERT_TRUE(Stats != nullptr);

    // Detect all static members
    auto staticMembers = StaticMemberTranslator::detectStaticMembers(Stats);
    EXPECT_EQ(3u, staticMembers.size()) << "Should detect all 3 static members";

    // Generate declarations for all
    std::vector<VarDecl*> declarations;
    for (auto* member : staticMembers) {
        VarDecl* cDecl = StaticMemberTranslator::generateStaticDeclaration(member, ctx);
        ASSERT_TRUE(cDecl != nullptr);
        declarations.push_back(cDecl);
    }

    EXPECT_EQ(3u, declarations.size());

    // Verify all have correct naming pattern
    for (auto* decl : declarations) {
        std::string name = decl->getNameAsString();
        EXPECT_TRUE(name.find("Stats__") == 0) << "All declarations should start with Stats__";
    }
}

// Test 5: Static member in namespaced class
TEST_F(StaticMemberIntegrationTest, StaticMemberInNamespacedClass) {
    const char *code = R"(
        namespace app {
            class Config {
            public:
                static int value;
            };
            int Config::value = 100;
        }
    )";

    auto AST = buildAST(code);
    ASSERT_TRUE(AST);
    auto ctx = createContext(AST.get());

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *Config = nullptr;
    VarDecl *valueDef = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
            if (ND->getNameAsString() == "app") {
                for (auto *Inner : ND->decls()) {
                    if (auto *RD = dyn_cast<CXXRecordDecl>(Inner)) {
                        if (RD->getNameAsString() == "Config" && RD->isCompleteDefinition()) {
                            Config = RD;
                        }
                    }
                    if (auto *VD = dyn_cast<VarDecl>(Inner)) {
                        if (VD->getNameAsString() == "value" && VD->isStaticDataMember()) {
                            valueDef = VD;
                        }
                    }
                }
                break;
            }
        }
    }

    ASSERT_TRUE(Config != nullptr);
    ASSERT_TRUE(valueDef != nullptr);

    // Generate definition with namespace mangling
    VarDecl* cDef = StaticMemberTranslator::generateStaticDefinition(valueDef, ctx);
    ASSERT_TRUE(cDef != nullptr);
    EXPECT_EQ("app__Config__value", cDef->getNameAsString())
        << "Should include namespace in mangled name";
}

// ============================================================================
// Test Summary: 5 integration tests covering:
// - Out-of-class definitions
// - In-class initializers
// - Array types
// - Multiple members
// - Namespace support
// ============================================================================
