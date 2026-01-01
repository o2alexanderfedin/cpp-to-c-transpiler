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
#include "dispatch/StaticDataMemberHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include <memory>
#include <vector>

using namespace clang;
using namespace cpptoc;

// Helper to build AST from code
std::unique_ptr<ASTUnit> buildAST(const char *code) {
    return tooling::buildASTFromCode(code);
}

// Helper to create test context
struct TestContext {
    std::unique_ptr<ASTUnit> cAST;
    PathMapper* pathMapper;
    std::unique_ptr<DeclLocationMapper> declLocationMapper;
    std::unique_ptr<DeclMapper> declMapper;
    std::unique_ptr<TypeMapper> typeMapper;
    std::unique_ptr<ExprMapper> exprMapper;
    std::unique_ptr<StmtMapper> stmtMapper;
    std::unique_ptr<CppToCVisitorDispatcher> dispatcher;
};

TestContext createTestContext() {
    TestContext ctx;

    // Reset PathMapper for test isolation
    PathMapper::reset();

    // Create C context
    ctx.cAST = tooling::buildASTFromCode("int dummy;");
    if (!ctx.cAST) {
        throw std::runtime_error("Failed to create C context");
    }

    // Create mappers
    ctx.pathMapper = &PathMapper::getInstance("/tmp/test_source", "/tmp/test_output");
    ctx.declLocationMapper = std::make_unique<DeclLocationMapper>(*ctx.pathMapper);
    ctx.declMapper = std::make_unique<DeclMapper>();
    ctx.typeMapper = std::make_unique<TypeMapper>();
    ctx.exprMapper = std::make_unique<ExprMapper>();
    ctx.stmtMapper = std::make_unique<StmtMapper>();

    // Create dispatcher (no handlers registered yet)
    ctx.dispatcher = std::make_unique<CppToCVisitorDispatcher>(
        *ctx.pathMapper,
        *ctx.declLocationMapper,
        *ctx.declMapper,
        *ctx.typeMapper,
        *ctx.exprMapper,
        *ctx.stmtMapper
    );

    return ctx;
}

// Test fixture
class StaticDataMemberIntegrationTest : public ::testing::Test {
protected:
    // No member variables needed
};

// ============================================================================
// Declaration & Definition Tests
// ============================================================================

// Test 1: Static int with out-of-class definition
TEST_F(StaticDataMemberIntegrationTest, StaticIntWithOutOfClassDefinition) {
    const char *code = R"(
        class Counter {
        public:
            static int count;
        };
        int Counter::count = 0;
    )";

    auto AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Create context
    auto ctx = createTestContext();
    StaticDataMemberHandler::registerWith(*ctx.dispatcher);

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
    auto staticMembers = StaticDataMemberHandler::detectStaticMembers(Counter);
    EXPECT_EQ(1u, staticMembers.size());

    // Test declaration generation (for header)
    ctx.dispatcher->dispatch(
        AST->getASTContext(),
        ctx.cAST->getASTContext(),
        countDecl
    );
    auto* cDecl = ctx.declMapper->getCreated(countDecl);
    ASSERT_TRUE(cDecl != nullptr);
    if (auto* varDecl = dyn_cast<VarDecl>(cDecl)) {
        EXPECT_EQ("Counter__count", varDecl->getNameAsString());
        EXPECT_EQ(SC_Extern, varDecl->getStorageClass());
    } else {
        FAIL() << "Expected VarDecl for declaration";
    }

    // Test definition generation (for implementation)
    ctx.dispatcher->dispatch(
        AST->getASTContext(),
        ctx.cAST->getASTContext(),
        countDef
    );
    auto* cDef = ctx.declMapper->getCreated(countDef);
    ASSERT_TRUE(cDef != nullptr);
    if (auto* varDef = dyn_cast<VarDecl>(cDef)) {
        EXPECT_EQ("Counter__count", varDef->getNameAsString());
        EXPECT_EQ(SC_None, varDef->getStorageClass());
        EXPECT_TRUE(varDef->hasInit());

        // Verify names match
        auto* declVar = dyn_cast<VarDecl>(cDecl);
        EXPECT_EQ(declVar->getNameAsString(), varDef->getNameAsString())
            << "Declaration and definition must have matching names";
    } else {
        FAIL() << "Expected VarDecl for definition";
    }
}

// Test 2: Const static with in-class initializer
TEST_F(StaticDataMemberIntegrationTest, ConstStaticWithInClassInitializer) {
    const char *code = R"(
        class Config {
        public:
            static const int MAX_SIZE = 1024;
        };
    )";

    auto AST = buildAST(code);
    ASSERT_TRUE(AST);

    // Create context
    auto ctx = createTestContext();
    StaticDataMemberHandler::registerWith(*ctx.dispatcher);

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
    auto staticMembers = StaticDataMemberHandler::detectStaticMembers(Config);
    ASSERT_EQ(1u, staticMembers.size());

    // Generate declaration
    ctx.dispatcher->dispatch(
        AST->getASTContext(),
        ctx.cAST->getASTContext(),
        maxSizeMember
    );
    auto* cDecl = ctx.declMapper->getCreated(maxSizeMember);
    ASSERT_TRUE(cDecl != nullptr);
    if (auto* varDecl = dyn_cast<VarDecl>(cDecl)) {
        EXPECT_EQ("Config__MAX_SIZE", varDecl->getNameAsString());
        EXPECT_TRUE(varDecl->getType().isConstQualified()) << "Should preserve const";
        EXPECT_TRUE(varDecl->hasInit()) << "Should have in-class initializer";
    } else {
        FAIL() << "Expected VarDecl";
    }
}

// Test 3: Static array with definition
TEST_F(StaticDataMemberIntegrationTest, StaticArrayWithDefinition) {
    const char *code = R"(
        class Table {
        public:
            static int lookup[10];
        };
        int Table::lookup[10] = {0};
    )";

    auto AST = buildAST(code);
    ASSERT_TRUE(AST);

    // Create context
    auto ctx = createTestContext();
    StaticDataMemberHandler::registerWith(*ctx.dispatcher);

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
    ctx.dispatcher->dispatch(
        AST->getASTContext(),
        ctx.cAST->getASTContext(),
        lookupDef
    );
    auto* cDef = ctx.declMapper->getCreated(lookupDef);
    ASSERT_TRUE(cDef != nullptr);
    if (auto* varDef = dyn_cast<VarDecl>(cDef)) {
        EXPECT_EQ("Table__lookup", varDef->getNameAsString());
        EXPECT_TRUE(varDef->getType()->isArrayType()) << "Should preserve array type";
    } else {
        FAIL() << "Expected VarDecl";
    }
}

// Test 4: Multiple static members in one class
TEST_F(StaticDataMemberIntegrationTest, MultipleStaticMembersInClass) {
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

    // Create context
    auto ctx = createTestContext();
    StaticDataMemberHandler::registerWith(*ctx.dispatcher);

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
    auto staticMembers = StaticDataMemberHandler::detectStaticMembers(Stats);
    EXPECT_EQ(3u, staticMembers.size()) << "Should detect all 3 static members";

    // Generate declarations for all via dispatcher
    std::vector<VarDecl*> declarations;
    for (auto* member : staticMembers) {
        ctx.dispatcher->dispatch(
            AST->getASTContext(),
            ctx.cAST->getASTContext(),
            member
        );
        auto* cDecl = ctx.declMapper->getCreated(member);
        ASSERT_TRUE(cDecl != nullptr);
        if (auto* varDecl = dyn_cast<VarDecl>(cDecl)) {
            declarations.push_back(varDecl);
        } else {
            FAIL() << "Expected VarDecl";
        }
    }

    EXPECT_EQ(3u, declarations.size());

    // Verify all have correct naming pattern
    for (auto* decl : declarations) {
        std::string name = decl->getNameAsString();
        EXPECT_TRUE(name.find("Stats__") == 0) << "All declarations should start with Stats__";
    }
}

// Test 5: Static member in namespaced class
TEST_F(StaticDataMemberIntegrationTest, StaticMemberInNamespacedClass) {
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

    // Create context
    auto ctx = createTestContext();
    StaticDataMemberHandler::registerWith(*ctx.dispatcher);

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
    ctx.dispatcher->dispatch(
        AST->getASTContext(),
        ctx.cAST->getASTContext(),
        valueDef
    );
    auto* cDef = ctx.declMapper->getCreated(valueDef);
    ASSERT_TRUE(cDef != nullptr);
    if (auto* varDef = dyn_cast<VarDecl>(cDef)) {
        EXPECT_EQ("app__Config__value", varDef->getNameAsString())
            << "Should include namespace in mangled name";
    } else {
        FAIL() << "Expected VarDecl";
    }
}

// ============================================================================
// Test Summary: 5 integration tests covering:
// - Out-of-class definitions
// - In-class initializers
// - Array types
// - Multiple members
// - Namespace support
// ============================================================================
