/**
 * @file NamespaceHandlerDispatcherTest.cpp
 * @brief Unit tests for NamespaceHandler with dispatcher integration
 *
 * Verifies:
 * - Handler registration
 * - Basic namespace tracking
 * - Nested namespace path computation (A::B → A_B)
 * - Anonymous namespace ID generation
 * - Function in namespace (dispatch integration)
 * - Class in namespace (dispatch integration)
 * - Already-processed detection
 * - Namespace path computation accuracy
 */

#include "dispatch/NamespaceHandler.h"
#include "dispatch/FunctionHandler.h"
#include "dispatch/ParameterHandler.h"
#include "dispatch/RecordHandler.h"
#include "dispatch/TypeHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/Casting.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

template<typename T>
T* findDecl(TranslationUnitDecl* TU, const std::string& name) {
    for (auto* D : TU->decls()) {
        if (auto* ND = dyn_cast<NamedDecl>(D)) {
            if (ND->getNameAsString() == name) {
                if (auto* Result = dyn_cast<T>(ND)) {
                    return Result;
                }
            }
        }
        // Check nested declarations within namespaces
        if (auto* DC = dyn_cast<DeclContext>(D)) {
            for (auto* Inner : DC->decls()) {
                if (auto* ND = dyn_cast<NamedDecl>(Inner)) {
                    if (ND->getNameAsString() == name) {
                        if (auto* Result = dyn_cast<T>(ND)) {
                            return Result;
                        }
                    }
                }
            }
        }
    }
    return nullptr;
}

// Find NamespaceDecl by name
NamespaceDecl* findNamespace(TranslationUnitDecl* TU, const std::string& name) {
    for (auto* D : TU->decls()) {
        if (auto* NS = dyn_cast<NamespaceDecl>(D)) {
            if (!NS->isAnonymousNamespace() && NS->getNameAsString() == name) {
                return NS;
            }
        }
    }
    return nullptr;
}

// Find first anonymous namespace
NamespaceDecl* findAnonymousNamespace(TranslationUnitDecl* TU) {
    for (auto* D : TU->decls()) {
        if (auto* NS = dyn_cast<NamespaceDecl>(D)) {
            if (NS->isAnonymousNamespace()) {
                return NS;
            }
        }
    }
    return nullptr;
}

// ============================================================================
// Test: NamespaceHandler Registration
// ============================================================================

TEST(NamespaceHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        namespace MyApp {
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::NamespaceHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    NamespaceDecl* cppNS = findNamespace(TU, "MyApp");
    ASSERT_NE(cppNS, nullptr);

    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppNS);
    EXPECT_TRUE(handled);

    // Verify namespace was tracked (stored with nullptr since C has no namespaces)
    EXPECT_TRUE(declMapper.hasCreated(cppNS));
}

// ============================================================================
// Test: Basic Namespace (single level)
// ============================================================================

TEST(NamespaceHandlerDispatcherTest, BasicNamespace) {
    const char *cpp = R"(
        namespace MyApp {
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::NamespaceHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    NamespaceDecl* cppNS = findNamespace(TU, "MyApp");
    ASSERT_NE(cppNS, nullptr);
    EXPECT_EQ(cppNS->getNameAsString(), "MyApp");

    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppNS);
    ASSERT_TRUE(handled);

    // Verify namespace was tracked
    EXPECT_TRUE(declMapper.hasCreated(cppNS));

    // Verify NO C declaration created (C has no namespaces)
    Decl* cDecl = declMapper.getCreated(cppNS);
    EXPECT_EQ(cDecl, nullptr) << "C has no namespaces, should store nullptr";
}

// ============================================================================
// Test: Nested Namespaces (A::B → A_B path computation)
// ============================================================================

TEST(NamespaceHandlerDispatcherTest, NestedNamespaces) {
    const char *cpp = R"(
        namespace A {
            namespace B {
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::NamespaceHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    NamespaceDecl* cppNS_A = findNamespace(TU, "A");
    ASSERT_NE(cppNS_A, nullptr);

    // Dispatch outer namespace A
    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled_A = dispatcher.dispatch(cppCtx, cCtx, cppNS_A);
    ASSERT_TRUE(handled_A);
    EXPECT_TRUE(declMapper.hasCreated(cppNS_A));

    // Find nested namespace B
    NamespaceDecl* cppNS_B = nullptr;
    for (auto* D : cppNS_A->decls()) {
        if (auto* NS = dyn_cast<NamespaceDecl>(D)) {
            if (NS->getNameAsString() == "B") {
                cppNS_B = NS;
                break;
            }
        }
    }
    ASSERT_NE(cppNS_B, nullptr);

    // Verify nested namespace B was processed by recursive dispatch
    EXPECT_TRUE(declMapper.hasCreated(cppNS_B));

    // Test namespace path computation
    std::string path_B = cpptoc::NamespaceHandler::getNamespacePath(cppNS_B);
    EXPECT_EQ(path_B, "A__B") << "Nested namespace path should be A__B";
}

// ============================================================================
// Test: C++17 Nested Namespace Syntax (namespace A::B::C)
// ============================================================================

TEST(NamespaceHandlerDispatcherTest, Cpp17NestedNamespaceSyntax) {
    const char *cpp = R"(
        namespace A::B::C {
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::NamespaceHandler::registerWith(dispatcher);

    // C++17 syntax creates nested NamespaceDecls
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    NamespaceDecl* cppNS_A = findNamespace(TU, "A");
    ASSERT_NE(cppNS_A, nullptr);

    // Dispatch outer namespace
    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppNS_A);
    ASSERT_TRUE(handled);

    // Find innermost namespace C
    NamespaceDecl* cppNS_B = nullptr;
    for (auto* D : cppNS_A->decls()) {
        if (auto* NS = dyn_cast<NamespaceDecl>(D)) {
            if (NS->getNameAsString() == "B") {
                cppNS_B = NS;
                break;
            }
        }
    }
    ASSERT_NE(cppNS_B, nullptr);

    NamespaceDecl* cppNS_C = nullptr;
    for (auto* D : cppNS_B->decls()) {
        if (auto* NS = dyn_cast<NamespaceDecl>(D)) {
            if (NS->getNameAsString() == "C") {
                cppNS_C = NS;
                break;
            }
        }
    }
    ASSERT_NE(cppNS_C, nullptr);

    // Test namespace path for innermost namespace
    std::string path_C = cpptoc::NamespaceHandler::getNamespacePath(cppNS_C);
    EXPECT_EQ(path_C, "A__B__C") << "C++17 nested namespace path should be A__B__C";
}

// ============================================================================
// Test: Anonymous Namespace (deterministic ID generation)
// ============================================================================

TEST(NamespaceHandlerDispatcherTest, AnonymousNamespace) {
    const char *cpp = R"(
        namespace {
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::NamespaceHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    NamespaceDecl* cppNS = findAnonymousNamespace(TU);
    ASSERT_NE(cppNS, nullptr);
    EXPECT_TRUE(cppNS->isAnonymousNamespace());

    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppNS);
    ASSERT_TRUE(handled);

    // Verify anonymous namespace was tracked
    EXPECT_TRUE(declMapper.hasCreated(cppNS));

    // Test ID generation (should be deterministic)
    const SourceManager& SM = cppCtx.getSourceManager();
    std::string id = cpptoc::NamespaceHandler::generateAnonymousID(cppNS, SM);
    EXPECT_TRUE(id.find("__anon_") == 0) << "Anonymous namespace ID should start with __anon_";
    EXPECT_GT(id.length(), 7) << "Anonymous namespace ID should have hash suffix";
}

// ============================================================================
// Test: Function in Namespace (dispatch integration)
// ============================================================================

TEST(NamespaceHandlerDispatcherTest, FunctionInNamespace) {
    const char *cpp = R"(
        namespace MyApp {
            void foo();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::NamespaceHandler::registerWith(dispatcher);
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::FunctionHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    NamespaceDecl* cppNS = findNamespace(TU, "MyApp");
    ASSERT_NE(cppNS, nullptr);

    // Dispatch namespace (should recursively dispatch function)
    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppNS);
    ASSERT_TRUE(handled);

    // Verify namespace was tracked
    EXPECT_TRUE(declMapper.hasCreated(cppNS));

    // Find function foo in namespace
    FunctionDecl* cppFunc = nullptr;
    for (auto* D : cppNS->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "foo") {
                cppFunc = FD;
                break;
            }
        }
    }
    ASSERT_NE(cppFunc, nullptr) << "Function foo should exist in namespace";

    // Verify function was processed by recursive dispatch
    // Note: FunctionHandler uses PathMapper, not DeclMapper
    // So we check if the function was registered in PathMapper
    std::string targetPath = dispatcher.getTargetPath(cppCtx, cppFunc);
    EXPECT_FALSE(targetPath.empty()) << "Function should have target path after translation";
}

// ============================================================================
// Test: Class in Namespace (dispatch integration)
// ============================================================================

TEST(NamespaceHandlerDispatcherTest, ClassInNamespace) {
    const char *cpp = R"(
        namespace MyApp {
            struct Point {
                int x;
                int y;
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::NamespaceHandler::registerWith(dispatcher);
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::RecordHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    NamespaceDecl* cppNS = findNamespace(TU, "MyApp");
    ASSERT_NE(cppNS, nullptr);

    // Dispatch namespace (should recursively dispatch struct)
    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, cppNS);
    ASSERT_TRUE(handled);

    // Verify namespace was tracked
    EXPECT_TRUE(declMapper.hasCreated(cppNS));

    // Find struct Point in namespace
    RecordDecl* cppStruct = nullptr;
    for (auto* D : cppNS->decls()) {
        if (auto* RD = dyn_cast<RecordDecl>(D)) {
            if (RD->getNameAsString() == "Point") {
                cppStruct = RD;
                break;
            }
        }
    }
    ASSERT_NE(cppStruct, nullptr) << "Struct Point should exist in namespace";

    // Verify struct was processed by recursive dispatch
    EXPECT_TRUE(declMapper.hasCreated(cppStruct)) << "Struct should be translated by recursive dispatch";
}

// ============================================================================
// Test: Already-Processed Detection
// ============================================================================

TEST(NamespaceHandlerDispatcherTest, DuplicateDetection) {
    const char *cpp = R"(
        namespace MyApp {
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper& declMapper = cpptoc::DeclMapper::getInstance();
    cpptoc::TypeMapper& typeMapper = cpptoc::TypeMapper::getInstance();
    cpptoc::ExprMapper& exprMapper = cpptoc::ExprMapper::getInstance();
    cpptoc::StmtMapper& stmtMapper = cpptoc::StmtMapper::getInstance();

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::NamespaceHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    NamespaceDecl* cppNS = findNamespace(TU, "MyApp");
    ASSERT_NE(cppNS, nullptr);

    // First dispatch
    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled1 = dispatcher.dispatch(cppCtx, cCtx, cppNS);
    ASSERT_TRUE(handled1);
    EXPECT_TRUE(declMapper.hasCreated(cppNS));

    // Second dispatch should detect duplicate and return early
    // Set current target path for file origin check
    dispatcher.setCurrentTargetPath("input");

    bool handled2 = dispatcher.dispatch(cppCtx, cCtx, cppNS);
    EXPECT_TRUE(handled2);

    // Should still have same mapping
    EXPECT_TRUE(declMapper.hasCreated(cppNS));
}

// ============================================================================
// Test: Namespace Path Computation (helper function)
// ============================================================================

TEST(NamespaceHandlerDispatcherTest, NamespacePathComputation) {
    const char *cpp = R"(
        namespace A {
            namespace B {
                namespace C {
                }
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    NamespaceDecl* cppNS_A = findNamespace(TU, "A");
    ASSERT_NE(cppNS_A, nullptr);

    // Find B
    NamespaceDecl* cppNS_B = nullptr;
    for (auto* D : cppNS_A->decls()) {
        if (auto* NS = dyn_cast<NamespaceDecl>(D)) {
            if (NS->getNameAsString() == "B") {
                cppNS_B = NS;
                break;
            }
        }
    }
    ASSERT_NE(cppNS_B, nullptr);

    // Find C
    NamespaceDecl* cppNS_C = nullptr;
    for (auto* D : cppNS_B->decls()) {
        if (auto* NS = dyn_cast<NamespaceDecl>(D)) {
            if (NS->getNameAsString() == "C") {
                cppNS_C = NS;
                break;
            }
        }
    }
    ASSERT_NE(cppNS_C, nullptr);

    // Test path computation at each level
    std::string path_A = cpptoc::NamespaceHandler::getNamespacePath(cppNS_A);
    EXPECT_EQ(path_A, "A") << "Single namespace should be just 'A'";

    std::string path_B = cpptoc::NamespaceHandler::getNamespacePath(cppNS_B);
    EXPECT_EQ(path_B, "A__B") << "Nested namespace should be 'A__B'";

    std::string path_C = cpptoc::NamespaceHandler::getNamespacePath(cppNS_C);
    EXPECT_EQ(path_C, "A__B__C") << "Triple nested namespace should be 'A__B__C'";
}
