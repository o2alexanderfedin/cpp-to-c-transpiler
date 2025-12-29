/**
 * @file DeclRefExprHandlerDispatcherTest.cpp
 * @brief Unit tests for DeclRefExprHandler dispatcher integration
 *
 * Verifies:
 * - Handler registration with dispatcher
 * - canHandle predicate behavior
 * - DeclRefExpr translation (variables, parameters, functions)
 * - Integration with ExprMapper and DeclMapper
 * - Multiple DeclRefExpr translation
 */

#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/Casting.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

template<typename T>
T* findNode(Stmt* root) {
    if (!root) return nullptr;
    if (auto* node = dyn_cast<T>(root)) return node;
    for (auto* child : root->children()) {
        if (auto* found = findNode<T>(child)) return found;
    }
    return nullptr;
}

// ============================================================================
// Test: DeclRefExprHandler Registration
// ============================================================================

TEST(DeclRefExprHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        int test(int x) { return x; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    DeclRefExpr* declRef = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                declRef = findNode<DeclRefExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(declRef, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, declRef);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreatedExpr(declRef);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<DeclRefExpr>(cExpr));
}

// ============================================================================
// Test: Parameter Reference Translation
// ============================================================================

TEST(DeclRefExprHandlerDispatcherTest, ParameterReference) {
    const char *cpp = R"(
        int add(int a, int b) { return a; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    DeclRefExpr* declRef = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                declRef = findNode<DeclRefExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(declRef, nullptr);
    EXPECT_EQ(declRef->getDecl()->getNameAsString(), "a");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, declRef);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreatedExpr(declRef);
    ASSERT_NE(cExpr, nullptr);

    auto* cDeclRef = dyn_cast<DeclRefExpr>(cExpr);
    ASSERT_NE(cDeclRef, nullptr);
}

// ============================================================================
// Test: Local Variable Reference
// ============================================================================

TEST(DeclRefExprHandlerDispatcherTest, LocalVariableReference) {
    const char *cpp = R"(
        int test() {
            int x = 42;
            return x;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    DeclRefExpr* declRef = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                declRef = findNode<DeclRefExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(declRef, nullptr);
    EXPECT_EQ(declRef->getDecl()->getNameAsString(), "x");

    bool handled = dispatcher.dispatch(cppCtx, cCtx, declRef);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreatedExpr(declRef);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test: Multiple DeclRefExpr in Expression
// ============================================================================

TEST(DeclRefExprHandlerDispatcherTest, MultipleDeclRefExprs) {
    const char *cpp = R"(
        int add(int a, int b) { return a + b; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);

    // Find all DeclRefExprs manually
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<DeclRefExpr*> declRefs;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                // Find both 'a' and 'b' references
                std::function<void(Stmt*)> findAll = [&](Stmt* S) {
                    if (!S) return;
                    if (auto* DR = dyn_cast<DeclRefExpr>(S)) {
                        declRefs.push_back(DR);
                    }
                    for (auto* child : S->children()) {
                        findAll(child);
                    }
                };
                findAll(FD->getBody());
                break;
            }
        }
    }

    ASSERT_EQ(declRefs.size(), 2) << "Should find 2 DeclRefExprs (a and b)";

    // Dispatch both
    for (auto* dr : declRefs) {
        bool handled = dispatcher.dispatch(cppCtx, cCtx, dr);
        EXPECT_TRUE(handled);
    }

    // Verify both were mapped
    for (auto* dr : declRefs) {
        Expr* cExpr = exprMapper.getCreatedExpr(dr);
        EXPECT_NE(cExpr, nullptr);
        EXPECT_TRUE(isa<DeclRefExpr>(cExpr));
    }
}

// ============================================================================
// Test: Non-DeclRefExpr Should Not Be Handled
// ============================================================================

TEST(DeclRefExprHandlerDispatcherTest, NonDeclRefExprNotHandled) {
    const char *cpp = R"(
        int test() { return 42; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper& mapper = cpptoc::PathMapper::getInstance("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    IntegerLiteral* intLit = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                intLit = findNode<IntegerLiteral>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(intLit, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, intLit);
    EXPECT_FALSE(handled) << "IntegerLiteral should not be handled by DeclRefExprHandler";
}
