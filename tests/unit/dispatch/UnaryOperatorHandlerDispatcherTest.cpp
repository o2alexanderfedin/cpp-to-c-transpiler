/**
 * @file UnaryOperatorHandlerDispatcherTest.cpp
 * @brief Unit tests for UnaryOperatorHandler with recursive dispatch
 *
 * Verifies:
 * - Handler registration
 * - Recursive dispatch of operand subexpression
 * - All unary operator types (!, -, ++, --, *, &, ~)
 * - Nested unary operators (!!x, -*x)
 * - Integration with ExprMapper
 * - Integration with other handlers (LiteralHandler, DeclRefExprHandler)
 */

#include "dispatch/UnaryOperatorHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/ParenExprHandler.h"
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
// Test: UnaryOperatorHandler Registration
// ============================================================================

TEST(UnaryOperatorHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        int test(int x) { return -x; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    UnaryOperator* unOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                unOp = findNode<UnaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(unOp, nullptr);
    EXPECT_EQ(unOp->getOpcode(), UO_Minus);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, unOp);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(unOp);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<UnaryOperator>(cExpr));
}

// ============================================================================
// Test: Logical NOT (!)
// ============================================================================

TEST(UnaryOperatorHandlerDispatcherTest, LogicalNOT) {
    const char *cpp = R"(
        bool test(bool x) { return !x; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    UnaryOperator* unOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                unOp = findNode<UnaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(unOp, nullptr);
    EXPECT_EQ(unOp->getOpcode(), UO_LNot);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, unOp);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(unOp);
    ASSERT_NE(cExpr, nullptr);

    auto* cUnOp = dyn_cast<UnaryOperator>(cExpr);
    ASSERT_NE(cUnOp, nullptr);
    EXPECT_EQ(cUnOp->getOpcode(), UO_LNot);
}

// ============================================================================
// Test: Unary Minus (-)
// ============================================================================

TEST(UnaryOperatorHandlerDispatcherTest, UnaryMinus) {
    const char *cpp = R"(
        int test() { return -42; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    UnaryOperator* unOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                unOp = findNode<UnaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(unOp, nullptr);
    EXPECT_EQ(unOp->getOpcode(), UO_Minus);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, unOp);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(unOp);
    ASSERT_NE(cExpr, nullptr);

    auto* cUnOp = dyn_cast<UnaryOperator>(cExpr);
    ASSERT_NE(cUnOp, nullptr);
    EXPECT_EQ(cUnOp->getOpcode(), UO_Minus);

    // Verify operand (literal) was also translated
    EXPECT_TRUE(isa<IntegerLiteral>(cUnOp->getSubExpr()));
}

// ============================================================================
// Test: Prefix Increment (++x)
// ============================================================================

TEST(UnaryOperatorHandlerDispatcherTest, PrefixIncrement) {
    const char *cpp = R"(
        int test(int x) { return ++x; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    UnaryOperator* unOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                unOp = findNode<UnaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(unOp, nullptr);
    EXPECT_EQ(unOp->getOpcode(), UO_PreInc);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, unOp);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(unOp);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test: Prefix Decrement (--x)
// ============================================================================

TEST(UnaryOperatorHandlerDispatcherTest, PrefixDecrement) {
    const char *cpp = R"(
        int test(int x) { return --x; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    UnaryOperator* unOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                unOp = findNode<UnaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(unOp, nullptr);
    EXPECT_EQ(unOp->getOpcode(), UO_PreDec);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, unOp);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(unOp);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test: Address-Of (&x)
// ============================================================================

TEST(UnaryOperatorHandlerDispatcherTest, AddressOf) {
    const char *cpp = R"(
        int* test(int x) { return &x; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    UnaryOperator* unOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                unOp = findNode<UnaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(unOp, nullptr);
    EXPECT_EQ(unOp->getOpcode(), UO_AddrOf);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, unOp);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(unOp);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test: Dereference (*ptr)
// ============================================================================

TEST(UnaryOperatorHandlerDispatcherTest, Dereference) {
    const char *cpp = R"(
        int test(int* ptr) { return *ptr; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    UnaryOperator* unOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                unOp = findNode<UnaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(unOp, nullptr);
    EXPECT_EQ(unOp->getOpcode(), UO_Deref);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, unOp);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(unOp);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test: Bitwise NOT (~)
// ============================================================================

TEST(UnaryOperatorHandlerDispatcherTest, BitwiseNOT) {
    const char *cpp = R"(
        int test(int x) { return ~x; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    UnaryOperator* unOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                unOp = findNode<UnaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(unOp, nullptr);
    EXPECT_EQ(unOp->getOpcode(), UO_Not);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, unOp);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(unOp);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test: Nested Unary Operators (!!x)
// ============================================================================

TEST(UnaryOperatorHandlerDispatcherTest, NestedUnaryOperators) {
    const char *cpp = R"(
        bool test(bool x) { return !!x; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    // Find all unary operators
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<UnaryOperator*> unOps;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                std::function<void(Stmt*)> findAll = [&](Stmt* S) {
                    if (!S) return;
                    if (auto* UO = dyn_cast<UnaryOperator>(S)) {
                        unOps.push_back(UO);
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

    ASSERT_EQ(unOps.size(), 2) << "Should find 2 unary operators (outer and inner !)";

    // Find outer NOT
    UnaryOperator* outer = unOps[0];
    ASSERT_EQ(outer->getOpcode(), UO_LNot);

    // Verify inner is also NOT
    auto* inner = dyn_cast<UnaryOperator>(outer->getSubExpr());
    ASSERT_NE(inner, nullptr);
    ASSERT_EQ(inner->getOpcode(), UO_LNot);

    // Dispatch outer (should recursively dispatch inner)
    bool handled = dispatcher.dispatch(cppCtx, cCtx, outer);
    ASSERT_TRUE(handled);

    // Verify both were translated
    Expr* cOuterExpr = exprMapper.getCreated(outer);
    ASSERT_NE(cOuterExpr, nullptr);

    Expr* cInnerExpr = exprMapper.getCreated(inner);
    ASSERT_NE(cInnerExpr, nullptr);
}

// ============================================================================
// Test: Non-UnaryOperator Should Not Be Handled
// ============================================================================

TEST(UnaryOperatorHandlerDispatcherTest, NonUnaryOperatorNotHandled) {
    const char *cpp = R"(
        int test() { return 42; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext& targetCtx = TargetContext::getInstance();
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper("/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

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
    EXPECT_FALSE(handled) << "IntegerLiteral should not be handled by UnaryOperatorHandler";
}
