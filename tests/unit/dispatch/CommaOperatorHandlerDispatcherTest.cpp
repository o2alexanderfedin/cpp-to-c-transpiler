/**
 * @file CommaOperatorHandlerDispatcherTest.cpp
 * @brief Unit tests for CommaOperatorHandler with recursive dispatch
 *
 * Verifies:
 * - Handler registration
 * - Recursive dispatch of LHS and RHS subexpressions
 * - Basic comma expressions (a, b)
 * - Nested comma expressions ((a, b), c) and (a, (b, c))
 * - Comma operator in for-loop initialization and increment
 * - Integration with ExprMapper
 * - Predicate correctness
 */

#include "dispatch/CommaOperatorHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/UnaryOperatorHandler.h"
#include "dispatch/ParenExprHandler.h"
#include "dispatch/BinaryOperatorHandler.h"
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

// Helper to find all nodes of a specific type
template<typename T>
void findAllNodes(Stmt* root, std::vector<T*>& results) {
    if (!root) return;
    if (auto* node = dyn_cast<T>(root)) {
        results.push_back(node);
    }
    for (auto* child : root->children()) {
        findAllNodes<T>(child, results);
    }
}

// ============================================================================
// Test: CommaOperatorHandler Registration
// ============================================================================

TEST(CommaOperatorHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        int test() {
            int a = 1, b = 2;
            return (a, b);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::CommaOperatorHandler::registerWith(dispatcher);

    // Find comma operator in return statement
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    BinaryOperator* commaOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                // Find the return statement
                if (auto* CS = dyn_cast<CompoundStmt>(FD->getBody())) {
                    for (auto* stmt : CS->body()) {
                        if (auto* RS = dyn_cast<ReturnStmt>(stmt)) {
                            commaOp = findNode<BinaryOperator>(RS);
                            if (commaOp && commaOp->getOpcode() == BO_Comma) {
                                break;
                            }
                        }
                    }
                }
                break;
            }
        }
    }

    ASSERT_NE(commaOp, nullptr) << "Could not find comma operator";
    EXPECT_EQ(commaOp->getOpcode(), BO_Comma);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, commaOp);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(commaOp);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<BinaryOperator>(cExpr));
    if (auto* cBinOp = dyn_cast<BinaryOperator>(cExpr)) {
        EXPECT_EQ(cBinOp->getOpcode(), BO_Comma);
    }
}

// ============================================================================
// Test: Basic Comma Expression (a, b)
// ============================================================================

TEST(CommaOperatorHandlerDispatcherTest, BasicCommaExpression) {
    const char *cpp = R"(
        int test() {
            int a = 10, b = 20;
            return (a, b);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::CommaOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    BinaryOperator* commaOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                if (auto* CS = dyn_cast<CompoundStmt>(FD->getBody())) {
                    for (auto* stmt : CS->body()) {
                        if (auto* RS = dyn_cast<ReturnStmt>(stmt)) {
                            commaOp = findNode<BinaryOperator>(RS);
                            if (commaOp && commaOp->getOpcode() == BO_Comma) {
                                break;
                            }
                        }
                    }
                }
                break;
            }
        }
    }

    ASSERT_NE(commaOp, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, commaOp);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(commaOp);
    ASSERT_NE(cExpr, nullptr);

    auto* cCommaOp = dyn_cast<BinaryOperator>(cExpr);
    ASSERT_NE(cCommaOp, nullptr);
    EXPECT_EQ(cCommaOp->getOpcode(), BO_Comma);

    // Verify LHS and RHS were also translated
    EXPECT_NE(cCommaOp->getLHS(), nullptr);
    EXPECT_NE(cCommaOp->getRHS(), nullptr);
}

// ============================================================================
// Test: Nested Comma Expressions ((a, b), c)
// ============================================================================

TEST(CommaOperatorHandlerDispatcherTest, NestedCommaLeft) {
    const char *cpp = R"(
        int test() {
            int a = 1, b = 2, c = 3;
            return ((a, b), c);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::CommaOperatorHandler::registerWith(dispatcher);

    // Find all comma operators
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<BinaryOperator*> commaOps;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                findAllNodes<BinaryOperator>(FD->getBody(), commaOps);
                break;
            }
        }
    }

    // Filter for BO_Comma only
    std::vector<BinaryOperator*> filteredCommaOps;
    for (auto* op : commaOps) {
        if (op->getOpcode() == BO_Comma) {
            filteredCommaOps.push_back(op);
        }
    }

    ASSERT_EQ(filteredCommaOps.size(), 2) << "Should find 2 comma operators";

    // Find the outer comma operator
    BinaryOperator* outerComma = nullptr;
    for (auto* op : filteredCommaOps) {
        // The outer one has another comma as LHS
        if (auto* lhs = dyn_cast<BinaryOperator>(op->getLHS()->IgnoreParens())) {
            if (lhs->getOpcode() == BO_Comma) {
                outerComma = op;
                break;
            }
        }
    }

    ASSERT_NE(outerComma, nullptr);

    // Dispatch outer (should recursively dispatch inner)
    bool handled = dispatcher.dispatch(cppCtx, cCtx, outerComma);
    ASSERT_TRUE(handled);

    // Verify both outer and inner were translated
    Expr* cOuterExpr = exprMapper.getCreated(outerComma);
    ASSERT_NE(cOuterExpr, nullptr);

    auto* innerComma = dyn_cast<BinaryOperator>(outerComma->getLHS()->IgnoreParens());
    ASSERT_NE(innerComma, nullptr);
    Expr* cInnerExpr = exprMapper.getCreated(innerComma);
    ASSERT_NE(cInnerExpr, nullptr);
}

// ============================================================================
// Test: Nested Comma Expressions (a, (b, c))
// ============================================================================

TEST(CommaOperatorHandlerDispatcherTest, NestedCommaRight) {
    const char *cpp = R"(
        int test() {
            int a = 1, b = 2, c = 3;
            return (a, (b, c));
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::CommaOperatorHandler::registerWith(dispatcher);

    // Find all comma operators
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<BinaryOperator*> commaOps;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                findAllNodes<BinaryOperator>(FD->getBody(), commaOps);
                break;
            }
        }
    }

    // Filter for BO_Comma only
    std::vector<BinaryOperator*> filteredCommaOps;
    for (auto* op : commaOps) {
        if (op->getOpcode() == BO_Comma) {
            filteredCommaOps.push_back(op);
        }
    }

    ASSERT_EQ(filteredCommaOps.size(), 2) << "Should find 2 comma operators";

    // Find the outer comma operator
    BinaryOperator* outerComma = nullptr;
    for (auto* op : filteredCommaOps) {
        // The outer one has another comma as RHS
        if (auto* rhs = dyn_cast<BinaryOperator>(op->getRHS()->IgnoreParens())) {
            if (rhs->getOpcode() == BO_Comma) {
                outerComma = op;
                break;
            }
        }
    }

    ASSERT_NE(outerComma, nullptr);

    // Dispatch outer (should recursively dispatch inner)
    bool handled = dispatcher.dispatch(cppCtx, cCtx, outerComma);
    ASSERT_TRUE(handled);

    // Verify both outer and inner were translated
    Expr* cOuterExpr = exprMapper.getCreated(outerComma);
    ASSERT_NE(cOuterExpr, nullptr);

    auto* innerComma = dyn_cast<BinaryOperator>(outerComma->getRHS()->IgnoreParens());
    ASSERT_NE(innerComma, nullptr);
    Expr* cInnerExpr = exprMapper.getCreated(innerComma);
    ASSERT_NE(cInnerExpr, nullptr);
}

// ============================================================================
// Test: Comma in For-Loop Initialization
// ============================================================================

TEST(CommaOperatorHandlerDispatcherTest, ForLoopInitialization) {
    const char *cpp = R"(
        void test() {
            for (int i = 0, j = 10; i < j; i++, j--) {
                // loop body
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::CommaOperatorHandler::registerWith(dispatcher);

    // Find comma operator in for-loop increment
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<BinaryOperator*> commaOps;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                findAllNodes<BinaryOperator>(FD->getBody(), commaOps);
                break;
            }
        }
    }

    // Filter for BO_Comma
    std::vector<BinaryOperator*> filteredCommaOps;
    for (auto* op : commaOps) {
        if (op->getOpcode() == BO_Comma) {
            filteredCommaOps.push_back(op);
        }
    }

    // Should find at least one comma operator in the increment part
    ASSERT_GE(filteredCommaOps.size(), 1) << "Should find at least 1 comma operator";

    // Dispatch the first comma operator
    bool handled = dispatcher.dispatch(cppCtx, cCtx, filteredCommaOps[0]);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(filteredCommaOps[0]);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test: Predicate Correctness
// ============================================================================

TEST(CommaOperatorHandlerDispatcherTest, PredicateCorrectness) {
    const char *cpp = R"(
        int test() {
            int a = 1, b = 2;
            int c = a + b;    // Plus operator, not comma
            return (a, b);    // Comma operator
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<BinaryOperator*> binOps;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                findAllNodes<BinaryOperator>(FD->getBody(), binOps);
                break;
            }
        }
    }

    ASSERT_GE(binOps.size(), 2) << "Should find at least 2 binary operators";

    // Find comma operator and plus operator
    BinaryOperator* commaOp = nullptr;
    BinaryOperator* plusOp = nullptr;

    for (auto* op : binOps) {
        if (op->getOpcode() == BO_Comma) {
            commaOp = op;
        } else if (op->getOpcode() == BO_Add) {
            plusOp = op;
        }
    }

    ASSERT_NE(commaOp, nullptr) << "Should find comma operator";
    ASSERT_NE(plusOp, nullptr) << "Should find plus operator";

    // Test predicate
    EXPECT_TRUE(cpptoc::CommaOperatorHandler::canHandle(commaOp))
        << "Predicate should return true for comma operator";
    EXPECT_FALSE(cpptoc::CommaOperatorHandler::canHandle(plusOp))
        << "Predicate should return false for plus operator";
}

// ============================================================================
// Test: Integration with ExprMapper - Deduplication
// ============================================================================

TEST(CommaOperatorHandlerDispatcherTest, ExprMapperDeduplication) {
    const char *cpp = R"(
        int test() {
            int a = 1, b = 2;
            return (a, b);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::CommaOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    BinaryOperator* commaOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                if (auto* CS = dyn_cast<CompoundStmt>(FD->getBody())) {
                    for (auto* stmt : CS->body()) {
                        if (auto* RS = dyn_cast<ReturnStmt>(stmt)) {
                            commaOp = findNode<BinaryOperator>(RS);
                            if (commaOp && commaOp->getOpcode() == BO_Comma) {
                                break;
                            }
                        }
                    }
                }
                break;
            }
        }
    }

    ASSERT_NE(commaOp, nullptr);

    // Dispatch once
    bool handled1 = dispatcher.dispatch(cppCtx, cCtx, commaOp);
    ASSERT_TRUE(handled1);

    Expr* cExpr1 = exprMapper.getCreated(commaOp);
    ASSERT_NE(cExpr1, nullptr);

    // Dispatch again - should be deduplicated
    bool handled2 = dispatcher.dispatch(cppCtx, cCtx, commaOp);
    EXPECT_TRUE(handled2);

    Expr* cExpr2 = exprMapper.getCreated(commaOp);
    ASSERT_NE(cExpr2, nullptr);

    // Should return the same C expression (deduplicated)
    EXPECT_EQ(cExpr1, cExpr2) << "ExprMapper should deduplicate and return same C expression";
}
