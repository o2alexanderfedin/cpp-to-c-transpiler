/**
 * @file BinaryOperatorHandlerDispatcherTest.cpp
 * @brief Unit tests for BinaryOperatorHandler with recursive dispatch
 *
 * Verifies:
 * - Handler registration
 * - Recursive dispatch of LHS and RHS subexpressions
 * - All binary operator types (arithmetic, comparison, logical, bitwise)
 * - Nested expressions (a + (b * c))
 * - Deep recursion ((a + b) * (c - d))
 * - Integration with ExprMapper
 * - Integration with other handlers (LiteralHandler, DeclRefExprHandler)
 */

#include "dispatch/BinaryOperatorHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/UnaryOperatorHandler.h"
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
// Test: BinaryOperatorHandler Registration
// ============================================================================

TEST(BinaryOperatorHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        int test() { return 1 + 2; }
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    BinaryOperator* binOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                binOp = findNode<BinaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), BO_Add);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, binOp);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(binOp);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<BinaryOperator>(cExpr));
}

// ============================================================================
// Test: Addition Operator with Literals
// ============================================================================

TEST(BinaryOperatorHandlerDispatcherTest, AdditionWithLiterals) {
    const char *cpp = R"(
        int test() { return 10 + 20; }
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    BinaryOperator* binOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                binOp = findNode<BinaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(binOp, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, binOp);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(binOp);
    ASSERT_NE(cExpr, nullptr);

    auto* cBinOp = dyn_cast<BinaryOperator>(cExpr);
    ASSERT_NE(cBinOp, nullptr);
    EXPECT_EQ(cBinOp->getOpcode(), BO_Add);

    // Verify LHS and RHS were also translated
    EXPECT_TRUE(isa<IntegerLiteral>(cBinOp->getLHS()));
    EXPECT_TRUE(isa<IntegerLiteral>(cBinOp->getRHS()));
}

// ============================================================================
// Test: Subtraction, Multiplication, Division, Modulo
// ============================================================================

TEST(BinaryOperatorHandlerDispatcherTest, ArithmeticOperators) {
    const char *cpp = R"(
        int test() {
            int a = 10 - 5;
            int b = 3 * 4;
            int c = 20 / 4;
            int d = 7 % 3;
            return a + b + c + d;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);

    // Find all binary operators
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<BinaryOperator*> binOps;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                std::function<void(Stmt*)> findAll = [&](Stmt* S) {
                    if (!S) return;
                    if (auto* BO = dyn_cast<BinaryOperator>(S)) {
                        binOps.push_back(BO);
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

    ASSERT_GE(binOps.size(), 4) << "Should find at least 4 binary operators";

    // Dispatch all operators
    for (auto* bo : binOps) {
        dispatcher.dispatch(cppCtx, cCtx, bo);
    }

    // Verify all were translated
    for (auto* bo : binOps) {
        Expr* cExpr = exprMapper.getCreated(bo);
        EXPECT_NE(cExpr, nullptr);
    }
}

// ============================================================================
// Test: Comparison Operators (==, !=, <, >, <=, >=)
// ============================================================================

TEST(BinaryOperatorHandlerDispatcherTest, ComparisonOperators) {
    const char *cpp = R"(
        bool test(int a, int b) {
            return a == b || a != b || a < b || a > b || a <= b || a >= b;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<BinaryOperator*> binOps;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                std::function<void(Stmt*)> findAll = [&](Stmt* S) {
                    if (!S) return;
                    if (auto* BO = dyn_cast<BinaryOperator>(S)) {
                        binOps.push_back(BO);
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

    ASSERT_GE(binOps.size(), 6) << "Should find at least 6 comparison operators";

    for (auto* bo : binOps) {
        dispatcher.dispatch(cppCtx, cCtx, bo);
    }

    for (auto* bo : binOps) {
        Expr* cExpr = exprMapper.getCreated(bo);
        EXPECT_NE(cExpr, nullptr);
    }
}

// ============================================================================
// Test: Logical Operators (&&, ||)
// ============================================================================

TEST(BinaryOperatorHandlerDispatcherTest, LogicalOperators) {
    const char *cpp = R"(
        bool test(bool a, bool b) {
            return a && b || !a;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    BinaryOperator* binOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                binOp = findNode<BinaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(binOp, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, binOp);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(binOp);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test: Nested Expressions (a + (b * c))
// ============================================================================

TEST(BinaryOperatorHandlerDispatcherTest, NestedExpressions) {
    const char *cpp = R"(
        int test(int a, int b, int c) {
            return a + (b * c);
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    // Find outer addition
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    BinaryOperator* outerAdd = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                outerAdd = findNode<BinaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(outerAdd, nullptr);
    EXPECT_EQ(outerAdd->getOpcode(), BO_Add);

    // Verify RHS is multiplication
    auto* innerMul = dyn_cast<BinaryOperator>(outerAdd->getRHS()->IgnoreParens());
    ASSERT_NE(innerMul, nullptr);
    EXPECT_EQ(innerMul->getOpcode(), BO_Mul);

    // Dispatch outer (should recursively dispatch inner)
    bool handled = dispatcher.dispatch(cppCtx, cCtx, outerAdd);
    ASSERT_TRUE(handled);

    // Verify both outer and inner were translated
    Expr* cOuterExpr = exprMapper.getCreated(outerAdd);
    ASSERT_NE(cOuterExpr, nullptr);

    Expr* cInnerExpr = exprMapper.getCreated(innerMul);
    ASSERT_NE(cInnerExpr, nullptr);

    auto* cOuterBinOp = dyn_cast<BinaryOperator>(cOuterExpr);
    ASSERT_NE(cOuterBinOp, nullptr);
    EXPECT_EQ(cOuterBinOp->getOpcode(), BO_Add);
}

// ============================================================================
// Test: Deep Recursion ((a + b) * (c - d))
// ============================================================================

TEST(BinaryOperatorHandlerDispatcherTest, DeepRecursion) {
    const char *cpp = R"(
        int test(int a, int b, int c, int d) {
            return (a + b) * (c - d);
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    // Find all binary operators
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<BinaryOperator*> binOps;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                std::function<void(Stmt*)> findAll = [&](Stmt* S) {
                    if (!S) return;
                    if (auto* BO = dyn_cast<BinaryOperator>(S)) {
                        binOps.push_back(BO);
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

    ASSERT_EQ(binOps.size(), 3) << "Should find 3 binary operators: *, +, -";

    // Find the root (multiplication)
    BinaryOperator* root = nullptr;
    for (auto* bo : binOps) {
        if (bo->getOpcode() == BO_Mul) {
            root = bo;
            break;
        }
    }
    ASSERT_NE(root, nullptr);

    // Dispatch root (should recursively dispatch all children)
    bool handled = dispatcher.dispatch(cppCtx, cCtx, root);
    ASSERT_TRUE(handled);

    // Verify all 3 operators were translated
    for (auto* bo : binOps) {
        Expr* cExpr = exprMapper.getCreated(bo);
        EXPECT_NE(cExpr, nullptr) << "Operator not translated: "
            << BinaryOperator::getOpcodeStr(bo->getOpcode()).str();
    }
}

// ============================================================================
// Test: Mixed Types (comparison with arithmetic)
// ============================================================================

TEST(BinaryOperatorHandlerDispatcherTest, MixedTypes) {
    const char *cpp = R"(
        bool test(int x, int y) {
            return (x + 5) > (y - 3);
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    BinaryOperator* root = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                root = findNode<BinaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(root, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, root);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(root);
    EXPECT_NE(cExpr, nullptr);
}
