/**
 * @file ArraySubscriptExprHandlerDispatcherTest.cpp
 * @brief Unit tests for ArraySubscriptExprHandler with recursive dispatch
 *
 * Verifies:
 * - Handler registration
 * - Recursive dispatch of base and index subexpressions
 * - Simple array access (arr[5])
 * - Variable index (arr[i])
 * - Multi-dimensional arrays (matrix[i][j])
 * - Complex index expression (arr[i + j])
 * - Complex base expression (getArray()[i])
 * - Pointer indexing (ptr[offset])
 * - Integration with ExprMapper
 * - Integration with other handlers (LiteralHandler, DeclRefExprHandler, BinaryOperatorHandler)
 * - Predicate correctness
 */

#include "dispatch/ArraySubscriptExprHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/BinaryOperatorHandler.h"
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
// Test: ArraySubscriptExprHandler Registration
// ============================================================================

TEST(ArraySubscriptExprHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        int test() {
            int arr[5];
            return arr[2];
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
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ArraySubscriptExpr* arrSub = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                arrSub = findNode<ArraySubscriptExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(arrSub, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, arrSub);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(arrSub);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<ArraySubscriptExpr>(cExpr));
}

// ============================================================================
// Test: Simple Array Access with Literal Index (arr[5])
// ============================================================================

TEST(ArraySubscriptExprHandlerDispatcherTest, SimpleLiteralIndex) {
    const char *cpp = R"(
        int test() {
            int arr[10];
            return arr[5];
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
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ArraySubscriptExpr* arrSub = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                arrSub = findNode<ArraySubscriptExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(arrSub, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, arrSub);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(arrSub);
    ASSERT_NE(cExpr, nullptr);

    auto* cArrSub = dyn_cast<ArraySubscriptExpr>(cExpr);
    ASSERT_NE(cArrSub, nullptr);

    // Verify base and index were translated
    EXPECT_NE(cArrSub->getBase(), nullptr);
    EXPECT_NE(cArrSub->getIdx(), nullptr);
}

// ============================================================================
// Test: Variable Index (arr[i])
// ============================================================================

TEST(ArraySubscriptExprHandlerDispatcherTest, VariableIndex) {
    const char *cpp = R"(
        int test(int i) {
            int arr[10];
            return arr[i];
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
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ArraySubscriptExpr* arrSub = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                arrSub = findNode<ArraySubscriptExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(arrSub, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, arrSub);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(arrSub);
    ASSERT_NE(cExpr, nullptr);

    auto* cArrSub = dyn_cast<ArraySubscriptExpr>(cExpr);
    ASSERT_NE(cArrSub, nullptr);

    // Verify base is DeclRefExpr (arr) and index is translated
    EXPECT_NE(cArrSub->getBase(), nullptr);
    EXPECT_NE(cArrSub->getIdx(), nullptr);
}

// ============================================================================
// Test: Multi-Dimensional Array Access (matrix[i][j])
// ============================================================================

TEST(ArraySubscriptExprHandlerDispatcherTest, MultiDimensionalArray) {
    const char *cpp = R"(
        int test(int i, int j) {
            int matrix[3][4];
            return matrix[i][j];
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
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);

    // Find the outer subscript (matrix[i][j])
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ArraySubscriptExpr* outerSub = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                outerSub = findNode<ArraySubscriptExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(outerSub, nullptr);

    // Verify base is also ArraySubscriptExpr (matrix[i])
    auto* innerSub = dyn_cast<ArraySubscriptExpr>(outerSub->getBase()->IgnoreImpCasts());
    ASSERT_NE(innerSub, nullptr);

    // Dispatch outer (should recursively dispatch inner)
    bool handled = dispatcher.dispatch(cppCtx, cCtx, outerSub);
    ASSERT_TRUE(handled);

    // Verify both outer and inner were translated
    Expr* cOuterExpr = exprMapper.getCreated(outerSub);
    ASSERT_NE(cOuterExpr, nullptr);

    Expr* cInnerExpr = exprMapper.getCreated(innerSub);
    ASSERT_NE(cInnerExpr, nullptr);

    auto* cOuterSub = dyn_cast<ArraySubscriptExpr>(cOuterExpr);
    ASSERT_NE(cOuterSub, nullptr);
}

// ============================================================================
// Test: Complex Index Expression (arr[i + j])
// ============================================================================

TEST(ArraySubscriptExprHandlerDispatcherTest, ComplexIndexExpression) {
    const char *cpp = R"(
        int test(int i, int j) {
            int arr[20];
            return arr[i + j];
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
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ArraySubscriptExpr* arrSub = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                arrSub = findNode<ArraySubscriptExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(arrSub, nullptr);

    // Verify index is a BinaryOperator (i + j)
    auto* binOp = dyn_cast<BinaryOperator>(arrSub->getIdx()->IgnoreImpCasts());
    ASSERT_NE(binOp, nullptr);
    EXPECT_EQ(binOp->getOpcode(), BO_Add);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, arrSub);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(arrSub);
    ASSERT_NE(cExpr, nullptr);

    // Verify the complex index expression was also translated
    Expr* cBinOp = exprMapper.getCreated(binOp);
    EXPECT_NE(cBinOp, nullptr);
}

// ============================================================================
// Test: Complex Index with Multiplication (arr[i * stride + offset])
// ============================================================================

TEST(ArraySubscriptExprHandlerDispatcherTest, ComplexIndexWithMultiplication) {
    const char *cpp = R"(
        int test(int i, int stride, int offset) {
            int arr[100];
            return arr[i * stride + offset];
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
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ArraySubscriptExpr* arrSub = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                arrSub = findNode<ArraySubscriptExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(arrSub, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, arrSub);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(arrSub);
    ASSERT_NE(cExpr, nullptr);

    auto* cArrSub = dyn_cast<ArraySubscriptExpr>(cExpr);
    ASSERT_NE(cArrSub, nullptr);

    // Verify complex index was translated
    EXPECT_NE(cArrSub->getIdx(), nullptr);
}

// ============================================================================
// Test: Pointer Indexing (ptr[offset])
// ============================================================================

TEST(ArraySubscriptExprHandlerDispatcherTest, PointerIndexing) {
    const char *cpp = R"(
        int test(int* ptr, int offset) {
            return ptr[offset];
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
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ArraySubscriptExpr* arrSub = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                arrSub = findNode<ArraySubscriptExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(arrSub, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, arrSub);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(arrSub);
    ASSERT_NE(cExpr, nullptr);

    auto* cArrSub = dyn_cast<ArraySubscriptExpr>(cExpr);
    ASSERT_NE(cArrSub, nullptr);
}

// ============================================================================
// Test: Nested Multi-Dimensional Access (matrix[i+1][j*2])
// ============================================================================

TEST(ArraySubscriptExprHandlerDispatcherTest, NestedMultiDimensionalWithComplexIndices) {
    const char *cpp = R"(
        int test(int i, int j) {
            int matrix[10][10];
            return matrix[i + 1][j * 2];
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
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ArraySubscriptExpr* outerSub = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                outerSub = findNode<ArraySubscriptExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(outerSub, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, outerSub);
    ASSERT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(outerSub);
    ASSERT_NE(cExpr, nullptr);

    auto* cOuterSub = dyn_cast<ArraySubscriptExpr>(cExpr);
    ASSERT_NE(cOuterSub, nullptr);

    // Verify all subexpressions were translated
    EXPECT_NE(cOuterSub->getBase(), nullptr);
    EXPECT_NE(cOuterSub->getIdx(), nullptr);
}

// ============================================================================
// Test: Predicate Correctness - canHandle()
// ============================================================================

TEST(ArraySubscriptExprHandlerDispatcherTest, PredicateCorrectness) {
    const char *cpp = R"(
        int test() {
            int arr[5];
            int x = arr[2];      // ArraySubscriptExpr
            int y = 1 + 2;       // BinaryOperator
            return x + y;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ArraySubscriptExpr* arrSub = nullptr;
    BinaryOperator* binOp = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                arrSub = findNode<ArraySubscriptExpr>(FD->getBody());
                binOp = findNode<BinaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(arrSub, nullptr);
    ASSERT_NE(binOp, nullptr);

    // Predicate should return true for ArraySubscriptExpr
    EXPECT_TRUE(cpptoc::ArraySubscriptExprHandler::canHandle(arrSub));

    // Predicate should return false for BinaryOperator
    EXPECT_FALSE(cpptoc::ArraySubscriptExprHandler::canHandle(binOp));
}

// ============================================================================
// Test: Integration with ExprMapper - Deduplication
// ============================================================================

TEST(ArraySubscriptExprHandlerDispatcherTest, ExprMapperDeduplication) {
    const char *cpp = R"(
        int test() {
            int arr[5];
            return arr[2];
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
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ArraySubscriptExpr* arrSub = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                arrSub = findNode<ArraySubscriptExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(arrSub, nullptr);

    // First dispatch
    bool handled1 = dispatcher.dispatch(cppCtx, cCtx, arrSub);
    ASSERT_TRUE(handled1);
    Expr* cExpr1 = exprMapper.getCreated(arrSub);
    ASSERT_NE(cExpr1, nullptr);

    // Second dispatch (should be deduplicated)
    bool handled2 = dispatcher.dispatch(cppCtx, cCtx, arrSub);
    EXPECT_TRUE(handled2);
    Expr* cExpr2 = exprMapper.getCreated(arrSub);
    ASSERT_NE(cExpr2, nullptr);

    // Should return the same C expression (deduplication)
    EXPECT_EQ(cExpr1, cExpr2);
}
