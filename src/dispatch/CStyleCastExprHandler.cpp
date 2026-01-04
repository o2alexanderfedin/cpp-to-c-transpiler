/**
 * @file CStyleCastExprHandler.cpp
 * @brief Implementation of CStyleCastExprHandler
 */

#include "dispatch/CStyleCastExprHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CStyleCastExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CStyleCastExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CStyleCastExprHandler::handleCStyleCastExpr)
    );
}

bool CStyleCastExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::CStyleCastExprClass;
}

void CStyleCastExprHandler::handleCStyleCastExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be CStyleCastExpr");

    const auto* cppCast = llvm::cast<clang::CStyleCastExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CStyleCastExprHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CStyleCastExprHandler] Processing C-style cast\n";

    // Dispatch subexpression
    const clang::Expr* cppSubExpr = cppCast->getSubExpr();
    bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppSubExpr));

    if (!handled) {
        llvm::errs() << "[CStyleCastExprHandler] ERROR: Subexpression not handled\n";
        llvm::errs() << "  Subexpression type: " << cppSubExpr->getStmtClassName() << "\n";
        assert(false && "Subexpression must be handled");
    }

    clang::Expr* cSubExpr = exprMapper.getCreated(cppSubExpr);
    assert(cSubExpr && "Subexpression must be in ExprMapper");

    // Get target type and cast kind
    clang::QualType targetType = cppCast->getType();
    clang::CastKind castKind = cppCast->getCastKind();

    // Create C-style cast expression
    clang::CStyleCastExpr* cCast = clang::CStyleCastExpr::Create(
        cASTContext,
        targetType,
        cppCast->getValueKind(),
        castKind,
        cSubExpr,
        nullptr,  // path (not used for most casts)
        clang::FPOptionsOverride(),
        cASTContext.getTrivialTypeSourceInfo(targetType),
        clang::SourceLocation(),  // LParenLoc
        clang::SourceLocation()   // RParenLoc
    );

    llvm::outs() << "[CStyleCastExprHandler] Created C-style cast\n";

    // Store mapping
    exprMapper.setCreated(E, cCast);
}

} // namespace cpptoc
