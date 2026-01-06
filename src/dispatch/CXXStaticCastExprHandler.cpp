/**
 * @file CXXStaticCastExprHandler.cpp
 * @brief Implementation of CXXStaticCastExprHandler
 */

#include "dispatch/CXXStaticCastExprHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CXXStaticCastExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CXXStaticCastExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CXXStaticCastExprHandler::handleCXXStaticCastExpr)
    );
}

bool CXXStaticCastExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::CXXStaticCastExprClass;
}

void CXXStaticCastExprHandler::handleCXXStaticCastExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be CXXStaticCastExpr");

    const auto* cppCast = llvm::cast<clang::CXXStaticCastExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CXXStaticCastExprHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CXXStaticCastExprHandler] Processing static_cast\n";

    // Dispatch subexpression
    const clang::Expr* cppSubExpr = cppCast->getSubExpr();
    bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppSubExpr));

    if (!handled) {
        llvm::errs() << "[CXXStaticCastExprHandler] ERROR: Subexpression not handled\n";
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

    llvm::outs() << "[CXXStaticCastExprHandler] Created C-style cast\n";

    // Store mapping
    exprMapper.setCreated(E, cCast);
}

} // namespace cpptoc
