/**
 * @file CXXFunctionalCastExprHandler.cpp
 * @brief Implementation of CXXFunctionalCastExprHandler
 */

#include "dispatch/CXXFunctionalCastExprHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CXXFunctionalCastExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CXXFunctionalCastExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CXXFunctionalCastExprHandler::handleCXXFunctionalCastExpr)
    );
}

bool CXXFunctionalCastExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::CXXFunctionalCastExprClass;
}

void CXXFunctionalCastExprHandler::handleCXXFunctionalCastExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be CXXFunctionalCastExpr");

    const auto* cppCast = llvm::cast<clang::CXXFunctionalCastExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CXXFunctionalCastExprHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CXXFunctionalCastExprHandler] Processing functional-style cast\n";

    // Dispatch subexpression
    const clang::Expr* cppSubExpr = cppCast->getSubExpr();
    bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppSubExpr));

    if (!handled) {
        llvm::errs() << "[CXXFunctionalCastExprHandler] ERROR: Subexpression not handled\n";
        llvm::errs() << "  Subexpression type: " << cppSubExpr->getStmtClassName() << "\n";
        assert(false && "Subexpression must be handled");
    }

    clang::Expr* cSubExpr = exprMapper.getCreated(cppSubExpr);
    assert(cSubExpr && "Subexpression must be in ExprMapper");

    // Get target type and cast kind
    clang::QualType targetType = cppCast->getType();
    clang::CastKind castKind = cppCast->getCastKind();

    // Create C-style cast expression
    // Note: CXXFunctionalCastExpr (e.g., int(x)) is converted to CStyleCastExpr (e.g., (int)x) in C
    clang::CStyleCastExpr* cCast = clang::CStyleCastExpr::Create(
        cASTContext,
        targetType,
        cppCast->getValueKind(),
        castKind,
        cSubExpr,
        nullptr,
        clang::FPOptionsOverride(),
        cASTContext.getTrivialTypeSourceInfo(targetType),
        clang::SourceLocation(),
        clang::SourceLocation()
    );

    llvm::outs() << "[CXXFunctionalCastExprHandler] Created C-style cast from functional cast\n";

    // Store mapping
    exprMapper.setCreated(E, cCast);
}

} // namespace cpptoc
