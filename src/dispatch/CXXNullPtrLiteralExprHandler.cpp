/**
 * @file CXXNullPtrLiteralExprHandler.cpp
 * @brief Implementation of CXXNullPtrLiteralExprHandler
 */

#include "dispatch/CXXNullPtrLiteralExprHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CXXNullPtrLiteralExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CXXNullPtrLiteralExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CXXNullPtrLiteralExprHandler::handleCXXNullPtrLiteralExpr)
    );
}

bool CXXNullPtrLiteralExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::CXXNullPtrLiteralExprClass;
}

void CXXNullPtrLiteralExprHandler::handleCXXNullPtrLiteralExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be CXXNullPtrLiteralExpr");

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CXXNullPtrLiteralExprHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CXXNullPtrLiteralExprHandler] Processing nullptr literal\n";

    // For nullptr, create integer literal 0 (C uses 0 or NULL)
    llvm::APInt zeroValue(32, 0);
    clang::IntegerLiteral* cNullPtr = clang::IntegerLiteral::Create(
        cASTContext,
        zeroValue,
        cASTContext.IntTy,
        clang::SourceLocation()
    );

    llvm::outs() << "[CXXNullPtrLiteralExprHandler] Created integer literal 0 for nullptr\n";

    // Store mapping
    exprMapper.setCreated(E, cNullPtr);
}

} // namespace cpptoc
