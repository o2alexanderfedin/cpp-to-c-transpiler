/**
 * @file CXXDeleteExprHandler.cpp
 * @brief Implementation of CXXDeleteExprHandler
 */

#include "dispatch/CXXDeleteExprHandler.h"
#include "mapping/StmtMapper.h"
#include "mapping/ExprMapper.h"
#include "SourceLocationMapper.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CXXDeleteExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&CXXDeleteExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&CXXDeleteExprHandler::handleCXXDeleteExpr)
    );
}

bool CXXDeleteExprHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");
    return S->getStmtClass() == clang::Stmt::CXXDeleteExprClass;
}

void CXXDeleteExprHandler::handleCXXDeleteExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(canHandle(S) && "Must be CXXDeleteExpr");

    const auto* cppDelete = llvm::cast<clang::CXXDeleteExpr>(S);
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(llvm::cast<clang::Expr>(S))) {
        llvm::outs() << "[CXXDeleteExprHandler] Already translated, skipping\n";
        return;
    }

    // Get target location for this expression
    std::string targetPath = disp.getCurrentTargetPath();
    assert(!targetPath.empty() && "Target path must be set before expression handling");
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    llvm::outs() << "[CXXDeleteExprHandler] Processing CXXDeleteExpr (translating to free)\n";

    // Get the argument (pointer being deleted)
    const clang::Expr* cppArg = cppDelete->getArgument();

    // Dispatch argument
    bool argHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppArg));

    if (!argHandled) {
        llvm::errs() << "[CXXDeleteExprHandler] ERROR: Argument not handled\n";
        llvm::errs() << "  Argument type: " << cppArg->getStmtClassName() << "\n";
        assert(false && "Argument must be handled");
    }

    clang::Expr* cArg = exprMapper.getCreated(cppArg);
    assert(cArg && "Argument must be in ExprMapper");

    // Create call to free(ptr)
    // Full implementation would require:
    // 1. Declaration of free function
    // 2. Proper CallExpr creation

    // For now, create a placeholder null statement (since delete is a statement in practice)
    // Create placeholder integer literal
    llvm::APInt zeroValue(32, 0);
    clang::IntegerLiteral* cPlaceholder = clang::IntegerLiteral::Create(
        cASTContext,
        zeroValue,
        cASTContext.IntTy,
        targetLoc
    );

    llvm::outs() << "[CXXDeleteExprHandler] Created placeholder for delete expression (full free translation not yet implemented)\n";

    // Store in both mappers
    exprMapper.setCreated(llvm::cast<clang::Expr>(S), cPlaceholder);
    stmtMapper.setCreated(S, cPlaceholder);
}

} // namespace cpptoc
