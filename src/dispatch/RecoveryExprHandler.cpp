/**
 * @file RecoveryExprHandler.cpp
 * @brief Implementation of RecoveryExprHandler
 */

#include "dispatch/RecoveryExprHandler.h"
#include "mapping/ExprMapper.h"
#include "SourceLocationMapper.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void RecoveryExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&RecoveryExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&RecoveryExprHandler::handleRecoveryExpr)
    );
}

bool RecoveryExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::RecoveryExprClass;
}

void RecoveryExprHandler::handleRecoveryExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be RecoveryExpr");

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[RecoveryExprHandler] Already translated, skipping\n";
        return;
    }

    // Get target location for this expression
    std::string targetPath = disp.getCurrentTargetPath();
    assert(!targetPath.empty() && "Target path must be set before expression handling");
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    llvm::outs() << "[RecoveryExprHandler] Processing RecoveryExpr (error recovery node)\n";
    llvm::outs() << "[RecoveryExprHandler] WARNING: RecoveryExpr indicates parsing errors in source\n";

    // RecoveryExpr represents an error in the source code.
    // For C transpilation, we create a placeholder integer literal (0)
    // to allow compilation to continue.
    llvm::APInt zeroValue(32, 0);
    clang::IntegerLiteral* cPlaceholder = clang::IntegerLiteral::Create(
        cASTContext,
        zeroValue,
        cASTContext.IntTy,
        targetLoc
    );

    llvm::outs() << "[RecoveryExprHandler] Created placeholder integer literal (0)\n";

    // Store mapping
    exprMapper.setCreated(E, cPlaceholder);
}

} // namespace cpptoc
