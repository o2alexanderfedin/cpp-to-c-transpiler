/**
 * @file ThrowExprHandler.cpp
 * @brief Implementation of ThrowExprHandler dispatcher pattern
 */

#include "dispatch/ThrowExprHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "ThrowTranslator.h"
#include "mapping/StmtMapper.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ThrowExprHandler::registerWith(::CppToCVisitorDispatcher& dispatcher) {
    // Cast to ExprPredicate and ExprVisitor to match dispatcher interface
    dispatcher.addHandler(
        static_cast<::CppToCVisitorDispatcher::ExprPredicate>(&ThrowExprHandler::canHandle),
        static_cast<::CppToCVisitorDispatcher::ExprVisitor>(&ThrowExprHandler::handleThrowExpr)
    );
}

bool ThrowExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::CXXThrowExprClass;
}

void ThrowExprHandler::handleThrowExpr(
    const ::CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Expression must be CXXThrowExpr");

    const auto* throwExpr = llvm::cast<clang::CXXThrowExpr>(E);

    llvm::outs() << "[ThrowExprHandler] Processing CXXThrowExpr\n";

    // Check if already processed
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
    if (stmtMapper.hasCreated(throwExpr)) {
        llvm::outs() << "[ThrowExprHandler] CXXThrowExpr already translated, skipping\n";
        return;
    }

    // Phase 5: Delegate to ThrowTranslator service class (AST-based - COMPLETE)
    clang::ThrowTranslator translator;
    clang::CompoundStmt* throwStmt = translator.generateThrowCode(
        throwExpr, disp, cppASTContext, cASTContext
    );

    if (!throwStmt) {
        llvm::errs() << "[ThrowExprHandler] ERROR: ThrowTranslator returned null\n";
        return;
    }

    llvm::outs() << "[ThrowExprHandler] Generated throw AST with "
                 << throwStmt->size() << " statements\n";

    // Phase 5: Store C CompoundStmt* in StmtMapper (COMPLETE)
    // Note: CXXThrowExpr is an expression in C++, but we translate it to a CompoundStmt in C
    // Store in StmtMapper so parent statement handlers can retrieve and incorporate it
    stmtMapper.setCreated(throwExpr, throwStmt);

    llvm::outs() << "[ThrowExprHandler] CXXThrowExpr translation complete (AST-based)\n";
}

} // namespace cpptoc
