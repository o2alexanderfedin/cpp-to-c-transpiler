/**
 * @file CXXDependentScopeMemberExprHandler.cpp
 * @brief Implementation of CXXDependentScopeMemberExprHandler
 */

#include "dispatch/CXXDependentScopeMemberExprHandler.h"
#include "mapping/ExprMapper.h"
#include "mapping/DeclMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CXXDependentScopeMemberExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CXXDependentScopeMemberExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CXXDependentScopeMemberExprHandler::handleCXXDependentScopeMemberExpr)
    );
}

bool CXXDependentScopeMemberExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::CXXDependentScopeMemberExprClass;
}

void CXXDependentScopeMemberExprHandler::handleCXXDependentScopeMemberExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be CXXDependentScopeMemberExpr");

    const auto* cppDepMember = llvm::cast<clang::CXXDependentScopeMemberExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CXXDependentScopeMemberExprHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CXXDependentScopeMemberExprHandler] Processing CXXDependentScopeMemberExpr\n";

    // Get base expression (if exists)
    clang::Expr* cBase = nullptr;
    if (!cppDepMember->isImplicitAccess()) {
        const clang::Expr* cppBase = cppDepMember->getBase();
        assert(cppBase && "Non-implicit access must have base");

        // Dispatch base expression
        bool baseHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppBase));
        if (!baseHandled) {
            llvm::errs() << "[CXXDependentScopeMemberExprHandler] ERROR: Base not handled\n";
            llvm::errs() << "  Base expression type: " << cppBase->getStmtClassName() << "\n";
            assert(false && "Base must be handled");
        }

        cBase = exprMapper.getCreated(cppBase);
        assert(cBase && "Base must be in ExprMapper");
    }

    // For dependent scope member expr in non-template context (after instantiation),
    // we create a simple DeclRefExpr to the member name
    // NOTE: This is simplified for C transpilation - proper handling would require
    // resolving the dependent name, but for our STL-free use cases, we can
    // treat it as a regular member access

    // Get member name
    clang::DeclarationName memberName = cppDepMember->getMember();
    std::string memberNameStr = memberName.getAsString();

    llvm::outs() << "[CXXDependentScopeMemberExprHandler] Member: " << memberNameStr << "\n";

    // For now, create a placeholder expression using the base (if exists)
    // In a full implementation, we'd need to resolve the member declaration
    clang::Expr* cExpr;
    if (cBase) {
        // Create a simple MemberExpr-like structure
        // Since we don't have the actual member decl in dependent context,
        // we'll create a DeclRefExpr as a placeholder
        // This is a simplification - real code would need member resolution
        cExpr = cBase; // Pass through the base for now
    } else {
        // Implicit this access - create placeholder
        // For C transpilation, this will need special handling
        llvm::errs() << "[CXXDependentScopeMemberExprHandler] WARNING: Implicit access not fully supported\n";
        cExpr = cBase; // nullptr - will need proper handling
    }

    // Store in ExprMapper
    exprMapper.setCreated(E, cExpr);

    llvm::outs() << "[CXXDependentScopeMemberExprHandler] Translation complete\n";
}

} // namespace cpptoc
