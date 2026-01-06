/**
 * @file UnresolvedLookupExprHandler.cpp
 * @brief Implementation of UnresolvedLookupExprHandler
 */

#include "dispatch/UnresolvedLookupExprHandler.h"
#include "mapping/ExprMapper.h"
#include "mapping/DeclMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void UnresolvedLookupExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&UnresolvedLookupExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&UnresolvedLookupExprHandler::handleUnresolvedLookupExpr)
    );
}

bool UnresolvedLookupExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::UnresolvedLookupExprClass;
}

void UnresolvedLookupExprHandler::handleUnresolvedLookupExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be UnresolvedLookupExpr");

    const auto* cppUnresolved = llvm::cast<clang::UnresolvedLookupExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[UnresolvedLookupExprHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[UnresolvedLookupExprHandler] Processing UnresolvedLookupExpr\n";

    // Get the name being looked up
    clang::DeclarationName declName = cppUnresolved->getName();
    std::string nameStr = declName.getAsString();

    llvm::outs() << "[UnresolvedLookupExprHandler] Looking up name: " << nameStr << "\n";

    // Try to find a resolved declaration in the decls
    clang::NamedDecl* resolvedDecl = nullptr;
    if (cppUnresolved->getNumDecls() > 0) {
        // Use the first declaration found
        resolvedDecl = *cppUnresolved->decls_begin();
        llvm::outs() << "[UnresolvedLookupExprHandler] Found " << cppUnresolved->getNumDecls() << " candidates\n";
    }

    // Try to find C declaration in DeclMapper
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    clang::Decl* cDecl = nullptr;
    if (resolvedDecl) {
        cDecl = declMapper.getCreated(resolvedDecl);
    }

    clang::ValueDecl* cValueDecl = nullptr;
    if (cDecl) {
        cValueDecl = llvm::dyn_cast<clang::ValueDecl>(cDecl);
        llvm::outs() << "[UnresolvedLookupExprHandler] Found C declaration in DeclMapper\n";
    }

    // If no C decl found, use the C++ decl as fallback
    if (!cValueDecl && resolvedDecl) {
        cValueDecl = llvm::dyn_cast<clang::ValueDecl>(resolvedDecl);
        llvm::outs() << "[UnresolvedLookupExprHandler] Using C++ declaration as fallback\n";
    }

    if (!cValueDecl) {
        llvm::errs() << "[UnresolvedLookupExprHandler] WARNING: Could not resolve " << nameStr << "\n";
        llvm::errs() << "[UnresolvedLookupExprHandler] Creating placeholder\n";

        // Create placeholder integer literal (0)
        llvm::APInt zeroValue(32, 0);
        clang::IntegerLiteral* cPlaceholder = clang::IntegerLiteral::Create(
            cASTContext,
            zeroValue,
            cASTContext.IntTy,
            clang::SourceLocation()
        );
        exprMapper.setCreated(E, cPlaceholder);
        return;
    }

    // Create DeclRefExpr pointing to the resolved declaration
    clang::DeclRefExpr* cDeclRef = clang::DeclRefExpr::Create(
        cASTContext,
        clang::NestedNameSpecifierLoc(),
        clang::SourceLocation(),
        cValueDecl,
        false,
        clang::SourceLocation(),
        cppUnresolved->getType(),
        clang::VK_LValue
    );

    llvm::outs() << "[UnresolvedLookupExprHandler] Created DeclRefExpr for: " << nameStr << "\n";

    // Store mapping
    exprMapper.setCreated(E, cDeclRef);
}

} // namespace cpptoc
