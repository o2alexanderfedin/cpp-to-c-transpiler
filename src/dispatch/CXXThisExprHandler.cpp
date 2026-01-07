/**
 * @file CXXThisExprHandler.cpp
 * @brief Implementation of CXXThisExprHandler
 */

#include "dispatch/CXXThisExprHandler.h"
#include "SourceLocationMapper.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CXXThisExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CXXThisExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CXXThisExprHandler::handleCXXThisExpr)
    );
}

bool CXXThisExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::CXXThisExprClass;
}

void CXXThisExprHandler::handleCXXThisExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be CXXThisExpr");

    const auto* cppThis = llvm::cast<clang::CXXThisExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CXXThisExprHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CXXThisExprHandler] Processing CXXThisExpr (this pointer)\n";

    // Get the type of 'this' pointer
    clang::QualType thisType = cppThis->getType();

    // For C translation, 'this' becomes an explicit parameter named "this"
    // The actual parameter decl should be created by the method handler
    // For now, we create a DeclRefExpr with identifier "this"

    // Get source location from SourceLocationMapper
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, E);
    }
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Create an IdentifierInfo for "this"
    clang::IdentifierInfo* thisIdent = &cASTContext.Idents.get("this");

    // Create a ParmVarDecl for the 'this' parameter
    // Note: This should ideally be looked up from the function being processed,
    // but for simplicity we create a placeholder here
    clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
        cASTContext,
        nullptr, // DeclContext - will be set by method handler
        targetLoc,
        targetLoc,
        thisIdent,
        thisType,
        cASTContext.getTrivialTypeSourceInfo(thisType),
        clang::SC_None,
        nullptr // default argument
    );

    // Create DeclRefExpr referring to this parameter
    clang::DeclRefExpr* cThisRef = clang::DeclRefExpr::Create(
        cASTContext,
        clang::NestedNameSpecifierLoc(),
        targetLoc,
        thisParam,
        false, // refersToEnclosingVariableOrCapture
        targetLoc,
        thisType,
        clang::VK_LValue
    );

    llvm::outs() << "[CXXThisExprHandler] Created DeclRefExpr for 'this' parameter\n";

    // Store mapping
    exprMapper.setCreated(E, cThisRef);
}

} // namespace cpptoc
