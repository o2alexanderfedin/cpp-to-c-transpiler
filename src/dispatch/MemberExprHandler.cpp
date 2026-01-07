/**
 * @file MemberExprHandler.cpp
 * @brief Implementation of MemberExprHandler with recursive dispatch
 */

#include "dispatch/MemberExprHandler.h"
#include "mapping/ExprMapper.h"
#include "mapping/DeclMapper.h"
#include "SourceLocationMapper.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void MemberExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&MemberExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&MemberExprHandler::handleMemberExpr)
    );
}

bool MemberExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::MemberExprClass;
}

void MemberExprHandler::handleMemberExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(E->getStmtClass() == clang::Stmt::MemberExprClass && "Must be MemberExpr");

    const auto* cppMemberExpr = llvm::cast<clang::MemberExpr>(E);

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[MemberExprHandler] MemberExpr already translated, skipping\n";
        return;
    }

    // Extract base expression and member declaration
    const clang::Expr* cppBase = cppMemberExpr->getBase();
    clang::ValueDecl* cppMemberDecl = cppMemberExpr->getMemberDecl();
    bool isArrow = cppMemberExpr->isArrow();

    llvm::outs() << "[MemberExprHandler] Processing MemberExpr: "
                 << (isArrow ? "->" : ".") << cppMemberDecl->getNameAsString() << "\n";

    // CRITICAL: Recursive dispatch pattern
    // Dispatch base expression via dispatcher (may trigger DeclRefExprHandler, MemberExprHandler, etc.)
    llvm::outs() << "[MemberExprHandler] Dispatching base expression\n";
    bool baseHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppBase));

    if (!baseHandled) {
        llvm::errs() << "[MemberExprHandler] ERROR: Base expression not handled by any handler\n";
        llvm::errs() << "  Base expression type: " << cppBase->getStmtClassName() << "\n";
        assert(false && "Base expression must be handled");
    }

    // Retrieve translated base from ExprMapper
    clang::Expr* cBase = exprMapper.getCreated(cppBase);
    assert(cBase && "Base must be in ExprMapper after dispatch");

    llvm::outs() << "[MemberExprHandler] Base expression translated successfully\n";

    // Look up translated member declaration in DeclMapper
    // If not found, we'll use the original (C++ field becomes C field with same name)
    clang::ValueDecl* cMemberDecl = cppMemberDecl;
    if (declMapper.hasCreated(cppMemberDecl)) {
        cMemberDecl = llvm::cast<clang::ValueDecl>(declMapper.getCreated(cppMemberDecl));
        llvm::outs() << "[MemberExprHandler] Using mapped C member declaration\n";
    } else {
        llvm::outs() << "[MemberExprHandler] WARNING: Member not in DeclMapper, using original declaration\n";
    }

    // Get source location from target context
    // Expression handlers rely on getCurrentTargetPath() being set
    std::string targetPath = disp.getCurrentTargetPath();
    assert(!targetPath.empty() && "Target path must be set before expression handling");
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Create C MemberExpr with translated base
    // CRITICAL: Preserve arrow vs dot flag for correct C semantics
    clang::MemberExpr* cMemberExpr = clang::MemberExpr::Create(
        cASTContext,
        cBase,
        isArrow,  // Preserve arrow vs dot distinction
        targetLoc,  // OperatorLoc
        clang::NestedNameSpecifierLoc(),  // QualifierLoc (no qualifiers in C)
        targetLoc,  // TemplateKWLoc (no templates in C)
        cMemberDecl,
        clang::DeclAccessPair::make(cMemberDecl, clang::AS_public),
        clang::DeclarationNameInfo(cMemberDecl->getDeclName(), targetLoc),
        nullptr,  // TemplateArgs (no templates in C)
        cppMemberExpr->getType(),  // May need type translation in future
        cppMemberExpr->getValueKind(),
        cppMemberExpr->getObjectKind(),
        clang::NOUR_None  // NonOdrUseReason
    );

    llvm::outs() << "[MemberExprHandler] Created C MemberExpr: "
                 << (isArrow ? "->" : ".") << cMemberDecl->getNameAsString() << "\n";

    // Store mapping in ExprMapper
    exprMapper.setCreated(E, cMemberExpr);
}

} // namespace cpptoc
