/**
 * @file CXXMemberCallExprHandler.cpp
 * @brief Implementation of CXXMemberCallExprHandler
 */

#include "dispatch/CXXMemberCallExprHandler.h"
#include "mapping/ExprMapper.h"
#include "mapping/DeclMapper.h"
#include "SourceLocationMapper.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CXXMemberCallExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CXXMemberCallExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CXXMemberCallExprHandler::handleCXXMemberCallExpr)
    );
}

bool CXXMemberCallExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::CXXMemberCallExprClass;
}

void CXXMemberCallExprHandler::handleCXXMemberCallExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be CXXMemberCallExpr");

    const auto* cppMemberCall = llvm::cast<clang::CXXMemberCallExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CXXMemberCallExprHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CXXMemberCallExprHandler] Processing CXXMemberCallExpr\n";

    // Get the callee (member function)
    const clang::FunctionDecl* cppCalleeDecl = cppMemberCall->getDirectCallee();
    if (!cppCalleeDecl) {
        llvm::errs() << "[CXXMemberCallExprHandler] ERROR: Cannot get callee function\n";
        assert(false && "Must have callee function");
    }

    llvm::outs() << "[CXXMemberCallExprHandler] Member function: "
                 << cppCalleeDecl->getNameAsString() << "\n";

    // Look up the C function in DeclMapper
    clang::Decl* cCalleeDecl = declMapper.getCreated(cppCalleeDecl);
    if (!cCalleeDecl) {
        llvm::errs() << "[CXXMemberCallExprHandler] WARNING: Member function not yet translated\n";
        llvm::errs() << "  Function: " << cppCalleeDecl->getNameAsString() << "\n";
        // Create a placeholder DeclRefExpr with the original function for now
        // The actual C function should be created by InstanceMethodHandler
        cCalleeDecl = const_cast<clang::FunctionDecl*>(cppCalleeDecl);
    }

    // Get valid SourceLocation for C AST node
    // For expressions, we rely on getCurrentTargetPath() since expressions
    // don't carry file location information like Decls do
    std::string targetPath = disp.getCurrentTargetPath();
    assert(!targetPath.empty() && "Target path must be set for expression handling");
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Create DeclRefExpr for the C function
    clang::DeclRefExpr* cCalleeDRE = clang::DeclRefExpr::Create(
        cASTContext,
        clang::NestedNameSpecifierLoc(),
        targetLoc,
        llvm::cast<clang::FunctionDecl>(cCalleeDecl),
        false, // RefersToEnclosingVariableOrCapture
        targetLoc,
        llvm::cast<clang::FunctionDecl>(cCalleeDecl)->getType(),
        clang::VK_LValue
    );

    // Dispatch on the implicit object argument (this)
    const clang::Expr* cppImplicitObj = cppMemberCall->getImplicitObjectArgument();
    llvm::SmallVector<clang::Expr*, 8> cArgs;

    if (cppImplicitObj) {
        llvm::outs() << "[CXXMemberCallExprHandler] Dispatching implicit object argument\n";
        bool objHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppImplicitObj));

        if (!objHandled) {
            llvm::errs() << "[CXXMemberCallExprHandler] ERROR: Implicit object not handled\n";
            llvm::errs() << "  Object expression type: " << cppImplicitObj->getStmtClassName() << "\n";
            assert(false && "Implicit object must be handled");
        }

        clang::Expr* cObj = exprMapper.getCreated(cppImplicitObj);
        assert(cObj && "Implicit object must be in ExprMapper");

        // Wrap implicit object in UnaryOperator (address-of &) to pass by pointer
        // C methods expect: void Class__method(struct Class* this, ...)
        // So we need to pass &obj instead of obj
        clang::QualType cObjPtrType = cASTContext.getPointerType(cObj->getType());
        clang::UnaryOperator* cObjAddr = clang::UnaryOperator::Create(
            cASTContext,
            cObj,
            clang::UO_AddrOf,
            cObjPtrType,
            clang::VK_PRValue,
            clang::OK_Ordinary,
            targetLoc,
            false, // CanOverflow
            clang::FPOptionsOverride()
        );

        llvm::outs() << "[CXXMemberCallExprHandler] Wrapped implicit object in address-of operator\n";

        // Add '&this' as first argument
        cArgs.push_back(cObjAddr);
    }

    // Dispatch all explicit arguments
    llvm::outs() << "[CXXMemberCallExprHandler] Dispatching " << cppMemberCall->getNumArgs() << " arguments\n";
    for (unsigned i = 0; i < cppMemberCall->getNumArgs(); ++i) {
        const clang::Expr* cppArg = cppMemberCall->getArg(i);

        bool argHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppArg));

        if (!argHandled) {
            llvm::errs() << "[CXXMemberCallExprHandler] ERROR: Argument " << i << " not handled\n";
            llvm::errs() << "  Argument type: " << cppArg->getStmtClassName() << "\n";
            assert(false && "All arguments must be handled");
        }

        clang::Expr* cArg = exprMapper.getCreated(cppArg);
        assert(cArg && "Argument must be in ExprMapper");

        // Check if the corresponding C++ parameter is a reference type
        // If so, wrap the argument in address-of operator
        if (cppCalleeDecl && i < cppCalleeDecl->getNumParams()) {
            clang::QualType cppParamType = cppCalleeDecl->getParamDecl(i)->getType();

            if (cppParamType->isReferenceType()) {
                llvm::outs() << "[CXXMemberCallExprHandler] Parameter " << i
                             << " is reference type, wrapping in address-of\n";

                clang::QualType cArgPtrType = cASTContext.getPointerType(cArg->getType());
                clang::UnaryOperator* cArgAddr = clang::UnaryOperator::Create(
                    cASTContext,
                    cArg,
                    clang::UO_AddrOf,
                    cArgPtrType,
                    clang::VK_PRValue,
                    clang::OK_Ordinary,
                    targetLoc,
                    false, // CanOverflow
                    clang::FPOptionsOverride()
                );
                cArgs.push_back(cArgAddr);
            } else {
                // Not a reference, pass by value
                cArgs.push_back(cArg);
            }
        } else {
            // No parameter info available, pass as-is
            cArgs.push_back(cArg);
        }
    }

    // Create C CallExpr
    clang::CallExpr* cCallExpr = clang::CallExpr::Create(
        cASTContext,
        cCalleeDRE,
        cArgs,
        cppMemberCall->getType(),
        cppMemberCall->getValueKind(),
        targetLoc,
        clang::FPOptionsOverride()
    );

    llvm::outs() << "[CXXMemberCallExprHandler] Created C CallExpr for member function call\n";

    // Store mapping
    exprMapper.setCreated(E, cCallExpr);
}

} // namespace cpptoc
