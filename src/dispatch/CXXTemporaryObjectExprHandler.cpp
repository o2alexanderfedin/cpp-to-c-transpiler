/**
 * @file CXXTemporaryObjectExprHandler.cpp
 * @brief Implementation of CXXTemporaryObjectExprHandler
 */

#include "dispatch/CXXTemporaryObjectExprHandler.h"
#include "mapping/ExprMapper.h"
#include "mapping/DeclMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CXXTemporaryObjectExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CXXTemporaryObjectExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CXXTemporaryObjectExprHandler::handleCXXTemporaryObjectExpr)
    );
}

bool CXXTemporaryObjectExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::CXXTemporaryObjectExprClass;
}

void CXXTemporaryObjectExprHandler::handleCXXTemporaryObjectExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be CXXTemporaryObjectExpr");

    const auto* cppTempObj = llvm::cast<clang::CXXTemporaryObjectExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CXXTemporaryObjectExprHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CXXTemporaryObjectExprHandler] Processing CXXTemporaryObjectExpr\n";

    // Get the constructor that would be called
    // CXXTemporaryObjectExpr represents expressions like Vector3D(1, 2, 3)
    // For C, we translate this to a compound literal: (struct Vector3D){1, 2, 3}

    // Get the type being constructed
    clang::QualType cppType = cppTempObj->getType();
    const clang::CXXRecordDecl* cppClass = cppType->getAsCXXRecordDecl();

    clang::QualType cType;
    if (cppClass) {
        llvm::outs() << "[CXXTemporaryObjectExprHandler] Looking up C struct for C++ class: "
                     << cppClass->getNameAsString() << "\n";

        cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
        clang::Decl* cDecl = declMapper.getCreated(cppClass);

        if (cDecl) {
            if (clang::RecordDecl* cStruct = llvm::dyn_cast<clang::RecordDecl>(cDecl)) {
                cType = cASTContext.getRecordType(cStruct);
                llvm::outs() << "[CXXTemporaryObjectExprHandler] Found C struct type\n";
            } else {
                llvm::errs() << "[CXXTemporaryObjectExprHandler] WARNING: DeclMapper entry is not RecordDecl\n";
                cType = cppType; // Fallback
            }
        } else {
            llvm::errs() << "[CXXTemporaryObjectExprHandler] WARNING: C struct not found in DeclMapper for "
                         << cppClass->getNameAsString() << ", using C++ type as fallback\n";
            cType = cppType; // Fallback
        }
    } else {
        // Not a class type, use as-is
        cType = cppType;
    }

    // Process constructor arguments
    llvm::SmallVector<clang::Expr*, 8> cArgs;
    for (unsigned i = 0; i < cppTempObj->getNumArgs(); ++i) {
        const clang::Expr* cppArg = cppTempObj->getArg(i);

        // Dispatch each argument
        bool argHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppArg));

        if (!argHandled) {
            llvm::errs() << "[CXXTemporaryObjectExprHandler] ERROR: Argument " << i << " not handled\n";
            llvm::errs() << "  Argument expression type: " << cppArg->getStmtClassName() << "\n";
            assert(false && "Constructor argument must be handled");
        }

        clang::Expr* cArg = exprMapper.getCreated(cppArg);
        assert(cArg && "Argument must be in ExprMapper after dispatch");
        cArgs.push_back(cArg);
    }

    // Create InitListExpr for compound literal
    clang::InitListExpr* cInitList = new (cASTContext) clang::InitListExpr(
        cASTContext,
        clang::SourceLocation(),
        cArgs,
        clang::SourceLocation()
    );

    cInitList->setType(cType);

    // Create CompoundLiteralExpr: (struct Type){...}
    clang::CompoundLiteralExpr* cCompoundLit = new (cASTContext) clang::CompoundLiteralExpr(
        clang::SourceLocation(),
        cASTContext.getTrivialTypeSourceInfo(cType),
        cType,
        clang::VK_PRValue,
        cInitList,
        false  // isFileScope
    );

    llvm::outs() << "[CXXTemporaryObjectExprHandler] Created CompoundLiteralExpr for temporary object\n";

    // Store mapping
    exprMapper.setCreated(E, cCompoundLit);
}

} // namespace cpptoc
