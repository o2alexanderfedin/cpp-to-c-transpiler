/**
 * @file CXXConstructExprHandler.cpp
 * @brief Implementation of CXXConstructExprHandler with recursive dispatch
 */

#include "dispatch/CXXConstructExprHandler.h"
#include "mapping/ExprMapper.h"
#include "mapping/DeclMapper.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <vector>

namespace cpptoc {

void CXXConstructExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CXXConstructExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CXXConstructExprHandler::handleCXXConstructExpr)
    );
}

bool CXXConstructExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::CXXConstructExprClass;
}

void CXXConstructExprHandler::handleCXXConstructExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(E->getStmtClass() == clang::Stmt::CXXConstructExprClass && "Must be CXXConstructExpr");

    const auto* cppConstructExpr = llvm::cast<clang::CXXConstructExpr>(E);

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CXXConstructExprHandler] CXXConstructExpr already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CXXConstructExprHandler] Processing CXXConstructExpr with "
                 << cppConstructExpr->getNumArgs() << " arguments\n";

    // Step 1: Recursively dispatch and translate all constructor arguments
    std::vector<clang::Expr*> translatedArgs;
    translatedArgs.reserve(cppConstructExpr->getNumArgs());

    for (unsigned i = 0; i < cppConstructExpr->getNumArgs(); ++i) {
        const clang::Expr* cppArg = cppConstructExpr->getArg(i);

        llvm::outs() << "[CXXConstructExprHandler] Dispatching argument " << i << "\n";

        // Dispatch argument via dispatcher (recursive)
        bool argHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppArg));

        if (!argHandled) {
            llvm::errs() << "[CXXConstructExprHandler] ERROR: Argument " << i
                         << " not handled by any expression handler\n";
            assert(false && "Constructor argument must be handled");
        }

        // Retrieve translated argument from ExprMapper
        clang::Expr* cArg = exprMapper.getCreated(cppArg);
        assert(cArg && "Argument must be in ExprMapper after dispatch");

        translatedArgs.push_back(cArg);
    }

    llvm::outs() << "[CXXConstructExprHandler] All " << translatedArgs.size()
                 << " arguments translated successfully\n";

    // Step 2: Get the C struct type from DeclMapper
    // C++ constructor expression has type of the class being constructed
    clang::QualType cppType = cppConstructExpr->getType();
    const clang::CXXRecordDecl* cppClass = cppType->getAsCXXRecordDecl();

    clang::QualType cType;
    if (cppClass) {
        llvm::outs() << "[CXXConstructExprHandler] Looking up C struct for C++ class: "
                     << cppClass->getNameAsString() << "\n";

        cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
        clang::Decl* cDecl = declMapper.getCreated(cppClass);

        if (cDecl) {
            // Found C struct declaration
            if (clang::RecordDecl* cStruct = llvm::dyn_cast<clang::RecordDecl>(cDecl)) {
                cType = cASTContext.getRecordType(cStruct);
                llvm::outs() << "[CXXConstructExprHandler] Found C struct type\n";
            } else {
                llvm::errs() << "[CXXConstructExprHandler] WARNING: DeclMapper entry is not RecordDecl\n";
                cType = cppType; // Fallback
            }
        } else {
            llvm::errs() << "[CXXConstructExprHandler] WARNING: C struct not found in DeclMapper for "
                         << cppClass->getNameAsString() << ", using C++ type as fallback\n";
            cType = cppType; // Fallback
        }
    } else {
        llvm::errs() << "[CXXConstructExprHandler] WARNING: Constructor expression type is not a class\n";
        cType = cppType; // Fallback
    }

    // Step 3: Create InitListExpr with translated arguments
    // This generates {arg1, arg2, ...} syntax
    clang::InitListExpr* initList = new (cASTContext) clang::InitListExpr(
        cASTContext,
        clang::SourceLocation(),
        translatedArgs,
        clang::SourceLocation()
    );
    initList->setType(cType);

    llvm::outs() << "[CXXConstructExprHandler] Created InitListExpr\n";

    // Step 4: Wrap in CompoundLiteralExpr to create (struct Type){...}
    // This is the proper C99 syntax for struct literals
    clang::CompoundLiteralExpr* compoundLit = new (cASTContext) clang::CompoundLiteralExpr(
        clang::SourceLocation(),
        cASTContext.getTrivialTypeSourceInfo(cType),
        cType,
        clang::VK_PRValue,
        initList,
        false // isFileScope
    );

    llvm::outs() << "[CXXConstructExprHandler] Created CompoundLiteralExpr (C99 syntax)\n";

    // Step 5: Store mapping in ExprMapper
    exprMapper.setCreated(E, compoundLit);

    llvm::outs() << "[CXXConstructExprHandler] CXXConstructExpr translation complete\n";
}

} // namespace cpptoc
