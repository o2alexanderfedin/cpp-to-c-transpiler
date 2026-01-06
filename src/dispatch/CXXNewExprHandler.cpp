/**
 * @file CXXNewExprHandler.cpp
 * @brief Implementation of CXXNewExprHandler
 */

#include "dispatch/CXXNewExprHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CXXNewExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CXXNewExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CXXNewExprHandler::handleCXXNewExpr)
    );
}

bool CXXNewExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::CXXNewExprClass;
}

void CXXNewExprHandler::handleCXXNewExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be CXXNewExpr");

    const auto* cppNew = llvm::cast<clang::CXXNewExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CXXNewExprHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CXXNewExprHandler] Processing CXXNewExpr (translating to malloc)\n";

    // Get the allocated type
    clang::QualType allocatedType = cppNew->getAllocatedType();

    // Calculate size expression for malloc
    // For new T[n], we need sizeof(T) * n
    // For new T, we need sizeof(T)

    clang::Expr* sizeExpr = nullptr;

    if (cppNew->isArray()) {
        // Array allocation: new T[n]
        llvm::outs() << "[CXXNewExprHandler] Array allocation\n";

        // Get array size expression
        const clang::Expr* cppArraySize = cppNew->getArraySize().value_or(nullptr);
        if (cppArraySize) {
            // Dispatch array size expression
            bool sizeHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppArraySize));
            if (!sizeHandled) {
                llvm::errs() << "[CXXNewExprHandler] ERROR: Array size not handled\n";
                llvm::errs() << "  Size expression type: " << cppArraySize->getStmtClassName() << "\n";
                assert(false && "Array size must be handled");
            }

            clang::Expr* cArraySize = exprMapper.getCreated(cppArraySize);
            assert(cArraySize && "Array size must be in ExprMapper");

            // Create sizeof(T) * n expression
            // For now, create a placeholder - full implementation needs sizeof expression
            sizeExpr = cArraySize;
        }
    } else {
        // Single object allocation: new T
        llvm::outs() << "[CXXNewExprHandler] Single object allocation\n";
        // For single object, size is sizeof(T)
        // Create a placeholder integer literal for now
        llvm::APInt sizeValue(32, 1);  // Simplified - should be actual sizeof(T)
        sizeExpr = clang::IntegerLiteral::Create(
            cASTContext,
            sizeValue,
            cASTContext.IntTy,
            clang::SourceLocation()
        );
    }

    // Create call to malloc(size)
    // We need to create a DeclRefExpr for malloc and a CallExpr

    // For now, create a simple placeholder CallExpr
    // Full implementation would require:
    // 1. Declaration of malloc function
    // 2. Proper sizeof() expression creation
    // 3. Cast from void* to the appropriate type

    // Create a placeholder integer literal (0) for now
    // This is not correct but allows transpilation to continue
    llvm::APInt zeroValue(32, 0);
    clang::IntegerLiteral* cPlaceholder = clang::IntegerLiteral::Create(
        cASTContext,
        zeroValue,
        cASTContext.IntTy,
        clang::SourceLocation()
    );

    llvm::outs() << "[CXXNewExprHandler] Created placeholder for new expression (full malloc translation not yet implemented)\n";

    // Store mapping
    exprMapper.setCreated(E, cPlaceholder);
}

} // namespace cpptoc
