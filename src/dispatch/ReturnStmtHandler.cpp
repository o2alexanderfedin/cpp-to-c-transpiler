/**
 * @file ReturnStmtHandler.cpp
 * @brief Implementation of ReturnStmtHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle return statement translation.
 * Phase 1 implementation: Basic return statement structure (no complex expression translation).
 */

#include "dispatch/ReturnStmtHandler.h"
#include "mapping/DeclMapper.h"
#include "translation/TypeTranslator.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ReturnStmtHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    // Explicitly cast to StmtPredicate and StmtVisitor to avoid ambiguity
    // (Expr derives from Stmt, so compiler can't choose between Stmt and Expr overloads)
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&ReturnStmtHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&ReturnStmtHandler::handleReturnStmt)
    );
}

bool ReturnStmtHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");

    // Use exact type matching (getStmtClass) for ReturnStmt
    return S->getStmtClass() == clang::Stmt::ReturnStmtClass;
}

void ReturnStmtHandler::handleReturnStmt(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(S->getStmtClass() == clang::Stmt::ReturnStmtClass && "Must be ReturnStmt");

    const auto* cppReturn = llvm::cast<clang::ReturnStmt>(S);

    // Extract return value expression (may be nullptr for void return: "return;")
    const clang::Expr* cppRetValue = cppReturn->getRetValue();

    // Create C return statement
    clang::ReturnStmt* cReturn = nullptr;
    clang::Expr* cRetValue = nullptr;

    if (cppRetValue) {
        // Following Chain of Responsibility pattern: Dispatch expression to ExpressionHandler
        // Cast away const for dispatch (dispatcher interface requires non-const)
        clang::Expr* cppRetValueNonConst = const_cast<clang::Expr*>(cppRetValue);

        // Dispatch expression to handler (will be handled by ExpressionHandler when it exists)
        bool handled = disp.dispatch(cppASTContext, cASTContext, cppRetValueNonConst);

        if (handled) {
            // TODO: When ExpressionHandler is implemented, retrieve translated expression
            // from ExprMapper (similar to how FunctionHandler retrieves parameters from DeclMapper)
            // For now, ExprMapper doesn't exist yet, so this branch won't execute
            // cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
            // cRetValue = exprMapper.getCreatedExpr(cppRetValue);
            llvm::outs() << "[ReturnStmtHandler] Expression dispatched and handled\n";
        } else {
            // Phase 1 fallback: No ExpressionHandler registered yet
            // Use the C++ expression node directly (will need proper translation in future)
            llvm::outs() << "[ReturnStmtHandler] No ExpressionHandler - using fallback\n";
            cRetValue = cppRetValueNonConst;
        }

        // Create C return statement with return value
        cReturn = clang::ReturnStmt::Create(
            cASTContext,
            clang::SourceLocation(),
            cRetValue,
            nullptr  // No NRVOCandidate in C
        );
    } else {
        // Void return: "return;"
        cReturn = clang::ReturnStmt::Create(
            cASTContext,
            clang::SourceLocation(),
            nullptr,  // No return value
            nullptr   // No NRVOCandidate in C
        );
    }

    assert(cReturn && "Failed to create C ReturnStmt");

    // Store mapping so parent handler (e.g., CompoundStmt handler) can retrieve this statement
    // Note: For statements, we use DeclMapper's statement mapping capability
    // (DeclMapper handles both Decl and Stmt mappings in the current architecture)
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();

    // Debug output for verification
    if (cppRetValue) {
        llvm::outs() << "[ReturnStmtHandler] Translated return statement with value\n";
    } else {
        llvm::outs() << "[ReturnStmtHandler] Translated void return statement\n";
    }

    // Note: The created ReturnStmt will be used by parent handler (e.g., CompoundStmtHandler)
    // It's not added directly to any parent - the parent handler will retrieve it
    // For now in Phase 1, we just create the node and verify it's properly formed
}

} // namespace cpptoc
