/**
 * @file ReturnStmtHandler.cpp
 * @brief Implementation of ReturnStmtHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle return statement translation.
 * Phase 1 implementation: Basic return statement structure (no complex expression translation).
 */

#include "dispatch/ReturnStmtHandler.h"
#include "mapping/DeclMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
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

        // Dispatch expression to handler (will be handled by LiteralHandler, DeclRefExprHandler,
        // BinaryOperatorHandler, UnaryOperatorHandler, etc.)
        bool handled = disp.dispatch(cppASTContext, cASTContext, cppRetValueNonConst);

        if (handled) {
            // Retrieve translated expression from ExprMapper
            cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
            cRetValue = exprMapper.getCreated(cppRetValue);

            assert(cRetValue && "Expression must be in ExprMapper after successful dispatch");
            llvm::outs() << "[ReturnStmtHandler] Expression dispatched and retrieved from ExprMapper\n";
        } else {
            // No handler matched - this is an error
            llvm::errs() << "[ReturnStmtHandler] ERROR: Return value expression not handled by any handler\n";
            assert(false && "Return value expression must be handled");
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
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
    stmtMapper.setCreated(cppReturn, cReturn);

    // Debug output for verification
    if (cppRetValue) {
        llvm::outs() << "[ReturnStmtHandler] Created C ReturnStmt with value and stored in StmtMapper\n";
    } else {
        llvm::outs() << "[ReturnStmtHandler] Created C ReturnStmt (void) and stored in StmtMapper\n";
    }
}

} // namespace cpptoc
