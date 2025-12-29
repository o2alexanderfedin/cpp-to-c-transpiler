/**
 * @file CompoundStmtHandler.cpp
 * @brief Implementation of CompoundStmtHandler dispatcher pattern
 */

#include "dispatch/CompoundStmtHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Stmt.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <vector>

namespace cpptoc {

void CompoundStmtHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    // Cast to StmtPredicate and StmtVisitor to avoid ambiguity
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&CompoundStmtHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&CompoundStmtHandler::handleCompoundStmt)
    );
}

bool CompoundStmtHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");

    // Use exact type matching with getStmtClass
    return S->getStmtClass() == clang::Stmt::CompoundStmtClass;
}

void CompoundStmtHandler::handleCompoundStmt(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(canHandle(S) && "Statement must be CompoundStmt");

    const auto* cppCompound = llvm::cast<clang::CompoundStmt>(S);

    llvm::outs() << "[CompoundStmtHandler] Processing CompoundStmt with "
                 << cppCompound->size() << " statements\n";

    // Translate each statement in the compound statement body
    std::vector<clang::Stmt*> cStmts;
    cStmts.reserve(cppCompound->size());

    for (const clang::Stmt* cppStmt : cppCompound->body()) {
        llvm::outs() << "[CompoundStmtHandler] Dispatching statement: "
                     << cppStmt->getStmtClassName() << "\n";

        // CRITICAL: Dispatch statement via dispatcher (recursive)
        bool handled = disp.dispatch(
            cppASTContext,
            cASTContext,
            const_cast<clang::Stmt*>(cppStmt)
        );

        if (!handled) {
            llvm::errs() << "[CompoundStmtHandler] WARNING: Statement not handled: "
                         << cppStmt->getStmtClassName() << "\n";
            llvm::errs() << "  Skipping unhandled statement in compound statement\n";
            // Continue with next statement instead of failing
            // This allows partial translation during development
            continue;
        }

        // For now, we don't have a StmtMapper to retrieve the translated statement
        // Once we add StmtMapper, we'll retrieve the translated statement here
        // For now, this handler just ensures statements are dispatched
        llvm::outs() << "[CompoundStmtHandler] Statement dispatched successfully\n";
    }

    llvm::outs() << "[CompoundStmtHandler] Processed CompoundStmt with "
                 << cStmts.size() << " translated statements\n";

    // TODO: Once we have StmtMapper, create C CompoundStmt and store mapping
    // For now, this handler is primarily for dispatching child statements
}

} // namespace cpptoc
