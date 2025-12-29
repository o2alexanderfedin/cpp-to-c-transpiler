/**
 * @file CompoundStmtHandler.cpp
 * @brief Implementation of CompoundStmtHandler dispatcher pattern
 */

#include "dispatch/CompoundStmtHandler.h"
#include "mapping/StmtMapper.h"
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

    // Get StmtMapper for retrieving and storing statement mappings
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();

    // Check if already processed
    if (stmtMapper.hasCreatedStmt(S)) {
        llvm::outs() << "[CompoundStmtHandler] CompoundStmt already translated, skipping\n";
        return;
    }

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

        // Retrieve translated statement from StmtMapper
        clang::Stmt* cStmt = stmtMapper.getCreatedStmt(cppStmt);
        if (!cStmt) {
            llvm::errs() << "[CompoundStmtHandler] WARNING: Statement dispatched but not in StmtMapper: "
                         << cppStmt->getStmtClassName() << "\n";
            llvm::errs() << "  Skipping statement not found in mapper\n";
            // Continue with next statement - allows graceful degradation
            continue;
        }

        // Add translated statement to collection
        cStmts.push_back(cStmt);
        llvm::outs() << "[CompoundStmtHandler] Statement translated successfully: "
                     << cStmt->getStmtClassName() << "\n";
    }

    llvm::outs() << "[CompoundStmtHandler] Collected " << cStmts.size()
                 << " translated statements (out of " << cppCompound->size() << " original)\n";

    // Create C CompoundStmt with translated statements
    clang::CompoundStmt* cCompound = clang::CompoundStmt::Create(
        cASTContext,
        cStmts,
        clang::FPOptionsOverride(),
        clang::SourceLocation(),
        clang::SourceLocation()
    );

    llvm::outs() << "[CompoundStmtHandler] Created C CompoundStmt with "
                 << cCompound->size() << " statements\n";

    // Store mapping in StmtMapper
    stmtMapper.setCreatedStmt(S, cCompound);

    llvm::outs() << "[CompoundStmtHandler] CompoundStmt translation complete and stored in StmtMapper\n";
}

} // namespace cpptoc
