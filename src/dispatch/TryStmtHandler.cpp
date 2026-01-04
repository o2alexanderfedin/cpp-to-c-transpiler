/**
 * @file TryStmtHandler.cpp
 * @brief Implementation of TryStmtHandler dispatcher pattern
 */

// CRITICAL: Include CppToCVisitorDispatcher BEFORE any headers that have it as forward declaration
// This ensures the full definition is always used
#include "dispatch/CppToCVisitorDispatcher.h"

// Now safe to include other headers
#include "dispatch/TryStmtHandler.h"
#include "TryCatchTransformer.h"
#include "mapping/StmtMapper.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void TryStmtHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    // Cast to StmtPredicate and StmtVisitor to match dispatcher interface
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&TryStmtHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&TryStmtHandler::handleTryStmt)
    );
}

bool TryStmtHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");

    // Use exact type matching with getStmtClass
    return S->getStmtClass() == clang::Stmt::CXXTryStmtClass;
}

void TryStmtHandler::handleTryStmt(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(canHandle(S) && "Statement must be CXXTryStmt");

    const auto* tryStmt = llvm::cast<clang::CXXTryStmt>(S);

    llvm::outs() << "[TryStmtHandler] Processing CXXTryStmt with "
                 << tryStmt->getNumHandlers() << " catch handlers\n";

    // Check if already processed
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
    if (stmtMapper.hasCreated(tryStmt)) {
        llvm::outs() << "[TryStmtHandler] CXXTryStmt already translated, skipping\n";
        return;
    }

    // Phase 2: Delegate to TryCatchTransformer service class (string-based for now)
    // Phase 6 will refactor to return C AST nodes

    // Generate unique frame variable and action table names
    // TODO: Use counter or UUID for nested try-catch blocks
    static int frameCounter = 0;
    std::string frameVarName = "frame_" + std::to_string(frameCounter);
    std::string actionsTableName = "actions_" + std::to_string(frameCounter);
    frameCounter++;

    // Phase 4: Use dispatcher-based version of transformTryCatch
    clang::TryCatchTransformer transformer;
    std::string tryCatchCode = transformer.transformTryCatch(
        tryStmt,
        frameVarName,
        actionsTableName,
        disp,        // Pass dispatcher for recursive statement translation
        cppASTContext,
        cASTContext
    );

    llvm::outs() << "[TryStmtHandler] Generated try-catch code:\n" << tryCatchCode << "\n";

    // TODO Phase 6: Store C Stmt* in StmtMapper instead of string
    // For now, we don't have a C AST representation yet
    // The string will be used by parent statement handler

    llvm::outs() << "[TryStmtHandler] CXXTryStmt translation complete (string-based)\n";
}

} // namespace cpptoc
