/**
 * @file CompoundAssignOperatorHandler.cpp
 * @brief Implementation of CompoundAssignOperatorHandler
 */

#include "dispatch/CompoundAssignOperatorHandler.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CompoundAssignOperatorHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    // CompoundAssignOperator is both an Expr and a Stmt
    // Register for both to handle all cases
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&CompoundAssignOperatorHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&CompoundAssignOperatorHandler::handleCompoundAssignOperator)
    );
}

bool CompoundAssignOperatorHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");
    return S->getStmtClass() == clang::Stmt::CompoundAssignOperatorClass;
}

void CompoundAssignOperatorHandler::handleCompoundAssignOperator(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(canHandle(S) && "Must be CompoundAssignOperator");

    const auto* cppCompoundAssign = llvm::cast<clang::CompoundAssignOperator>(S);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();

    // Check if already processed
    if (exprMapper.hasCreated(llvm::cast<clang::Expr>(S))) {
        llvm::outs() << "[CompoundAssignOperatorHandler] Already translated, skipping\n";
        return;
    }

    llvm::outs() << "[CompoundAssignOperatorHandler] Processing compound assignment operator: "
                 << cppCompoundAssign->getOpcodeStr().str() << "\n";

    // Process LHS
    const clang::Expr* cppLHS = cppCompoundAssign->getLHS();
    bool lhsHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppLHS));

    if (!lhsHandled) {
        llvm::errs() << "[CompoundAssignOperatorHandler] ERROR: LHS not handled\n";
        llvm::errs() << "  LHS expression type: " << cppLHS->getStmtClassName() << "\n";
        assert(false && "LHS must be handled");
    }

    clang::Expr* cLHS = exprMapper.getCreated(cppLHS);
    assert(cLHS && "LHS must be in ExprMapper");

    // Process RHS
    const clang::Expr* cppRHS = cppCompoundAssign->getRHS();
    bool rhsHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppRHS));

    if (!rhsHandled) {
        llvm::errs() << "[CompoundAssignOperatorHandler] ERROR: RHS not handled\n";
        llvm::errs() << "  RHS expression type: " << cppRHS->getStmtClassName() << "\n";
        assert(false && "RHS must be handled");
    }

    clang::Expr* cRHS = exprMapper.getCreated(cppRHS);
    assert(cRHS && "RHS must be in ExprMapper");

    // Create C CompoundAssignOperator
    clang::CompoundAssignOperator* cCompoundAssign = clang::CompoundAssignOperator::Create(
        cASTContext,
        cLHS,
        cRHS,
        cppCompoundAssign->getOpcode(),
        cppCompoundAssign->getType(),
        cppCompoundAssign->getValueKind(),
        cppCompoundAssign->getObjectKind(),
        cppCompoundAssign->getOperatorLoc(),
        clang::FPOptionsOverride(),
        cppCompoundAssign->getComputationLHSType(),
        cppCompoundAssign->getComputationResultType()
    );

    llvm::outs() << "[CompoundAssignOperatorHandler] Created compound assignment\n";

    // Store in both mappers (since it's both Expr and Stmt)
    exprMapper.setCreated(llvm::cast<clang::Expr>(S), cCompoundAssign);
    stmtMapper.setCreated(S, cCompoundAssign);
}

} // namespace cpptoc
