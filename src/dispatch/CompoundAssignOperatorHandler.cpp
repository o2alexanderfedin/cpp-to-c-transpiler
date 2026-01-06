/**
 * @file CompoundAssignOperatorHandler.cpp
 * @brief Implementation of CompoundAssignOperatorHandler with recursive dispatch
 */

#include "dispatch/CompoundAssignOperatorHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CompoundAssignOperatorHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CompoundAssignOperatorHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CompoundAssignOperatorHandler::handleCompoundAssignOperator)
    );
}

bool CompoundAssignOperatorHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    return E->getStmtClass() == clang::Stmt::CompoundAssignOperatorClass;
}

clang::BinaryOperatorKind CompoundAssignOperatorHandler::convertToBinaryOp(clang::BinaryOperatorKind compoundOp) {
    // Convert compound assignment operator to corresponding binary operator
    // +=  -> +
    // -=  -> -
    // *=  -> *
    // /=  -> /
    // %=  -> %
    // &=  -> &
    // |=  -> |
    // ^=  -> ^
    // <<= -> <<
    // >>= -> >>

    switch (compoundOp) {
        case clang::BO_AddAssign:  return clang::BO_Add;
        case clang::BO_SubAssign:  return clang::BO_Sub;
        case clang::BO_MulAssign:  return clang::BO_Mul;
        case clang::BO_DivAssign:  return clang::BO_Div;
        case clang::BO_RemAssign:  return clang::BO_Rem;
        case clang::BO_AndAssign:  return clang::BO_And;
        case clang::BO_OrAssign:   return clang::BO_Or;
        case clang::BO_XorAssign:  return clang::BO_Xor;
        case clang::BO_ShlAssign:  return clang::BO_Shl;
        case clang::BO_ShrAssign:  return clang::BO_Shr;
        default:
            llvm::errs() << "[CompoundAssignOperatorHandler] ERROR: Unknown compound assignment operator\n";
            assert(false && "Unknown compound assignment operator");
            return clang::BO_Add; // unreachable
    }
}

void CompoundAssignOperatorHandler::handleCompoundAssignOperator(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(E->getStmtClass() == clang::Stmt::CompoundAssignOperatorClass && "Must be CompoundAssignOperator");

    const auto* cppCompoundAssign = llvm::cast<clang::CompoundAssignOperator>(E);

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[CompoundAssignOperatorHandler] CompoundAssignOperator already translated, skipping\n";
        return;
    }

    // Extract LHS and RHS subexpressions
    const clang::Expr* cppLHS = cppCompoundAssign->getLHS();
    const clang::Expr* cppRHS = cppCompoundAssign->getRHS();

    llvm::outs() << "[CompoundAssignOperatorHandler] Processing CompoundAssignOperator: "
                 << cppCompoundAssign->getOpcodeStr().str() << "\n";

    // CRITICAL: Recursive dispatch pattern
    // Dispatch LHS via dispatcher (may trigger DeclRefExprHandler, MemberExprHandler, ArraySubscriptExprHandler, etc.)
    llvm::outs() << "[CompoundAssignOperatorHandler] Dispatching LHS subexpression\n";
    bool lhsHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppLHS));

    if (!lhsHandled) {
        llvm::errs() << "[CompoundAssignOperatorHandler] ERROR: LHS not handled by any expression handler\n";
        llvm::errs() << "  LHS expression type: " << cppLHS->getStmtClassName() << "\n";
        assert(false && "LHS must be handled");
    }

    // Retrieve translated LHS from ExprMapper
    clang::Expr* cLHS = exprMapper.getCreated(cppLHS);
    assert(cLHS && "LHS must be in ExprMapper after dispatch");

    // Dispatch RHS via dispatcher (recursive)
    llvm::outs() << "[CompoundAssignOperatorHandler] Dispatching RHS subexpression\n";
    bool rhsHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppRHS));

    if (!rhsHandled) {
        llvm::errs() << "[CompoundAssignOperatorHandler] ERROR: RHS not handled by any expression handler\n";
        llvm::errs() << "  RHS expression type: " << cppRHS->getStmtClassName() << "\n";
        assert(false && "RHS must be handled");
    }

    // Retrieve translated RHS from ExprMapper
    clang::Expr* cRHS = exprMapper.getCreated(cppRHS);
    assert(cRHS && "RHS must be in ExprMapper after dispatch");

    llvm::outs() << "[CompoundAssignOperatorHandler] Both operands translated successfully\n";

    // TRANSLATION LOGIC:
    // C++: x += 5
    // C:   x = x + 5
    //
    // Step 1: Create BinaryOperator for the operation (e.g., + for +=)
    // Step 2: Create Assignment (BinaryOperator with BO_Assign) combining LHS and the operation result

    // Convert compound assignment opcode to binary opcode
    clang::BinaryOperatorKind binaryOp = convertToBinaryOp(cppCompoundAssign->getOpcode());

    llvm::outs() << "[CompoundAssignOperatorHandler] Converting "
                 << cppCompoundAssign->getOpcodeStr().str()
                 << " to assignment with "
                 << clang::BinaryOperator::getOpcodeStr(binaryOp).str() << "\n";

    // We need to duplicate LHS for the operation (since x += 5 becomes x = x + 5)
    // Note: This is a shallow copy, but should work for most cases
    // For complex LHS (like a[i++]), this might need special handling in the future
    clang::Expr* cLHSForOperation = cLHS;

    // Create BinaryOperator for the operation (e.g., x + 5)
    clang::BinaryOperator* cOperation = clang::BinaryOperator::Create(
        cASTContext,
        cLHSForOperation,
        cRHS,
        binaryOp,
        cppCompoundAssign->getType(),  // Result type of the operation
        cppCompoundAssign->getValueKind(),
        cppCompoundAssign->getObjectKind(),
        clang::SourceLocation(),
        clang::FPOptionsOverride()
    );

    llvm::outs() << "[CompoundAssignOperatorHandler] Created C BinaryOperator for operation: "
                 << clang::BinaryOperator::getOpcodeStr(binaryOp).str() << "\n";

    // Create Assignment (x = ...)
    clang::BinaryOperator* cAssignment = clang::BinaryOperator::Create(
        cASTContext,
        cLHS,
        cOperation,
        clang::BO_Assign,
        cppCompoundAssign->getType(),  // Result type of the assignment
        cppCompoundAssign->getValueKind(),
        cppCompoundAssign->getObjectKind(),
        clang::SourceLocation(),
        clang::FPOptionsOverride()
    );

    llvm::outs() << "[CompoundAssignOperatorHandler] Created C Assignment: "
                 << cppCompoundAssign->getOpcodeStr().str()
                 << " -> = with " << clang::BinaryOperator::getOpcodeStr(binaryOp).str() << "\n";

    // Store mapping in ExprMapper
    exprMapper.setCreated(E, cAssignment);
}

} // namespace cpptoc
