/**
 * @file CallExprHandler.cpp
 * @brief Implementation of CallExprHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle regular function call translation.
 */

#include "dispatch/CallExprHandler.h"
#include "mapping/ExprMapper.h"
#include "CNodeBuilder.h"
#include "SourceLocationMapper.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void CallExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&CallExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&CallExprHandler::handleCallExpr)
    );
}

bool CallExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass
    // CallExpr is distinct from:
    // - CXXOperatorCallExpr (operator overloading: obj[5])
    // - CXXMemberCallExpr (method calls: obj.method())
    // - CXXConstructExpr (constructor calls)
    return E->getStmtClass() == clang::Stmt::CallExprClass;
}

void CallExprHandler::handleCallExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(E->getStmtClass() == clang::Stmt::CallExprClass && "Must be CallExpr");

    const auto* cppCall = llvm::cast<clang::CallExpr>(E);

    llvm::outs() << "[CallExprHandler] Handling CallExpr\n";

    // Check if already translated
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
    if (exprMapper.getCreated(cppCall)) {
        llvm::outs() << "[CallExprHandler] CallExpr already translated\n";
        return;
    }

    // Get callee expression (function reference)
    const clang::Expr* cppCallee = cppCall->getCallee();
    assert(cppCallee && "CallExpr must have a callee");

    // Dispatch callee expression (usually DeclRefExpr or ImplicitCastExpr)
    clang::Expr* cppCalleeNonConst = const_cast<clang::Expr*>(cppCallee);
    bool calleeHandled = disp.dispatch(cppASTContext, cASTContext, cppCalleeNonConst);

    if (!calleeHandled) {
        llvm::errs() << "[CallExprHandler] ERROR: Callee expression not handled\n";
        llvm::errs() << "  Callee expression type: " << cppCallee->getStmtClassName() << "\n";
        assert(false && "Callee expression must be handled");
    }

    clang::Expr* cCallee = exprMapper.getCreated(cppCallee);
    assert(cCallee && "Callee must be in ExprMapper after successful dispatch");

    // Get source location for SourceLocation initialization
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile("");

    // Get the function declaration to check parameter types
    const clang::FunctionDecl* calleeDecl = cppCall->getDirectCallee();

    // Dispatch all arguments
    std::vector<clang::Expr*> cArgs;
    for (unsigned i = 0; i < cppCall->getNumArgs(); ++i) {
        const clang::Expr* cppArg = cppCall->getArg(i);

        // Dispatch argument expression
        clang::Expr* cppArgNonConst = const_cast<clang::Expr*>(cppArg);
        bool argHandled = disp.dispatch(cppASTContext, cASTContext, cppArgNonConst);

        if (!argHandled) {
            llvm::errs() << "[CallExprHandler] ERROR: Argument " << i << " not handled\n";
            assert(false && "All arguments must be handled");
        }

        clang::Expr* cArg = exprMapper.getCreated(cppArg);
        assert(cArg && "Argument must be in ExprMapper after successful dispatch");

        // Check if parameter is a reference type - if so, wrap argument with &
        if (calleeDecl && i < calleeDecl->getNumParams()) {
            const clang::ParmVarDecl* param = calleeDecl->getParamDecl(i);
            clang::QualType paramType = param->getType();

            // If parameter is a reference type, wrap the argument with address-of operator
            if (paramType->isLValueReferenceType() || paramType->isRValueReferenceType()) {
                llvm::outs() << "[CallExprHandler] Parameter " << i << " is reference type, wrapping argument with &\n";

                // Create UnaryOperator with & (address-of)
                clang::QualType argType = cArg->getType();
                clang::QualType ptrType = cASTContext.getPointerType(argType);

                cArg = clang::UnaryOperator::Create(
                    cASTContext,
                    cArg,
                    clang::UO_AddrOf,
                    ptrType,
                    clang::VK_PRValue,
                    clang::OK_Ordinary,
                    targetLoc,
                    false,  // canOverflow
                    clang::FPOptionsOverride()
                );
            }
        }

        cArgs.push_back(cArg);
    }

    // Create C CallExpr (targetLoc already initialized above)
    clang::CallExpr* cCall = clang::CallExpr::Create(
        cASTContext,
        cCallee,
        cArgs,
        cppCall->getType(),  // Return type
        clang::VK_PRValue,
        targetLoc,
        clang::FPOptionsOverride()
    );

    assert(cCall && "Failed to create C CallExpr");

    // Store in ExprMapper
    exprMapper.setCreated(cppCall, cCall);

    llvm::outs() << "[CallExprHandler] Created C CallExpr with "
                 << cArgs.size() << " arguments\n";
}

} // namespace cpptoc
