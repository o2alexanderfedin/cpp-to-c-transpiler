#include "dispatch/InitListExprHandler.h"
#include "mapping/ExprMapper.h"
#include "SourceLocationMapper.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void InitListExprHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&InitListExprHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&InitListExprHandler::handleInitListExpr)
    );
}

bool InitListExprHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");
    return E->getStmtClass() == clang::Stmt::InitListExprClass;
}

void InitListExprHandler::handleInitListExpr(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Must be InitListExpr");

    const auto* cppInitList = llvm::cast<clang::InitListExpr>(E);
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[InitListExprHandler] InitListExpr already translated, skipping\n";
        return;
    }

    llvm::outs() << "[InitListExprHandler] Processing InitListExpr with "
                 << cppInitList->getNumInits() << " initializers\n";

    // Translate each initializer expression
    std::vector<clang::Expr*> cInits;
    cInits.reserve(cppInitList->getNumInits());

    for (unsigned i = 0; i < cppInitList->getNumInits(); ++i) {
        const clang::Expr* cppInit = cppInitList->getInit(i);

        // Dispatch the initializer
        bool handled = disp.dispatch(cppASTContext, cASTContext, cppInit);

        if (!handled) {
            llvm::errs() << "[InitListExprHandler] ERROR: Initializer " << i << " not handled\n";
            assert(false && "All initializers must be handled");
        }

        // Retrieve translated initializer
        clang::Expr* cInit = exprMapper.getCreated(cppInit);
        assert(cInit && "Initializer must be in ExprMapper after dispatch");

        cInits.push_back(cInit);
    }

    llvm::outs() << "[InitListExprHandler] All " << cInits.size() << " initializers translated\n";

    // Get source location for SourceLocation initialization
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile("");

    // Create C InitListExpr
    clang::InitListExpr* cInitList = new (cASTContext) clang::InitListExpr(
        cASTContext,
        targetLoc,  // LBraceLoc
        cInits,
        targetLoc   // RBraceLoc
    );

    // Set type (same as C++ - arrays are arrays in C too)
    cInitList->setType(cppInitList->getType());

    llvm::outs() << "[InitListExprHandler] Created C InitListExpr\n";

    // Store mapping
    exprMapper.setCreated(E, cInitList);
}

} // namespace cpptoc
