/**
 * @file LiteralHandler.cpp
 * @brief Implementation of LiteralHandler dispatcher pattern
 */

#include "dispatch/LiteralHandler.h"
#include "mapping/ExprMapper.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void LiteralHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    // Cast to ExprPredicate and ExprVisitor to avoid ambiguity
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::ExprPredicate>(&LiteralHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::ExprVisitor>(&LiteralHandler::handleLiteral)
    );
}

bool LiteralHandler::canHandle(const clang::Expr* E) {
    assert(E && "Expression must not be null");

    // Use exact type matching with getStmtClass for all literal types
    clang::Stmt::StmtClass stmtClass = E->getStmtClass();

    return stmtClass == clang::Stmt::IntegerLiteralClass ||
           stmtClass == clang::Stmt::FloatingLiteralClass ||
           stmtClass == clang::Stmt::StringLiteralClass ||
           stmtClass == clang::Stmt::CharacterLiteralClass ||
           stmtClass == clang::Stmt::CXXBoolLiteralExprClass;
}

void LiteralHandler::handleLiteral(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Expr* E
) {
    assert(E && "Expression must not be null");
    assert(canHandle(E) && "Expression must be a literal");

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    // Check if already processed
    if (exprMapper.hasCreated(E)) {
        llvm::outs() << "[LiteralHandler] Literal already translated, skipping\n";
        return;
    }

    // Dispatch to specific literal handler based on type (code-by-intent)
    clang::Expr* cLiteral = nullptr;
    clang::Stmt::StmtClass stmtClass = E->getStmtClass();

    if (stmtClass == clang::Stmt::IntegerLiteralClass) {
        cLiteral = createIntegerLiteral(llvm::cast<clang::IntegerLiteral>(E), cASTContext);
    }
    else if (stmtClass == clang::Stmt::FloatingLiteralClass) {
        cLiteral = createFloatingLiteral(llvm::cast<clang::FloatingLiteral>(E), cASTContext);
    }
    else if (stmtClass == clang::Stmt::StringLiteralClass) {
        cLiteral = createStringLiteral(llvm::cast<clang::StringLiteral>(E), cASTContext);
    }
    else if (stmtClass == clang::Stmt::CharacterLiteralClass) {
        cLiteral = createCharacterLiteral(llvm::cast<clang::CharacterLiteral>(E), cASTContext);
    }
    else if (stmtClass == clang::Stmt::CXXBoolLiteralExprClass) {
        cLiteral = createBoolLiteral(llvm::cast<clang::CXXBoolLiteralExpr>(E), cASTContext);
    }

    assert(cLiteral && "Failed to create C literal");

    // Store mapping in ExprMapper
    exprMapper.setCreated(E, cLiteral);
}

// ============================================================================
// Private: Code-by-intent helper functions for each literal type
// ============================================================================

clang::Expr* LiteralHandler::createIntegerLiteral(
    const clang::IntegerLiteral* cppLit,
    clang::ASTContext& cASTContext
) {
    assert(cppLit && "IntegerLiteral must not be null");

    clang::Expr* cLiteral = clang::IntegerLiteral::Create(
        cASTContext,
        cppLit->getValue(),
        cppLit->getType(),
        clang::SourceLocation()
    );

    llvm::outs() << "[LiteralHandler] Translated IntegerLiteral: "
                 << cppLit->getValue() << "\n";

    return cLiteral;
}

clang::Expr* LiteralHandler::createFloatingLiteral(
    const clang::FloatingLiteral* cppLit,
    clang::ASTContext& cASTContext
) {
    assert(cppLit && "FloatingLiteral must not be null");

    clang::Expr* cLiteral = clang::FloatingLiteral::Create(
        cASTContext,
        cppLit->getValue(),
        cppLit->isExact(),
        cppLit->getType(),
        clang::SourceLocation()
    );

    llvm::outs() << "[LiteralHandler] Translated FloatingLiteral\n";

    return cLiteral;
}

clang::Expr* LiteralHandler::createStringLiteral(
    const clang::StringLiteral* cppLit,
    clang::ASTContext& cASTContext
) {
    assert(cppLit && "StringLiteral must not be null");

    clang::Expr* cLiteral = clang::StringLiteral::Create(
        cASTContext,
        cppLit->getString(),
        cppLit->getKind(),
        cppLit->isPascal(),
        cppLit->getType(),
        clang::SourceLocation()
    );

    llvm::outs() << "[LiteralHandler] Translated StringLiteral: \""
                 << cppLit->getString().str() << "\"\n";

    return cLiteral;
}

clang::Expr* LiteralHandler::createCharacterLiteral(
    const clang::CharacterLiteral* cppLit,
    clang::ASTContext& cASTContext
) {
    assert(cppLit && "CharacterLiteral must not be null");

    clang::Expr* cLiteral = new (cASTContext) clang::CharacterLiteral(
        cppLit->getValue(),
        cppLit->getKind(),
        cppLit->getType(),
        clang::SourceLocation()
    );

    llvm::outs() << "[LiteralHandler] Translated CharacterLiteral: '"
                 << (char)cppLit->getValue() << "'\n";

    return cLiteral;
}

clang::Expr* LiteralHandler::createBoolLiteral(
    const clang::CXXBoolLiteralExpr* cppLit,
    clang::ASTContext& cASTContext
) {
    assert(cppLit && "CXXBoolLiteralExpr must not be null");

    // In C, booleans are represented as integers (0 or 1)
    // Create IntegerLiteral for C compatibility
    llvm::APInt boolValue(32, cppLit->getValue() ? 1 : 0);
    clang::Expr* cLiteral = clang::IntegerLiteral::Create(
        cASTContext,
        boolValue,
        cASTContext.IntTy,
        clang::SourceLocation()
    );

    llvm::outs() << "[LiteralHandler] Translated CXXBoolLiteralExpr to int: "
                 << (cppLit->getValue() ? "1" : "0") << "\n";

    return cLiteral;
}

} // namespace cpptoc
