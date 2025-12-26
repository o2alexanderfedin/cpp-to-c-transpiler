/**
 * @file StatementHandler.cpp
 * @brief Implementation of StatementHandler
 *
 * TDD Implementation: Start minimal, add complexity as tests demand.
 *
 * Translation Strategy:
 * - Most statements translate directly (same syntax in C and C++)
 * - Key work is recursively translating sub-statements and expressions
 * - Delegate to ExpressionHandler for expressions
 * - Delegate to VariableHandler for declarations
 */

#include "handlers/StatementHandler.h"
#include "handlers/HandlerContext.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

bool StatementHandler::canHandle(const clang::Stmt* S) const {
    if (!S) return false;

    // Handle return, compound, and control flow statements (Phase 1-2)
    // Task 5: While loops, Task 6: Do-while, Task 7: For loops
    // Goto and Label statements
    switch (S->getStmtClass()) {
        case clang::Stmt::ReturnStmtClass:
        case clang::Stmt::CompoundStmtClass:
        case clang::Stmt::IfStmtClass:
        case clang::Stmt::WhileStmtClass:
        case clang::Stmt::DoStmtClass:
        case clang::Stmt::ForStmtClass:
        case clang::Stmt::SwitchStmtClass:
        case clang::Stmt::CaseStmtClass:
        case clang::Stmt::DefaultStmtClass:
        case clang::Stmt::BreakStmtClass:
        case clang::Stmt::ContinueStmtClass:
        case clang::Stmt::GotoStmtClass:
        case clang::Stmt::LabelStmtClass:
            return true;
        default:
            return false;
    }
}

clang::Stmt* StatementHandler::handleStmt(const clang::Stmt* S, HandlerContext& ctx) {
    if (!S) return nullptr;

    switch (S->getStmtClass()) {
        case clang::Stmt::ReturnStmtClass:
            return translateReturnStmt(llvm::cast<clang::ReturnStmt>(S), ctx);

        case clang::Stmt::CompoundStmtClass:
            return translateCompoundStmt(llvm::cast<clang::CompoundStmt>(S), ctx);

        case clang::Stmt::IfStmtClass:
            return translateIfStmt(llvm::cast<clang::IfStmt>(S), ctx);

        case clang::Stmt::WhileStmtClass:
            return translateWhileStmt(llvm::cast<clang::WhileStmt>(S), ctx);

        case clang::Stmt::DoStmtClass:
            return translateDoStmt(llvm::cast<clang::DoStmt>(S), ctx);

        case clang::Stmt::ForStmtClass:
            return translateForStmt(llvm::cast<clang::ForStmt>(S), ctx);

        case clang::Stmt::SwitchStmtClass:
            return translateSwitchStmt(llvm::cast<clang::SwitchStmt>(S), ctx);

        case clang::Stmt::CaseStmtClass:
            return translateCaseStmt(llvm::cast<clang::CaseStmt>(S), ctx);

        case clang::Stmt::DefaultStmtClass:
            return translateDefaultStmt(llvm::cast<clang::DefaultStmt>(S), ctx);

        case clang::Stmt::BreakStmtClass:
            return translateBreakStmt(llvm::cast<clang::BreakStmt>(S), ctx);

        case clang::Stmt::ContinueStmtClass:
            return translateContinueStmt(llvm::cast<clang::ContinueStmt>(S), ctx);

        case clang::Stmt::GotoStmtClass:
            return translateGotoStmt(llvm::cast<clang::GotoStmt>(S), ctx);

        case clang::Stmt::LabelStmtClass:
            return translateLabelStmt(llvm::cast<clang::LabelStmt>(S), ctx);

        default:
            // For now, pass through other statements
            // TODO: Add support for more statement types in later phases
            return const_cast<clang::Stmt*>(S);
    }
}

clang::ReturnStmt* StatementHandler::translateReturnStmt(
    const clang::ReturnStmt* RS,
    HandlerContext& ctx
) {
    // Get return expression (may be null for void return)
    const clang::Expr* retValue = RS->getRetValue();
    clang::Expr* cRetValue = nullptr;

    if (retValue) {
        // For now, pass through the expression
        // TODO: Delegate to ExpressionHandler when available
        cRetValue = const_cast<clang::Expr*>(retValue);
    }

    // Create C return statement using CNodeBuilder
    clang::ASTContext& cContext = ctx.getCContext();
    return clang::ReturnStmt::Create(
        cContext,
        RS->getReturnLoc(),
        cRetValue,
        nullptr // NRVOCandidate
    );
}

clang::CompoundStmt* StatementHandler::translateCompoundStmt(
    const clang::CompoundStmt* CS,
    HandlerContext& ctx
) {
    // Translate each statement in the compound statement
    std::vector<clang::Stmt*> cStmts;

    for (const clang::Stmt* S : CS->body()) {
        clang::Stmt* cStmt = handleStmt(S, ctx);
        if (cStmt) {
            cStmts.push_back(cStmt);
        }
    }

    // Create C compound statement using CNodeBuilder
    clang::ASTContext& cContext = ctx.getCContext();
    return clang::CompoundStmt::Create(
        cContext,
        cStmts,
        clang::FPOptionsOverride(),
        CS->getLBracLoc(),
        CS->getRBracLoc()
    );
}

clang::IfStmt* StatementHandler::translateIfStmt(
    const clang::IfStmt* IS,
    HandlerContext& ctx
) {
    clang::ASTContext& cContext = ctx.getCContext();

    // Translate condition
    const clang::Expr* cond = IS->getCond();
    clang::Expr* cCond = const_cast<clang::Expr*>(cond);

    // Translate then branch
    const clang::Stmt* thenStmt = IS->getThen();
    clang::Stmt* cThenStmt = handleStmt(thenStmt, ctx);

    // Translate else branch (if present)
    clang::Stmt* cElseStmt = nullptr;
    if (IS->getElse()) {
        cElseStmt = handleStmt(IS->getElse(), ctx);
    }

    // Create C if statement
    return clang::IfStmt::Create(
        cContext,
        IS->getIfLoc(),
        clang::IfStatementKind::Ordinary,
        nullptr, // init (C++17)
        nullptr, // condVar
        cCond,
        clang::SourceLocation(),
        clang::SourceLocation(),
        cThenStmt,
        cElseStmt ? IS->getElseLoc() : clang::SourceLocation(),
        cElseStmt
    );
}

clang::WhileStmt* StatementHandler::translateWhileStmt(
    const clang::WhileStmt* WS,
    HandlerContext& ctx
) {
    clang::ASTContext& cContext = ctx.getCContext();

    // Translate condition
    const clang::Expr* cond = WS->getCond();
    clang::Expr* cCond = const_cast<clang::Expr*>(cond);

    // Translate body
    const clang::Stmt* body = WS->getBody();
    clang::Stmt* cBody = handleStmt(body, ctx);

    // Create C while statement
    return clang::WhileStmt::Create(
        cContext,
        nullptr, // ConditionVariable
        cCond,
        cBody,
        WS->getWhileLoc(),
        clang::SourceLocation(), // LParenLoc
        clang::SourceLocation()  // RParenLoc
    );
}

// Placeholder implementations for future tasks
clang::SwitchStmt* StatementHandler::translateSwitchStmt(
    const clang::SwitchStmt* SS,
    HandlerContext& ctx
) {
    // TODO: Task 8 - Implement switch translation
    return const_cast<clang::SwitchStmt*>(SS);
}

clang::CaseStmt* StatementHandler::translateCaseStmt(
    const clang::CaseStmt* CS,
    HandlerContext& ctx
) {
    // TODO: Task 8 - Implement case translation
    return const_cast<clang::CaseStmt*>(CS);
}

clang::DefaultStmt* StatementHandler::translateDefaultStmt(
    const clang::DefaultStmt* DS,
    HandlerContext& ctx
) {
    // TODO: Task 8 - Implement default translation
    return const_cast<clang::DefaultStmt*>(DS);
}

clang::BreakStmt* StatementHandler::translateBreakStmt(
    const clang::BreakStmt* BS,
    HandlerContext& ctx
) {
    // TODO: Task 9 - Implement break translation
    return const_cast<clang::BreakStmt*>(BS);
}

clang::ContinueStmt* StatementHandler::translateContinueStmt(
    const clang::ContinueStmt* CS,
    HandlerContext& ctx
) {
    clang::ASTContext& cContext = ctx.getCContext();
    return new (cContext) clang::ContinueStmt(CS->getContinueLoc());
}

clang::DoStmt* StatementHandler::translateDoStmt(
    const clang::DoStmt* DS,
    HandlerContext& ctx
) {
    // TODO: Task 6 - Implement do-while translation
    return const_cast<clang::DoStmt*>(DS);
}

clang::ForStmt* StatementHandler::translateForStmt(
    const clang::ForStmt* FS,
    HandlerContext& ctx
) {
    // TODO: Task 7 - Implement for loop translation
    return const_cast<clang::ForStmt*>(FS);
}

clang::GotoStmt* StatementHandler::translateGotoStmt(
    const clang::GotoStmt* GS,
    HandlerContext& ctx
) {
    // Goto statements in C and C++ have identical syntax
    // We need to create a new label declaration in the C AST and reference it
    clang::ASTContext& cContext = ctx.getCContext();

    // Get the original label
    const clang::LabelDecl* cppLabel = GS->getLabel();
    if (!cppLabel) {
        return nullptr;
    }

    // Create a new label declaration in C AST with the same name
    clang::IdentifierInfo& II = cContext.Idents.get(cppLabel->getName());
    clang::LabelDecl* cLabel = clang::LabelDecl::Create(
        cContext,
        cContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        &II
    );

    // Create C goto statement
    return new (cContext) clang::GotoStmt(
        cLabel,
        GS->getGotoLoc(),
        GS->getLabelLoc()
    );
}

clang::LabelStmt* StatementHandler::translateLabelStmt(
    const clang::LabelStmt* LS,
    HandlerContext& ctx
) {
    // Label statements in C and C++ have identical syntax
    // We need to create a new label declaration and translate the sub-statement
    clang::ASTContext& cContext = ctx.getCContext();

    // Get the original label declaration
    const clang::LabelDecl* cppDecl = LS->getDecl();
    if (!cppDecl) {
        return nullptr;
    }

    // Create a new label declaration in C AST with the same name
    clang::IdentifierInfo& II = cContext.Idents.get(cppDecl->getName());
    clang::LabelDecl* cDecl = clang::LabelDecl::Create(
        cContext,
        cContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        &II
    );

    // Translate the sub-statement
    const clang::Stmt* subStmt = LS->getSubStmt();
    clang::Stmt* cSubStmt = handleStmt(subStmt, ctx);

    if (!cSubStmt) {
        return nullptr;
    }

    // Create C label statement
    return new (cContext) clang::LabelStmt(
        LS->getIdentLoc(),
        cDecl,
        cSubStmt
    );
}

} // namespace cpptoc
