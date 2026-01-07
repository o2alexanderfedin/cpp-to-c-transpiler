/**
 * @file StatementHandler.cpp
 * @brief Implementation of StatementHandler dispatcher pattern
 *
 * Handles various statement types following the Chain of Responsibility pattern.
 * Dispatches sub-statements and expressions recursively via dispatcher.
 */

#include "dispatch/StatementHandler.h"
#include "mapping/StmtMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/DeclMapper.h"
#include "SourceLocationMapper.h"
#include "TargetContext.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Decl.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>
#include <vector>

namespace cpptoc {

void StatementHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    // Cast to StmtPredicate and StmtVisitor to avoid ambiguity
    dispatcher.addHandler(
        static_cast<CppToCVisitorDispatcher::StmtPredicate>(&StatementHandler::canHandle),
        static_cast<CppToCVisitorDispatcher::StmtVisitor>(&StatementHandler::handleStatement)
    );
}

bool StatementHandler::canHandle(const clang::Stmt* S) {
    assert(S && "Statement must not be null");

    // Handle various statement types EXCEPT ReturnStmt and CompoundStmt
    // (those have dedicated handlers)
    switch (S->getStmtClass()) {
        case clang::Stmt::IfStmtClass:
        case clang::Stmt::WhileStmtClass:
        case clang::Stmt::DoStmtClass:
        case clang::Stmt::ForStmtClass:
        case clang::Stmt::CXXForRangeStmtClass:
        case clang::Stmt::SwitchStmtClass:
        case clang::Stmt::CaseStmtClass:
        case clang::Stmt::DefaultStmtClass:
        case clang::Stmt::BreakStmtClass:
        case clang::Stmt::ContinueStmtClass:
        case clang::Stmt::GotoStmtClass:
        case clang::Stmt::LabelStmtClass:
        case clang::Stmt::DeclStmtClass:
            return true;
        default:
            return false;
    }
}

void StatementHandler::handleStatement(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Stmt* S
) {
    assert(S && "Statement must not be null");
    assert(canHandle(S) && "Statement must be handled by this handler");

    // Get StmtMapper for storing statement mappings
    cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();

    // Check if already processed
    if (stmtMapper.hasCreated(S)) {
        llvm::outs() << "[StatementHandler] Statement already translated, skipping: "
                     << S->getStmtClassName() << "\n";
        return;
    }

    llvm::outs() << "[StatementHandler] Processing statement: " << S->getStmtClassName() << "\n";

    // Get valid SourceLocation for C AST node
    // For statements, we rely on getCurrentTargetPath() since statements
    // don't carry file location information like Decls do
    std::string targetPath = disp.getCurrentTargetPath();
    assert(!targetPath.empty() && "Target path must be set for statement handling");
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Dispatch to appropriate helper based on statement type
    clang::Stmt* cStmt = nullptr;

    switch (S->getStmtClass()) {
        case clang::Stmt::IfStmtClass:
            cStmt = translateIfStmt(llvm::cast<clang::IfStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        case clang::Stmt::WhileStmtClass:
            cStmt = translateWhileStmt(llvm::cast<clang::WhileStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        case clang::Stmt::DoStmtClass:
            cStmt = translateDoStmt(llvm::cast<clang::DoStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        case clang::Stmt::ForStmtClass:
            cStmt = translateForStmt(llvm::cast<clang::ForStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        case clang::Stmt::CXXForRangeStmtClass:
            cStmt = translateCXXForRangeStmt(llvm::cast<clang::CXXForRangeStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        case clang::Stmt::SwitchStmtClass:
            cStmt = translateSwitchStmt(llvm::cast<clang::SwitchStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        case clang::Stmt::CaseStmtClass:
            cStmt = translateCaseStmt(llvm::cast<clang::CaseStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        case clang::Stmt::DefaultStmtClass:
            cStmt = translateDefaultStmt(llvm::cast<clang::DefaultStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        case clang::Stmt::BreakStmtClass:
            cStmt = translateBreakStmt(llvm::cast<clang::BreakStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        case clang::Stmt::ContinueStmtClass:
            cStmt = translateContinueStmt(llvm::cast<clang::ContinueStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        case clang::Stmt::GotoStmtClass:
            cStmt = translateGotoStmt(llvm::cast<clang::GotoStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        case clang::Stmt::LabelStmtClass:
            cStmt = translateLabelStmt(llvm::cast<clang::LabelStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        case clang::Stmt::DeclStmtClass:
            cStmt = translateDeclStmt(llvm::cast<clang::DeclStmt>(S), disp, cppASTContext, cASTContext, targetLoc);
            break;

        default:
            llvm::errs() << "[StatementHandler] ERROR: Unhandled statement type: "
                         << S->getStmtClassName() << "\n";
            assert(false && "Statement type should be handled by canHandle()");
            return;
    }

    if (!cStmt) {
        llvm::errs() << "[StatementHandler] ERROR: Failed to translate statement: "
                     << S->getStmtClassName() << "\n";
        assert(false && "Statement translation should not return nullptr");
        return;
    }

    // Store mapping in StmtMapper
    stmtMapper.setCreated(S, cStmt);

    llvm::outs() << "[StatementHandler] Statement translation complete and stored in StmtMapper: "
                 << cStmt->getStmtClassName() << "\n";
}

// Helper functions for specific statement types

clang::IfStmt* StatementHandler::translateIfStmt(
    const clang::IfStmt* IS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating IfStmt\n";

    // Translate condition expression
    const clang::Expr* cppCond = IS->getCond();
    clang::Expr* cCond = nullptr;

    if (cppCond) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppCond));
        if (handled) {
            cCond = disp.getExprMapper().getCreated(cppCond);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Condition expression not handled\n";
            cCond = const_cast<clang::Expr*>(cppCond); // Fallback
        }
    }

    // Translate then branch
    const clang::Stmt* cppThen = IS->getThen();
    clang::Stmt* cThen = nullptr;

    if (cppThen) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppThen));
        if (handled) {
            cThen = disp.getStmtMapper().getCreated(cppThen);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Then branch not handled\n";
        }
    }

    // Translate else branch (if present)
    clang::Stmt* cElse = nullptr;
    const clang::Stmt* cppElse = IS->getElse();

    if (cppElse) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppElse));
        if (handled) {
            cElse = disp.getStmtMapper().getCreated(cppElse);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Else branch not handled\n";
        }
    }

    // Create C if statement
    return clang::IfStmt::Create(
        cASTContext,
        IS->getIfLoc(),
        clang::IfStatementKind::Ordinary,
        nullptr, // init (C++17)
        nullptr, // condVar
        cCond,
        targetLoc,
        targetLoc,
        cThen,
        cppElse ? IS->getElseLoc() : targetLoc,
        cElse
    );
}

clang::WhileStmt* StatementHandler::translateWhileStmt(
    const clang::WhileStmt* WS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating WhileStmt\n";

    // Translate condition
    const clang::Expr* cppCond = WS->getCond();
    clang::Expr* cCond = nullptr;

    if (cppCond) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppCond));
        if (handled) {
            cCond = disp.getExprMapper().getCreated(cppCond);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Condition expression not handled\n";
            cCond = const_cast<clang::Expr*>(cppCond); // Fallback
        }
    }

    // Translate body
    const clang::Stmt* cppBody = WS->getBody();
    clang::Stmt* cBody = nullptr;

    if (cppBody) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppBody));
        if (handled) {
            cBody = disp.getStmtMapper().getCreated(cppBody);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Body not handled\n";
        }
    }

    // Create C while statement
    return clang::WhileStmt::Create(
        cASTContext,
        nullptr, // ConditionVariable
        cCond,
        cBody,
        WS->getWhileLoc(),
        targetLoc, // LParenLoc
        targetLoc  // RParenLoc
    );
}

clang::DoStmt* StatementHandler::translateDoStmt(
    const clang::DoStmt* DS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating DoStmt\n";

    // Translate body
    const clang::Stmt* cppBody = DS->getBody();
    clang::Stmt* cBody = nullptr;

    if (cppBody) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppBody));
        if (handled) {
            cBody = disp.getStmtMapper().getCreated(cppBody);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Body not handled\n";
        }
    }

    // Translate condition
    const clang::Expr* cppCond = DS->getCond();
    clang::Expr* cCond = nullptr;

    if (cppCond) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppCond));
        if (handled) {
            cCond = disp.getExprMapper().getCreated(cppCond);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Condition expression not handled\n";
            cCond = const_cast<clang::Expr*>(cppCond); // Fallback
        }
    }

    // Create C do-while statement
    return new (cASTContext) clang::DoStmt(
        cBody,
        cCond,
        DS->getDoLoc(),
        DS->getWhileLoc(),
        DS->getRParenLoc()
    );
}

clang::ForStmt* StatementHandler::translateForStmt(
    const clang::ForStmt* FS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating ForStmt\n";

    // Translate init statement
    const clang::Stmt* cppInit = FS->getInit();
    clang::Stmt* cInit = nullptr;

    if (cppInit) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppInit));
        if (handled) {
            cInit = disp.getStmtMapper().getCreated(cppInit);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Init statement not handled\n";
        }
    }

    // Translate condition
    const clang::Expr* cppCond = FS->getCond();
    clang::Expr* cCond = nullptr;

    if (cppCond) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppCond));
        if (handled) {
            cCond = disp.getExprMapper().getCreated(cppCond);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Condition expression not handled\n";
            cCond = const_cast<clang::Expr*>(cppCond); // Fallback
        }
    }

    // Translate increment
    const clang::Expr* cppInc = FS->getInc();
    clang::Expr* cInc = nullptr;

    if (cppInc) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppInc));
        if (handled) {
            cInc = disp.getExprMapper().getCreated(cppInc);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Increment expression not handled\n";
            cInc = const_cast<clang::Expr*>(cppInc); // Fallback
        }
    }

    // Translate body
    const clang::Stmt* cppBody = FS->getBody();
    clang::Stmt* cBody = nullptr;

    if (cppBody) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppBody));
        if (handled) {
            cBody = disp.getStmtMapper().getCreated(cppBody);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Body not handled\n";
        }
    }

    // Create C for statement
    return new (cASTContext) clang::ForStmt(
        cASTContext,
        cInit,
        cCond,
        nullptr, // ConditionVariable
        cInc,
        cBody,
        FS->getForLoc(),
        FS->getLParenLoc(),
        FS->getRParenLoc()
    );
}

clang::ForStmt* StatementHandler::translateCXXForRangeStmt(
    const clang::CXXForRangeStmt* RFS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating CXXForRangeStmt (simplified - full implementation needed)\n";

    // TODO: Full range-based for loop translation
    // For now, return nullptr to indicate not supported
    // This needs RangeTypeAnalyzer, LoopVariableAnalyzer, etc.
    llvm::errs() << "[StatementHandler] WARNING: CXXForRangeStmt translation not fully implemented\n";

    return nullptr;
}

clang::SwitchStmt* StatementHandler::translateSwitchStmt(
    const clang::SwitchStmt* SS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating SwitchStmt\n";

    // Translate condition expression
    const clang::Expr* cppCond = SS->getCond();
    clang::Expr* cCond = nullptr;

    if (cppCond) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppCond));
        if (handled) {
            cCond = disp.getExprMapper().getCreated(cppCond);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Condition expression not handled\n";
            cCond = const_cast<clang::Expr*>(cppCond); // Fallback
        }
    }

    // Translate body
    const clang::Stmt* cppBody = SS->getBody();
    clang::Stmt* cBody = nullptr;

    if (cppBody) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppBody));
        if (handled) {
            cBody = disp.getStmtMapper().getCreated(cppBody);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Body not handled\n";
        }
    }

    // Create C switch statement
    clang::SwitchStmt* cSwitch = clang::SwitchStmt::Create(
        cASTContext,
        nullptr,  // No init statement (C99 doesn't support this)
        nullptr,  // No condition variable
        cCond,
        SS->getLParenLoc(),
        SS->getRParenLoc()
    );

    // Set body
    if (cBody) {
        cSwitch->setBody(cBody);
    }

    return cSwitch;
}

clang::CaseStmt* StatementHandler::translateCaseStmt(
    const clang::CaseStmt* CS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating CaseStmt\n";

    // Translate case value expression
    const clang::Expr* cppLHS = CS->getLHS();
    clang::Expr* cLHS = nullptr;

    if (cppLHS) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppLHS));
        if (handled) {
            cLHS = disp.getExprMapper().getCreated(cppLHS);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Case value expression not handled\n";
            cLHS = const_cast<clang::Expr*>(cppLHS); // Fallback
        }
    }

    // Handle RHS for case ranges (GNU extension, rare)
    const clang::Expr* cppRHS = CS->getRHS();
    clang::Expr* cRHS = nullptr;

    if (cppRHS) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Expr*>(cppRHS));
        if (handled) {
            cRHS = disp.getExprMapper().getCreated(cppRHS);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Case RHS expression not handled\n";
            cRHS = const_cast<clang::Expr*>(cppRHS); // Fallback
        }
    }

    // Translate sub-statement
    const clang::Stmt* cppSubStmt = CS->getSubStmt();
    clang::Stmt* cSubStmt = nullptr;

    if (cppSubStmt) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppSubStmt));
        if (handled) {
            cSubStmt = disp.getStmtMapper().getCreated(cppSubStmt);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Sub-statement not handled\n";
        }
    }

    // Create C case statement
    clang::CaseStmt* cCase = clang::CaseStmt::Create(
        cASTContext,
        cLHS,
        cRHS,
        CS->getCaseLoc(),
        CS->getEllipsisLoc(),
        CS->getColonLoc()
    );

    // Set sub-statement
    if (cSubStmt) {
        cCase->setSubStmt(cSubStmt);
    }

    return cCase;
}

clang::DefaultStmt* StatementHandler::translateDefaultStmt(
    const clang::DefaultStmt* DS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating DefaultStmt\n";

    // Translate sub-statement
    const clang::Stmt* cppSubStmt = DS->getSubStmt();
    clang::Stmt* cSubStmt = nullptr;

    if (cppSubStmt) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppSubStmt));
        if (handled) {
            cSubStmt = disp.getStmtMapper().getCreated(cppSubStmt);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Sub-statement not handled\n";
        }
    }

    // Create C default statement
    return new (cASTContext) clang::DefaultStmt(
        DS->getDefaultLoc(),
        DS->getColonLoc(),
        cSubStmt
    );
}

clang::BreakStmt* StatementHandler::translateBreakStmt(
    const clang::BreakStmt* BS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating BreakStmt\n";

    // Break statements are identical in C and C++
    return new (cASTContext) clang::BreakStmt(BS->getBreakLoc());
}

clang::ContinueStmt* StatementHandler::translateContinueStmt(
    const clang::ContinueStmt* CS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating ContinueStmt\n";

    // Continue statements are identical in C and C++
    return new (cASTContext) clang::ContinueStmt(CS->getContinueLoc());
}

clang::GotoStmt* StatementHandler::translateGotoStmt(
    const clang::GotoStmt* GS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating GotoStmt\n";

    // Get the original label
    const clang::LabelDecl* cppLabel = GS->getLabel();
    if (!cppLabel) {
        return nullptr;
    }

    // Create a new label declaration in C AST with the same name
    clang::IdentifierInfo& II = cASTContext.Idents.get(cppLabel->getName());
    clang::LabelDecl* cLabel = clang::LabelDecl::Create(
        cASTContext,
        cASTContext.getTranslationUnitDecl(),
        targetLoc,
        &II
    );

    // Create C goto statement
    return new (cASTContext) clang::GotoStmt(
        cLabel,
        GS->getGotoLoc(),
        GS->getLabelLoc()
    );
}

clang::LabelStmt* StatementHandler::translateLabelStmt(
    const clang::LabelStmt* LS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating LabelStmt\n";

    // Get the original label declaration
    const clang::LabelDecl* cppDecl = LS->getDecl();
    if (!cppDecl) {
        return nullptr;
    }

    // Create a new label declaration in C AST with the same name
    clang::IdentifierInfo& II = cASTContext.Idents.get(cppDecl->getName());
    clang::LabelDecl* cDecl = clang::LabelDecl::Create(
        cASTContext,
        cASTContext.getTranslationUnitDecl(),
        targetLoc,
        &II
    );

    // Translate the sub-statement
    const clang::Stmt* cppSubStmt = LS->getSubStmt();
    clang::Stmt* cSubStmt = nullptr;

    if (cppSubStmt) {
        bool handled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppSubStmt));
        if (handled) {
            cSubStmt = disp.getStmtMapper().getCreated(cppSubStmt);
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Sub-statement not handled\n";
        }
    }

    if (!cSubStmt) {
        return nullptr;
    }

    // Create C label statement
    return new (cASTContext) clang::LabelStmt(
        LS->getIdentLoc(),
        cDecl,
        cSubStmt
    );
}

clang::Stmt* StatementHandler::translateDeclStmt(
    const clang::DeclStmt* DS,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    clang::SourceLocation targetLoc
) {
    llvm::outs() << "[StatementHandler] Translating DeclStmt\n";

    // TODO: Full DeclStmt translation with object construction/destruction
    // For now, simplified implementation

    std::vector<clang::Decl*> cDecls;

    for (auto* cppDecl : DS->decls()) {
        // Dispatch declaration via dispatcher
        bool handled = disp.dispatch(cppASTContext, cASTContext, cppDecl);

        if (handled) {
            clang::Decl* cDecl = disp.getDeclMapper().getCreated(cppDecl);
            if (cDecl) {
                cDecls.push_back(cDecl);
            }
        } else {
            llvm::errs() << "[StatementHandler] WARNING: Declaration not handled: "
                         << cppDecl->getDeclKindName() << "\n";
        }
    }

    if (cDecls.empty()) {
        llvm::errs() << "[StatementHandler] WARNING: No declarations translated in DeclStmt\n";
        return nullptr;
    }

    // Create C DeclStmt
    return new (cASTContext) clang::DeclStmt(
        clang::DeclGroupRef::Create(cASTContext, cDecls.data(), cDecls.size()),
        targetLoc,
        targetLoc
    );
}

} // namespace cpptoc
