// src/CFGAnalyzer.cpp
// Story #151: CFG Analysis Infrastructure
// Implementation of CFG analyzer for RAII destructor injection
//
// SOLID Principles Applied:
// - Single Responsibility: Each method analyzes one aspect of CFG
// - Open/Closed: Can extend with new analysis methods without modifying existing code
// - Interface Segregation: Clean, focused public interface
// - Dependency Inversion: Depends on Clang CFG abstractions

#include "CFGAnalyzer.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Stmt.h"

using namespace clang;

void CFGAnalyzer::analyzeCFG(FunctionDecl *FD) {
    // Early return if function is invalid or has no body (KISS principle)
    if (!FD || !FD->hasBody()) {
        return;
    }

    // Build CFG with implicit destructors enabled
    // This is essential for RAII analysis as it shows where destructors would be called
    CFG::BuildOptions options;
    options.AddImplicitDtors = true;

    cfg = CFG::buildCFG(FD, FD->getBody(), &FD->getASTContext(), options);

    // If CFG construction fails, we cannot proceed with analysis
    if (!cfg) {
        return;
    }

    // Perform all analysis passes
    // Order doesn't matter as each pass is independent (Single Responsibility)
    findExitPoints();
    findLocalVars(FD);
    findScopes(FD);
    findBreakContinue(FD);
    findGoto(FD);
}

void CFGAnalyzer::findExitPoints() {
    if (!cfg) {
        return;
    }

    // Iterate through all CFG blocks looking for return statements
    // In Clang CFG, return statements appear as elements within blocks, not as terminators
    for (auto *Block : *cfg) {
        if (!Block) continue;

        // Check each statement in the block
        for (auto I = Block->begin(), E = Block->end(); I != E; ++I) {
            if (I->getKind() == CFGElement::Statement) {
                const Stmt *S = I->castAs<CFGStmt>().getStmt();
                if (llvm::isa<ReturnStmt>(S)) {
                    exitPoints.push_back(Block);
                    break; // Only count block once even if it has multiple returns
                }
            }
        }
    }
}

void CFGAnalyzer::findLocalVars(FunctionDecl *FD) {
    // Use RecursiveASTVisitor to find all local variable declarations
    class VarFinder : public RecursiveASTVisitor<VarFinder> {
    public:
        std::vector<VarDecl*> &vars;
        VarFinder(std::vector<VarDecl*> &v) : vars(v) {}

        bool VisitVarDecl(VarDecl *VD) {
            if (VD->isLocalVarDecl()) {
                vars.push_back(VD);
            }
            return true;
        }
    };

    VarFinder finder(localVars);
    finder.TraverseStmt(FD->getBody());
}

void CFGAnalyzer::findScopes(FunctionDecl *FD) {
    // Use RecursiveASTVisitor to find all compound statements (scopes)
    class ScopeFinder : public RecursiveASTVisitor<ScopeFinder> {
    public:
        std::vector<CompoundStmt*> &scopes;
        ScopeFinder(std::vector<CompoundStmt*> &s) : scopes(s) {}

        bool VisitCompoundStmt(CompoundStmt *CS) {
            scopes.push_back(CS);
            return true;
        }
    };

    ScopeFinder finder(scopes);
    finder.TraverseStmt(FD->getBody());
}

void CFGAnalyzer::findBreakContinue(FunctionDecl *FD) {
    // Use RecursiveASTVisitor to find break and continue statements
    class BreakContinueFinder : public RecursiveASTVisitor<BreakContinueFinder> {
    public:
        std::vector<Stmt*> &stmts;
        BreakContinueFinder(std::vector<Stmt*> &s) : stmts(s) {}

        bool VisitBreakStmt(BreakStmt *BS) {
            stmts.push_back(BS);
            return true;
        }

        bool VisitContinueStmt(ContinueStmt *CS) {
            stmts.push_back(CS);
            return true;
        }
    };

    BreakContinueFinder finder(breakContinueStmts);
    finder.TraverseStmt(FD->getBody());
}

void CFGAnalyzer::findGoto(FunctionDecl *FD) {
    // Use RecursiveASTVisitor to find goto statements
    class GotoFinder : public RecursiveASTVisitor<GotoFinder> {
    public:
        std::vector<GotoStmt*> &gotos;
        GotoFinder(std::vector<GotoStmt*> &g) : gotos(g) {}

        bool VisitGotoStmt(GotoStmt *GS) {
            gotos.push_back(GS);
            return true;
        }
    };

    GotoFinder finder(gotoStmts);
    finder.TraverseStmt(FD->getBody());
}
