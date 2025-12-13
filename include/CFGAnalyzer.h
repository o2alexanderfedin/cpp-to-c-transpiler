// include/CFGAnalyzer.h
// Story #151: CFG (Control Flow Graph) Analysis Infrastructure
// Analyzes Clang CFG to identify scope exit points for destructor injection

#ifndef CFGANALYZER_H
#define CFGANALYZER_H

#include "clang/AST/Decl.h"
#include "clang/Analysis/CFG.h"
#include <memory>
#include <vector>

namespace clang {

/**
 * @brief Analyzes control flow graphs to identify destructor injection points
 *
 * This class uses Clang's CFG API to analyze function control flow and identify:
 * - Exit points (return statements, end of function)
 * - Control flow statements (goto, break, continue)
 * - Local variable declarations with destructors
 * - Nested scopes requiring cleanup
 *
 * Used by CppToCVisitor to determine where to inject destructor calls for RAII.
 */
class CFGAnalyzer {
public:
    CFGAnalyzer() = default;

    /**
     * @brief Analyze CFG for a function declaration
     * @param FD Function to analyze
     */
    void analyzeCFG(FunctionDecl *FD);

    /**
     * @brief Get number of exit points detected
     * Exit points are locations where destructors must be injected
     * @return Count of exit points (return statements, end of function)
     */
    int getExitPointCount() const { return exitPoints.size(); }

    /**
     * @brief Get number of local variables detected
     * @return Count of local variable declarations
     */
    int getLocalVarCount() const { return localVars.size(); }

    /**
     * @brief Get number of scopes detected
     * @return Count of compound statements (scopes)
     */
    int getScopeCount() const { return scopes.size(); }

    /**
     * @brief Get number of break/continue statements detected
     * @return Count of break and continue statements
     */
    int getBreakContinueCount() const { return breakContinueStmts.size(); }

    /**
     * @brief Get number of goto statements detected
     * @return Count of goto statements
     */
    int getGotoCount() const { return gotoStmts.size(); }

    /**
     * @brief Get exit points (CFG blocks with terminators)
     * @return Vector of CFG blocks representing exit points
     */
    const std::vector<CFGBlock*>& getExitPoints() const { return exitPoints; }

    /**
     * @brief Get local variables in function
     * @return Vector of variable declarations
     */
    const std::vector<VarDecl*>& getLocalVars() const { return localVars; }

    /**
     * @brief Get scopes (compound statements) in function
     * @return Vector of compound statements
     */
    const std::vector<CompoundStmt*>& getScopes() const { return scopes; }

    /**
     * @brief Get the constructed CFG
     * @return Pointer to CFG, or nullptr if not built yet
     */
    CFG* getCFG() const { return cfg.get(); }

private:
    std::unique_ptr<CFG> cfg;                       // Control flow graph
    std::vector<CFGBlock*> exitPoints;              // Return statements, function end
    std::vector<VarDecl*> localVars;                // Local variable declarations
    std::vector<CompoundStmt*> scopes;              // Nested scopes
    std::vector<Stmt*> breakContinueStmts;          // Break/continue statements
    std::vector<GotoStmt*> gotoStmts;               // Goto statements

    /**
     * @brief Find all exit points in CFG
     * Populates exitPoints vector with return statements and implicit exits
     */
    void findExitPoints();

    /**
     * @brief Find all local variables in function
     * @param FD Function to scan for variable declarations
     */
    void findLocalVars(FunctionDecl *FD);

    /**
     * @brief Find all scopes (compound statements) in function
     * @param FD Function to scan for compound statements
     */
    void findScopes(FunctionDecl *FD);

    /**
     * @brief Find all break/continue statements in function
     * @param FD Function to scan for break/continue
     */
    void findBreakContinue(FunctionDecl *FD);

    /**
     * @brief Find all goto statements in function
     * @param FD Function to scan for goto statements
     */
    void findGoto(FunctionDecl *FD);
};

} // namespace clang

#endif // CFGANALYZER_H
