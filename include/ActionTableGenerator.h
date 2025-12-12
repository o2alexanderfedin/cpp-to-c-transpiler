// ActionTableGenerator.h - Action table generation from CFG analysis
// Story #77: Implement Action Table Generation from CFG Analysis
// SOLID Principles:
//   - Single Responsibility: Generates action tables for exception handling
//   - Open/Closed: Extensible for different exception handling patterns
//   - Dependency Inversion: Depends on Clang AST abstractions

#ifndef ACTION_TABLE_GENERATOR_H
#define ACTION_TABLE_GENERATOR_H

#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"
#include <string>
#include <vector>

namespace clang {

/// @brief Represents a single try block with its constructed objects
struct TryBlockInfo {
    CXXTryStmt *tryStmt;                    // AST node for try statement
    std::vector<VarDecl*> constructedObjects; // Objects constructed in try block (in order)
    int tryBlockIndex;                      // Unique index for this try block
};

/// @brief Generates action tables for exception handling unwinding
///
/// This class analyzes try blocks to identify constructed objects and generates
/// action tables listing destructors in reverse construction order. Action tables
/// are used during stack unwinding to properly destroy objects.
class ActionTableGenerator {
public:
    ActionTableGenerator() = default;

    /// @brief Analyze function for try blocks and constructed objects
    /// @param FD Function declaration to analyze
    void analyzeTryBlocks(FunctionDecl *FD);

    /// @brief Get number of try blocks found
    /// @return Count of try blocks in analyzed function
    int getTryBlockCount() const { return tryBlocks.size(); }

    /// @brief Get number of objects constructed in specific try block
    /// @param tryBlockIndex Index of try block
    /// @return Count of objects constructed in that try block
    int getObjectCount(int tryBlockIndex) const;

    /// @brief Get destructor sequence for a try block (in reverse construction order)
    /// @param tryBlockIndex Index of try block
    /// @return Vector of destructor names in destruction order
    std::vector<std::string> getDestructorSequence(int tryBlockIndex) const;

    /// @brief Generate action table code for a specific try block
    /// @param tryBlockIndex Index of try block
    /// @return C code defining static action table array
    std::string generateActionTable(int tryBlockIndex) const;

    /// @brief Generate runtime binding code to set object addresses
    /// @param tryBlockIndex Index of try block
    /// @return C code that assigns object addresses to action table entries
    std::string generateRuntimeBinding(int tryBlockIndex) const;

    /// @brief Get all try blocks found during analysis
    /// @return Vector of try block information
    const std::vector<TryBlockInfo>& getTryBlocks() const { return tryBlocks; }

private:
    std::vector<TryBlockInfo> tryBlocks;   // All try blocks in function

    /// @brief Find try statements in a statement tree
    /// @param S Statement to search
    /// @param tryStmts Output vector for found try statements
    void findTryStatements(Stmt *S, std::vector<CXXTryStmt*>& tryStmts);

    /// @brief Find constructed objects within a try block scope
    /// @param tryStmt Try statement to analyze
    /// @return Vector of variable declarations with constructors
    std::vector<VarDecl*> findConstructedObjects(CXXTryStmt *tryStmt);

    /// @brief Get destructor function name for a class type
    /// @param classDecl Class declaration
    /// @return Mangled destructor function name
    std::string getDestructorName(const CXXRecordDecl *classDecl) const;

    /// @brief Get variable name from declaration
    /// @param varDecl Variable declaration
    /// @return Variable name as string
    std::string getVariableName(const VarDecl *varDecl) const;
};

} // namespace clang

#endif // ACTION_TABLE_GENERATOR_H
