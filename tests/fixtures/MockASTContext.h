/**
 * @file MockASTContext.h
 * @brief Mock AST Context for creating test C++ AST nodes
 *
 * This fixture provides a simplified API for creating C++ AST nodes
 * programmatically for testing purposes. It manages AST contexts and
 * owns all created nodes.
 *
 * Design Principles:
 * - Single Responsibility: Only creates C++ AST nodes for testing
 * - Dependency Inversion: Handlers depend on abstractions, not concrete types
 * - KISS: Simple API for common test scenarios
 */

#pragma once

#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Type.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Basic/TargetOptions.h"
#include <memory>
#include <string>
#include <vector>

namespace cpptoc {
namespace test {

/**
 * @class MockASTContext
 * @brief Test fixture for creating C++ AST nodes
 *
 * Provides a clean API for constructing C++ AST nodes without
 * boilerplate. All nodes are owned by the AST context.
 */
class MockASTContext {
private:
    /// Owned AST context for C++ nodes
    std::unique_ptr<clang::ASTContext> context_;

    /// Target information for AST context
    std::shared_ptr<clang::TargetOptions> targetOptions_;
    clang::TargetInfo* targetInfo_;

    /// Owned declarations (for lifetime management)
    std::vector<std::unique_ptr<clang::Decl>> ownedDecls_;

    /// Owned statements (for lifetime management)
    std::vector<std::unique_ptr<clang::Stmt>> ownedStmts_;

    /**
     * @brief Parse type from string representation
     * @param typeStr Type string (e.g., "int", "float", "void")
     * @return QualType
     */
    clang::QualType parseType(const std::string& typeStr);

    /**
     * @brief Create parameter from string "type name"
     * @param paramStr Parameter string (e.g., "int x")
     * @return ParmVarDecl*
     */
    clang::ParmVarDecl* createParameter(const std::string& paramStr);

public:
    /**
     * @brief Construct MockASTContext with default target
     */
    MockASTContext();

    /**
     * @brief Destructor - cleans up AST context
     */
    ~MockASTContext();

    /**
     * @brief Get the underlying AST context
     * @return Reference to ASTContext
     */
    clang::ASTContext& getContext() { return *context_; }

    // ========================================================================
    // C++ AST Node Creation Methods
    // ========================================================================

    /**
     * @brief Create a simple function declaration
     * @param returnType Return type as string (e.g., "int", "void")
     * @param name Function name
     * @param params Parameter declarations as strings (e.g., {"int a", "float b"})
     * @param body Optional function body (nullptr for declaration only)
     * @return FunctionDecl* (owned by MockASTContext)
     *
     * Example:
     * @code
     *   auto* func = mock.createFunction("int", "add", {"int a", "int b"}, body);
     * @endcode
     */
    clang::FunctionDecl* createFunction(
        const std::string& returnType,
        const std::string& name,
        const std::vector<std::string>& params = {},
        clang::Stmt* body = nullptr
    );

    /**
     * @brief Create a variable declaration
     * @param type Variable type as string
     * @param name Variable name
     * @param init Optional initializer expression
     * @return VarDecl*
     *
     * Example:
     * @code
     *   auto* var = mock.createVariable("int", "x", mock.createIntLiteral(42));
     * @endcode
     */
    clang::VarDecl* createVariable(
        const std::string& type,
        const std::string& name,
        clang::Expr* init = nullptr
    );

    /**
     * @brief Create an integer literal
     * @param value Integer value
     * @return IntegerLiteral*
     *
     * Example:
     * @code
     *   auto* lit = mock.createIntLiteral(42);
     * @endcode
     */
    clang::IntegerLiteral* createIntLiteral(int value);

    /**
     * @brief Create a floating-point literal
     * @param value Float value
     * @return FloatingLiteral*
     *
     * Example:
     * @code
     *   auto* lit = mock.createFloatLiteral(3.14);
     * @endcode
     */
    clang::FloatingLiteral* createFloatLiteral(double value);

    /**
     * @brief Create a binary operator expression
     * @param op Operator kind (BO_Add, BO_Sub, etc.)
     * @param lhs Left-hand side expression
     * @param rhs Right-hand side expression
     * @return BinaryOperator*
     *
     * Example:
     * @code
     *   auto* add = mock.createBinaryOp(clang::BO_Add, lhs, rhs);
     * @endcode
     */
    clang::BinaryOperator* createBinaryOp(
        clang::BinaryOperatorKind op,
        clang::Expr* lhs,
        clang::Expr* rhs
    );

    /**
     * @brief Create a variable reference expression
     * @param var Variable declaration to reference
     * @return DeclRefExpr*
     *
     * Example:
     * @code
     *   auto* ref = mock.createVarRef(varDecl);
     * @endcode
     */
    clang::DeclRefExpr* createVarRef(clang::VarDecl* var);

    /**
     * @brief Create a return statement
     * @param expr Optional return expression (nullptr for void return)
     * @return ReturnStmt*
     *
     * Example:
     * @code
     *   auto* ret = mock.createReturnStmt(expr);
     * @endcode
     */
    clang::ReturnStmt* createReturnStmt(clang::Expr* expr = nullptr);

    /**
     * @brief Create a compound statement (block)
     * @param stmts Statements in block
     * @return CompoundStmt*
     *
     * Example:
     * @code
     *   auto* block = mock.createCompoundStmt({stmt1, stmt2});
     * @endcode
     */
    clang::CompoundStmt* createCompoundStmt(const std::vector<clang::Stmt*>& stmts);
};

} // namespace test
} // namespace cpptoc
