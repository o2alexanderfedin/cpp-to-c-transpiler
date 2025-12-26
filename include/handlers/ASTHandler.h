/**
 * @file ASTHandler.h
 * @brief Base interface for all AST translation handlers
 *
 * This file defines the core handler interface for the Chain of Responsibility
 * pattern used in Stage 2 (C++ AST → C AST translation).
 *
 * Design Principles:
 * - Single Responsibility: Each handler translates ONE C++ construct
 * - Open/Closed: New handlers can be added without modifying existing ones
 * - Liskov Substitution: All handlers can be used interchangeably
 * - Interface Segregation: Only implement methods relevant to handler type
 * - Dependency Inversion: Depend on HandlerContext abstraction
 */

#pragma once

#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"

namespace cpptoc {

// Forward declaration
class HandlerContext;

/**
 * @class ASTHandler
 * @brief Abstract base class for all C++ AST to C AST translation handlers
 *
 * Each handler is responsible for translating a specific C++ construct.
 * Handlers are registered with HandlerRegistry and dispatched by
 * TranslationOrchestrator.
 *
 * Handler Lifecycle:
 * 1. Orchestrator calls canHandle() to check if handler processes this node
 * 2. If true, orchestrator calls appropriate handle method
 * 3. Handler creates C AST nodes using HandlerContext.getBuilder()
 * 4. Handler registers mapping in context
 * 5. Handler returns C AST node
 */
class ASTHandler {
public:
    virtual ~ASTHandler() = default;

    /**
     * @brief Check if this handler can process the given declaration
     * @param D C++ declaration to check
     * @return true if handler can process this declaration
     *
     * Example:
     * @code
     *   bool FunctionHandler::canHandle(const Decl* D) const {
     *       return llvm::isa<clang::FunctionDecl>(D);
     *   }
     * @endcode
     */
    virtual bool canHandle(const clang::Decl* D) const { return false; }

    /**
     * @brief Check if this handler can process the given statement
     * @param S C++ statement to check
     * @return true if handler can process this statement
     */
    virtual bool canHandle(const clang::Stmt* S) const { return false; }

    /**
     * @brief Check if this handler can process the given expression
     * @param E C++ expression to check
     * @return true if handler can process this expression
     */
    virtual bool canHandle(const clang::Expr* E) const { return false; }

    /**
     * @brief Translate C++ declaration to C declaration
     * @param D C++ declaration to translate
     * @param ctx Shared context for symbol tables, type mappings, state
     * @return Translated C declaration, or nullptr if cannot translate
     *
     * The handler should:
     * 1. Cast D to specific declaration type (e.g., FunctionDecl)
     * 2. Use ctx to lookup/translate types
     * 3. Use ctx.getBuilder() to create C AST nodes
     * 4. Register mapping in ctx (ctx.registerDecl)
     * 5. Return created C declaration
     *
     * Example:
     * @code
     *   Decl* FunctionHandler::handleDecl(const Decl* D, HandlerContext& ctx) {
     *       auto* FD = llvm::cast<FunctionDecl>(D);
     *       // ... translation logic ...
     *       ctx.registerDecl(FD, cFunc);
     *       return cFunc;
     *   }
     * @endcode
     */
    virtual clang::Decl* handleDecl(const clang::Decl* D, HandlerContext& ctx) {
        return nullptr;
    }

    /**
     * @brief Translate C++ statement to C statement
     * @param S C++ statement to translate
     * @param ctx Shared context for symbol tables, type mappings, state
     * @return Translated C statement, or nullptr if cannot translate
     */
    virtual clang::Stmt* handleStmt(const clang::Stmt* S, HandlerContext& ctx) {
        return nullptr;
    }

    /**
     * @brief Translate C++ expression to C expression
     * @param E C++ expression to translate
     * @param ctx Shared context for symbol tables, type mappings, state
     * @return Translated C expression, or nullptr if cannot translate
     */
    virtual clang::Expr* handleExpr(const clang::Expr* E, HandlerContext& ctx) {
        return nullptr;
    }
};

} // namespace cpptoc
