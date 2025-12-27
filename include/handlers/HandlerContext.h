/**
 * @file HandlerContext.h
 * @brief Shared context passed between handlers during translation
 *
 * HandlerContext provides shared state and services to all handlers:
 * - Symbol tables (C++ decl → C decl mappings)
 * - Type translation cache
 * - Current translation state
 * - Access to CNodeBuilder for C AST creation
 *
 * Design Principles:
 * - Dependency Inversion: Handlers depend on this abstraction
 * - Single Responsibility: Manages shared translation state only
 * - Testable: Can create mock contexts for unit tests
 */

#pragma once

#include "CNodeBuilder.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Type.h"
#include <map>
#include <vector>

namespace cpptoc {

/**
 * @class HandlerContext
 * @brief Shared context passed between handlers during translation
 *
 * Provides:
 * - Symbol table for tracking C++ → C declaration mappings
 * - Type translation and caching
 * - Access to CNodeBuilder for C AST creation
 *
 * Thread safety: Not thread-safe (single-threaded translation)
 */
class HandlerContext {
private:
    /// C++ AST Context (input)
    clang::ASTContext& cppContext_;

    /// C AST Context (output)
    clang::ASTContext& cContext_;

    /// C AST node builder
    clang::CNodeBuilder& builder_;

    /// Symbol table: C++ declaration → C declaration
    std::map<const clang::Decl*, clang::Decl*> declMap_;

    /// Type translation cache: C++ type → C type
    std::map<clang::QualType, clang::QualType> typeMap_;

    /// Current function being translated (for context-dependent translations)
    clang::FunctionDecl* currentFunction_ = nullptr;

    /// Function context stack (for nested function translations)
    std::vector<clang::FunctionDecl*> functionStack_;

    /// Method-to-function mapping (C++ method → C function)
    std::map<const clang::CXXMethodDecl*, clang::FunctionDecl*> methodMap_;

public:
    /**
     * @brief Construct handler context
     * @param cppCtx C++ ASTContext (input)
     * @param cCtx C ASTContext (output)
     * @param builder CNodeBuilder for creating C nodes
     */
    HandlerContext(
        clang::ASTContext& cppCtx,
        clang::ASTContext& cCtx,
        clang::CNodeBuilder& builder
    );

    /**
     * @brief Destructor
     */
    ~HandlerContext();

    // ========================================================================
    // AST Context Access
    // ========================================================================

    /**
     * @brief Get C++ AST context
     * @return Reference to C++ ASTContext
     */
    clang::ASTContext& getCppContext() { return cppContext_; }

    /**
     * @brief Get C AST context
     * @return Reference to C ASTContext
     */
    clang::ASTContext& getCContext() { return cContext_; }

    /**
     * @brief Get C node builder
     * @return Reference to CNodeBuilder
     */
    clang::CNodeBuilder& getBuilder() { return builder_; }

    // ========================================================================
    // Symbol Registration and Lookup
    // ========================================================================

    /**
     * @brief Register C++ declaration → C declaration mapping
     * @param cppDecl C++ declaration (source)
     * @param cDecl C declaration (target)
     *
     * Allows later lookups to find the C equivalent of a C++ declaration.
     *
     * Example:
     * @code
     *   ctx.registerDecl(cppFunc, cFunc);
     *   // Later: ctx.lookupDecl(cppFunc) returns cFunc
     * @endcode
     */
    void registerDecl(const clang::Decl* cppDecl, clang::Decl* cDecl);

    /**
     * @brief Lookup C declaration for C++ declaration
     * @param cppDecl C++ declaration to lookup
     * @return C declaration, or nullptr if not found
     *
     * Example:
     * @code
     *   Decl* cDecl = ctx.lookupDecl(cppDecl);
     *   if (cDecl) {
     *       // Use translated declaration
     *   }
     * @endcode
     */
    clang::Decl* lookupDecl(const clang::Decl* cppDecl) const;

    // ========================================================================
    // Type Translation
    // ========================================================================

    /**
     * @brief Translate C++ type to C type
     * @param cppType C++ type to translate
     * @return C type
     *
     * Handles:
     * - References (T&) → pointers (T*)
     * - Classes → structs (via symbol table lookup)
     * - Basic types → same
     *
     * Results are cached for performance.
     *
     * Example:
     * @code
     *   QualType cType = ctx.translateType(cppParam->getType());
     * @endcode
     */
    clang::QualType translateType(clang::QualType cppType);

    // ========================================================================
    // Function Context Management
    // ========================================================================

    /**
     * @brief Set the current function being translated
     * @param func C function declaration (translated version)
     *
     * Used by MethodHandler, ConstructorHandler, DestructorHandler to set
     * context for translating function bodies. This allows expression handlers
     * to access function parameters (e.g., 'this' parameter for CXXThisExpr).
     */
    void setCurrentFunction(clang::FunctionDecl* func) {
        currentFunction_ = func;
    }

    /**
     * @brief Get the current function being translated
     * @return Current C function declaration, or nullptr if not in function
     */
    clang::FunctionDecl* getCurrentFunction() const {
        return currentFunction_;
    }

    /**
     * @brief Push function onto context stack
     * @param func C function declaration to push
     *
     * Used for managing nested function translation contexts.
     * Automatically sets currentFunction_ to the pushed function.
     */
    void pushFunction(clang::FunctionDecl* func) {
        functionStack_.push_back(func);
        currentFunction_ = func;
    }

    /**
     * @brief Pop function from context stack
     *
     * Restores the previous function context, or sets currentFunction_ to nullptr
     * if the stack becomes empty.
     */
    void popFunction() {
        if (!functionStack_.empty()) {
            functionStack_.pop_back();
            currentFunction_ = functionStack_.empty() ? nullptr : functionStack_.back();
        }
    }

    // ========================================================================
    // Method Registration and Lookup
    // ========================================================================

    /**
     * @brief Register C++ method → C function mapping
     * @param cppMethod C++ method declaration (source)
     * @param cFunc C function declaration (target)
     *
     * Allows method call translation to find the corresponding C function.
     * The C function should have 'this' as its first parameter for non-static methods.
     *
     * Example:
     * @code
     *   // C++: class Counter { void increment(); };
     *   // C:   void Counter_increment(struct Counter* this);
     *   ctx.registerMethod(cppMethod, cFunc);
     * @endcode
     */
    void registerMethod(const clang::CXXMethodDecl* cppMethod, clang::FunctionDecl* cFunc) {
        methodMap_[cppMethod] = cFunc;
        // Also register in general decl map for backward compatibility
        registerDecl(cppMethod, cFunc);
    }

    /**
     * @brief Lookup C function for C++ method
     * @param cppMethod C++ method to lookup
     * @return C function declaration, or nullptr if not found
     *
     * Example:
     * @code
     *   FunctionDecl* cFunc = ctx.lookupMethod(cppMethod);
     *   if (cFunc) {
     *       // Use translated function
     *   }
     * @endcode
     */
    clang::FunctionDecl* lookupMethod(const clang::CXXMethodDecl* cppMethod) const {
        auto it = methodMap_.find(cppMethod);
        return (it != methodMap_.end()) ? it->second : nullptr;
    }
};

} // namespace cpptoc
