#pragma once

#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/Basic/IdentifierTable.h"
#include "clang/Basic/LangOptions.h"
#include "clang/Basic/SourceManager.h"
#include "clang/Basic/TargetInfo.h"
#include "clang/Basic/Builtins.h"
#include <memory>

// Phase 35-02 (Bug #30 FIX): Separate source and target ASTContexts
//
// Architecture (per Clang standards):
// - Source ASTContext: Immutable, from frontend (one per .cpp file)
// - Target ASTContext: Mutable, for C AST nodes (ONE shared for all files)
// - C_TranslationUnit: One per file (standard: one TU per file)
//
// Each source file:
// 1. Gets its own source ASTContext from frontend
// 2. Creates its OWN C_TranslationUnit in the shared target context
// 3. Visitor creates all C nodes in the shared target context
// 4. Consumer outputs that C_TU to .c/.h files
//
// This fixes Bug #30: all C nodes exist in same context, but each file
// has its own C_TU for proper file-based output.

/**
 * @brief Singleton manager for the shared target (C output) ASTContext
 *
 * Manages ONE shared ASTContext used for ALL C AST node creation across
 * all source files. Each file creates its own TranslationUnit within this
 * shared context.
 */
class TargetContext {
private:
    // Infrastructure for independent target ASTContext
    // NOTE: DiagClient must be declared BEFORE Diagnostics so it's destroyed AFTER
    std::unique_ptr<clang::DiagnosticConsumer> DiagClient;
    std::unique_ptr<clang::FileManager> FileMgr;
    std::unique_ptr<clang::SourceManager> SourceMgr;
    std::unique_ptr<clang::DiagnosticsEngine> Diagnostics;
    std::unique_ptr<clang::TargetInfo> Target;
    std::unique_ptr<clang::IdentifierTable> Idents;
    std::unique_ptr<clang::SelectorTable> Selectors;
    std::unique_ptr<clang::Builtin::Context> Builtins;

    // The shared target ASTContext for all C nodes
    std::unique_ptr<clang::ASTContext> Context;

    // Singleton instance
    static TargetContext* instance;

    // Private constructor creates independent target context
    TargetContext();

public:
    // Destructor - must destroy Context before other dependencies
    ~TargetContext();

    // Singleton access
    static TargetContext& getInstance();

    // Singleton cleanup (call before program exit)
    static void cleanup();

    // Delete copy/move constructors
    TargetContext(const TargetContext&) = delete;
    TargetContext& operator=(const TargetContext&) = delete;

    /**
     * @brief Get the shared target ASTContext for C code generation
     * @return Reference to the shared target ASTContext
     *
     * All C nodes (from all files) are created in this context
     */
    clang::ASTContext& getContext() { return *Context; }

    /**
     * @brief Create a new C_TranslationUnit for a source file
     * @return Pointer to new C_TranslationUnit in the shared target context
     *
     * Each source file creates its own C_TU for separate .c/.h output
     */
    clang::TranslationUnitDecl* createTranslationUnit() {
        return clang::TranslationUnitDecl::Create(*Context);
    }

    /**
     * @brief Get the shared constructor map (mangled name -> C function)
     * @return Reference to the shared ctorMap
     *
     * This map is shared across all source files to enable multi-file constructor calls.
     * Uses mangled names as keys (not pointers) to work across different C++ ASTContexts.
     */
    std::map<std::string, clang::FunctionDecl *>& getCtorMap() { return ctorMap; }

    /**
     * @brief Get the shared method map (mangled name -> C function)
     * @return Reference to the shared methodMap
     *
     * This map is shared across all source files to enable multi-file method calls.
     * Uses mangled names as keys (not pointers) to work across different C++ ASTContexts.
     */
    std::map<std::string, clang::FunctionDecl *>& getMethodMap() { return methodMap; }

    /**
     * @brief Get the shared destructor map (mangled name -> C function)
     * @return Reference to the shared dtorMap
     *
     * This map is shared across all source files to enable multi-file destructor calls.
     * Uses mangled names as keys (not pointers) to work across different C++ ASTContexts.
     */
    std::map<std::string, clang::FunctionDecl *>& getDtorMap() { return dtorMap; }

private:
    // Shared maps for multi-file support (Bug Fix: use string keys to work across ASTContexts)
    // Each file has its own C++ ASTContext, so we can't use C++ AST pointers as keys.
    // Instead, we use mangled names which are stable across contexts.
    std::map<std::string, clang::FunctionDecl *> ctorMap;
    std::map<std::string, clang::FunctionDecl *> methodMap;
    std::map<std::string, clang::FunctionDecl *> dtorMap;
};
