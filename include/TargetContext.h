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
 * @brief RAII manager for the target (C output) ASTContext
 *
 * Manages ONE ASTContext used for C AST node creation.
 * Each file creates its own TranslationUnit within this context.
 *
 * RAII Pattern: Each test/transpilation session creates its own instance
 * for complete isolation. Thread-safe through instance isolation.
 */
class TargetContext {
public:
    // Public constructor for RAII pattern
    TargetContext();

    // Destructor - must destroy Context before other dependencies
    ~TargetContext();

    // Prevent copying (use move semantics or unique_ptr instead)
    TargetContext(const TargetContext&) = delete;
    TargetContext& operator=(const TargetContext&) = delete;

    // Allow move semantics for modern C++
    TargetContext(TargetContext&&) = default;
    TargetContext& operator=(TargetContext&&) = default;

private:
    // Infrastructure for independent target ASTContext
    // NOTE: DiagClient and DiagOpts must be declared BEFORE Diagnostics so they're destroyed AFTER
    // NOTE: TargetOpts must be declared BEFORE Target so it's destroyed AFTER
    std::unique_ptr<clang::DiagnosticConsumer> DiagClient;
    std::unique_ptr<clang::DiagnosticOptions> DiagOpts;
    std::unique_ptr<clang::TargetOptions> TargetOpts;
    std::unique_ptr<clang::FileManager> FileMgr;
    std::unique_ptr<clang::SourceManager> SourceMgr;
    std::unique_ptr<clang::DiagnosticsEngine> Diagnostics;
    std::unique_ptr<clang::TargetInfo> Target;
    std::unique_ptr<clang::IdentifierTable> Idents;
    std::unique_ptr<clang::SelectorTable> Selectors;
    std::unique_ptr<clang::Builtin::Context> Builtins;

    // The target ASTContext for all C nodes
    std::unique_ptr<clang::ASTContext> Context;

public:

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

    /**
     * @brief Find existing global enum by name
     * @param name Enum name (e.g., "GameState")
     * @return Pointer to existing EnumDecl or nullptr if not found
     *
     * Used for deduplication: check if enum already exists before creating new one
     */
    clang::EnumDecl* findEnum(const std::string& name);

    /**
     * @brief Find existing global struct by name
     * @param name Struct name (e.g., "Point")
     * @return Pointer to existing RecordDecl or nullptr if not found
     *
     * Used for deduplication: check if struct already exists before creating new one
     */
    clang::RecordDecl* findStruct(const std::string& name);

    /**
     * @brief Find existing global typedef by name
     * @param name Typedef name (e.g., "String")
     * @return Pointer to existing TypedefDecl or nullptr if not found
     *
     * Used for deduplication: check if typedef already exists before creating new one
     */
    clang::TypedefDecl* findTypedef(const std::string& name);

    /**
     * @brief Record C AST node and its output file location
     * @param node C AST node (e.g., EnumDecl, RecordDecl, FunctionDecl)
     * @param location Output file path where this node will be emitted
     *
     * Each C AST node has exactly ONE output file location
     */
    void recordNode(const clang::Decl* node, const std::string& location);

    /**
     * @brief Get output file location for a C AST node
     * @param node C AST node
     * @return Output file path, or empty string if not recorded
     */
    std::string getLocation(const clang::Decl* node) const;

private:
    // Shared maps for multi-file support (Bug Fix: use string keys to work across ASTContexts)
    // Each file has its own C++ ASTContext, so we can't use C++ AST pointers as keys.
    // Instead, we use mangled names which are stable across contexts.
    std::map<std::string, clang::FunctionDecl *> ctorMap;
    std::map<std::string, clang::FunctionDecl *> methodMap;
    std::map<std::string, clang::FunctionDecl *> dtorMap;

    // Node location tracking (Phase 1.1)
    // Maps C AST nodes to their output file paths
    std::map<const clang::Decl*, std::string> nodeToLocation;

    // Global deduplication maps (Phase 1.1)
    // Maps enum/struct/typedef names to their C AST nodes to prevent duplicates
    std::map<std::string, clang::EnumDecl*> globalEnums;
    std::map<std::string, clang::RecordDecl*> globalStructs;
    std::map<std::string, clang::TypedefDecl*> globalTypedefs;
};
