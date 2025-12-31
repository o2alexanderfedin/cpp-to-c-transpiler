/**
 * @file NamespaceHandler.h
 * @brief Handler for processing NamespaceDecl nodes (namespace declarations)
 *
 * Registers with CppToCVisitorDispatcher to handle C++ namespace declarations.
 * Tracks namespace paths and flattens namespace-qualified names to C identifiers.
 *
 * Phase 1 Scope: Namespace tracking ONLY
 * - Compute namespace paths (A::B → A__B)
 * - Store namespace mappings (for reference tracking)
 * - Recursively dispatch child declarations
 * - Handle anonymous namespaces with deterministic IDs
 *
 * Future Phases:
 * - Integration with FunctionHandler/RecordHandler for name prefixing
 * - Using directives (using namespace X)
 * - Namespace aliases (namespace Y = X)
 *
 * Design Pattern: Chain of Responsibility handler for dispatcher
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"

namespace cpptoc {

/**
 * @class NamespaceHandler
 * @brief Processes NamespaceDecl and tracks namespace paths for name flattening
 *
 * Responsibilities:
 * - Match NamespaceDecl nodes (predicate)
 * - Compute namespace path recursively (A::B::C → A__B__C)
 * - Generate deterministic IDs for anonymous namespaces
 * - Store namespace mappings (for tracking, NO C equivalent created)
 * - Recursively dispatch child declarations
 * - Child handlers will check parent context and apply namespace prefix
 *
 * Translation Strategy (C has NO namespaces):
 * - Track namespace paths but DON'T create C NamespaceDecl
 * - Store mapping: declMapper.setCreated(cppNS, nullptr)
 * - Child declarations get prefixed based on parent namespace context
 *
 * Translation Examples:
 *
 * C++ namespace:
 * @code
 * namespace MyApp {
 *     void foo() {}
 * }
 * @endcode
 *
 * C flattened name (child handler applies prefix):
 * @code
 * void MyApp__foo() {}
 * @endcode
 *
 * C++ nested namespace:
 * @code
 * namespace A {
 *     namespace B {
 *         void bar() {}
 *     }
 * }
 * @endcode
 *
 * C flattened name:
 * @code
 * void A__B__bar() {}
 * @endcode
 *
 * C++ C++17 nested namespace syntax:
 * @code
 * namespace A::B::C {
 *     void baz() {}
 * }
 * @endcode
 *
 * C flattened name:
 * @code
 * void A__B__C__baz() {}
 * @endcode
 *
 * C++ anonymous namespace:
 * @code
 * namespace {
 *     void internal() {}
 * }
 * @endcode
 *
 * C with unique ID:
 * @code
 * void __anon_12345_internal() {}  // ID based on source location
 * @endcode
 *
 * Usage:
 * @code
 * CppToCVisitorDispatcher dispatcher(pathMapper, declLocationMapper, ...);
 * NamespaceHandler::registerWith(dispatcher);  // Register BEFORE FunctionHandler/RecordHandler
 * FunctionHandler::registerWith(dispatcher);
 *
 * NamespaceDecl* cppNS = ...;
 * dispatcher.dispatch(cppCtx, cCtx, cppNS);
 * // → Stores namespace mapping, recursively dispatches children
 * @endcode
 */
class NamespaceHandler {
public:
    /**
     * @brief Register this handler with the dispatcher
     * @param dispatcher Dispatcher to register with
     *
     * Registers both predicate and visitor for NamespaceDecl
     */
    static void registerWith(CppToCVisitorDispatcher& dispatcher);

    /**
     * @brief Compute full namespace path recursively
     * @param NS Namespace declaration to compute path for
     * @return Namespace path with "__" separator (e.g., "A__B__C")
     *
     * Algorithm:
     * 1. Walk parent DeclContexts from inner to outer
     * 2. Collect namespace names (skip anonymous namespaces)
     * 3. Reverse collected names
     * 4. Join with "__" separator
     *
     * Examples:
     * - Single level: "MyApp" → "MyApp"
     * - Nested: A::B → "A__B"
     * - Triple nested: A::B::C → "A__B__C"
     * - Anonymous skipped: A::<anon>::B → "A__B"
     *
     * Handles C++17 nested namespace syntax:
     * - namespace A::B::C {} is equivalent to namespace A { namespace B { namespace C {} } }
     * - Both produce path "A__B__C"
     *
     * Made public for testing
     */
    static std::string getNamespacePath(const clang::NamespaceDecl* NS);

    /**
     * @brief Generate deterministic unique ID for anonymous namespace
     * @param NS Anonymous namespace declaration
     * @param SM Source manager for location information
     * @return Unique ID based on source location (e.g., "__anon_12345")
     *
     * Implementation:
     * 1. Get source location of namespace
     * 2. Use raw encoding as hash (deterministic across runs)
     * 3. Generate ID: "__anon_<hash>"
     *
     * Pattern matches NameMangler::getAnonymousNamespaceID() for consistency
     *
     * Example: namespace {} at line 42 → "__anon_12345"
     *
     * Made public for testing
     */
    static std::string generateAnonymousID(
        const clang::NamespaceDecl* NS,
        const clang::SourceManager& SM
    );

private:
    /**
     * @brief Predicate: Check if declaration is EXACTLY NamespaceDecl
     * @param D Declaration to check (must not be null)
     * @return true if D is NamespaceDecl
     *
     * Implementation pattern:
     * 1. Assert D is not null (fails fast on programming errors)
     * 2. Use D->getKind() for exact type matching
     * 3. Accept only Namespace kind
     *
     * @pre D != nullptr (asserted)
     */
    static bool canHandle(const clang::Decl* D);

    /**
     * @brief Visitor: Process C++ namespace and dispatch child declarations
     * @param disp Dispatcher for accessing PathMapper and child handlers
     * @param cppASTContext Source C++ ASTContext (read-only)
     * @param cASTContext Target C ASTContext (write)
     * @param D NamespaceDecl to process (must not be null)
     *
     * Algorithm:
     * 1. Assert D is not null and is NamespaceDecl
     * 2. Cast D to NamespaceDecl
     * 3. Check declMapper.hasCreated() - skip if already processed
     * 4. Detect anonymous vs named namespace:
     *    - If isAnonymousNamespace(), generate unique ID
     *    - Otherwise, use namespace name
     * 5. Compute full namespace path recursively:
     *    - Walk parent DeclContexts
     *    - Collect all namespace names from inner to outer
     *    - Reverse and join with "__" separator
     *    - Example: A::B::C → ["C", "B", "A"] → reverse → "A__B__C"
     * 6. Store namespace mapping for tracking:
     *    - declMapper.setCreated(cppNamespace, nullptr)
     *    - NO C NamespaceDecl created (C has no namespaces)
     *    - Mapping is for tracking only
     * 7. Recursively dispatch child declarations:
     *    - Iterate through NS->decls()
     *    - Dispatch each child to appropriate handler
     *    - Child handlers will check parent context for namespace prefix
     * 8. Debug output for verification
     *
     * Phase 1 Limitation: Only tracks namespaces, doesn't apply prefixes
     * - Prefix application requires integration with child handlers (Phase 2)
     * - This phase focuses on namespace path computation and tracking
     *
     * @pre D != nullptr && D->getKind() == Decl::Namespace (asserted)
     */
    static void handleNamespace(
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext,
        const clang::Decl* D
    );

    /**
     * @brief Recursively dispatch child declarations in namespace
     * @param NS Namespace declaration
     * @param disp Dispatcher for recursive dispatch
     * @param cppASTContext Source C++ ASTContext
     * @param cASTContext Target C ASTContext
     *
     * Iterates through NS->decls() and dispatches each child:
     * - FunctionDecl → FunctionHandler (will apply namespace prefix in Phase 2)
     * - RecordDecl → RecordHandler (will apply namespace prefix in Phase 2)
     * - NamespaceDecl → NamespaceHandler (recursive for nested namespaces)
     * - Other declarations → appropriate handlers
     *
     * Phase 1: Just dispatch, child handlers don't apply prefix yet
     * Phase 2: Child handlers will check parent context and apply prefix
     */
    static void processChildDecls(
        const clang::NamespaceDecl* NS,
        const CppToCVisitorDispatcher& disp,
        const clang::ASTContext& cppASTContext,
        clang::ASTContext& cASTContext
    );
};

} // namespace cpptoc
