/**
 * @file OverloadRegistry.h
 * @brief Global registry for tracking function overload sets across translation units
 *
 * The OverloadRegistry provides centralized tracking of all function overloads
 * in the transpilation process, enabling consistent cross-file name mangling.
 *
 * Key Features:
 * - Singleton pattern for global access
 * - Deterministic ordering of overloads (independent of registration order)
 * - Support for namespace-qualified function names
 * - Thread-safe singleton initialization
 * - O(log n) lookup performance
 *
 * Architecture:
 * - Each overload set is identified by a base name (e.g., "foo", "ns::bar", "Class::method")
 * - Overloads within a set are stored in deterministic order
 * - FunctionDecl pointers map to mangled names for quick lookup
 *
 * Usage Example:
 * @code
 *   OverloadRegistry& registry = OverloadRegistry::getInstance();
 *   registry.registerOverload("foo", fooIntDecl, "foo_int");
 *   registry.registerOverload("foo", fooDoubleDecl, "foo_double");
 *
 *   std::vector<std::string> overloads = registry.getOverloads("foo");
 *   // overloads = ["foo_double", "foo_int"] (deterministically ordered)
 * @endcode
 *
 * Thread Safety:
 * - Singleton getInstance() is thread-safe
 * - Individual methods are NOT thread-safe (assumes single-threaded transpilation)
 *
 * @see NameMangler for name generation
 * @see FunctionHandler for registration integration
 */

#ifndef OVERLOAD_REGISTRY_H
#define OVERLOAD_REGISTRY_H

#include "clang/AST/Decl.h"
#include <string>
#include <vector>
#include <map>
#include <set>

namespace cpptoc {

/**
 * @brief Global registry for function overload tracking
 *
 * Singleton class that tracks all function overloads across the entire
 * transpilation process. Ensures consistent name mangling regardless of
 * file processing order.
 *
 * Design Principles:
 * - SOLID: Single Responsibility (only tracks overloads, doesn't mangle names)
 * - KISS: Simple map-based storage with deterministic ordering
 * - DRY: Centralized overload tracking (eliminates per-file tracking)
 */
class OverloadRegistry {
public:
    /**
     * @brief Get singleton instance of registry
     * @return Reference to global OverloadRegistry instance
     *
     * Thread-safe singleton initialization using C++11 magic statics.
     * Multiple calls return the same instance.
     */
    static OverloadRegistry& getInstance();

    /**
     * @brief Register a function overload with its mangled name
     * @param baseName Unmangled base name (e.g., "foo", "ns::bar", "Class::method")
     * @param decl Pointer to FunctionDecl or CXXMethodDecl
     * @param mangledName The mangled C name for this overload
     *
     * Stores the association between the C++ declaration and its mangled name.
     * Overloads are stored in deterministic order based on signature comparison.
     *
     * Duplicate registrations (same baseName + decl) are ignored.
     *
     * Example:
     * @code
     *   registry.registerOverload("foo", fooIntDecl, "foo_int");
     *   registry.registerOverload("foo", fooDoubleDecl, "foo_double");
     * @endcode
     */
    void registerOverload(const std::string& baseName,
                          const clang::FunctionDecl* decl,
                          const std::string& mangledName);

    /**
     * @brief Get all mangled names for overload set
     * @param baseName Base function name to query
     * @return Vector of mangled names in deterministic order
     *
     * Returns empty vector if baseName has no registered overloads.
     *
     * Order is deterministic and independent of registration order:
     * - Sorted by parameter count (ascending)
     * - Then by parameter types (lexicographic on mangled names)
     * - Then by return type (tie-breaker)
     *
     * Example:
     * @code
     *   std::vector<std::string> overloads = registry.getOverloads("foo");
     *   // Returns: ["foo_double", "foo_int", "foo_int_int"]
     * @endcode
     */
    std::vector<std::string> getOverloads(const std::string& baseName) const;

    /**
     * @brief Get zero-based index of specific overload within its set
     * @param baseName Base function name
     * @param decl Function declaration to find
     * @return Index (0-based) or -1 if not found
     *
     * Useful for generating unique suffixes (_0, _1, _2, etc.) when needed.
     *
     * Example:
     * @code
     *   int index = registry.getOverloadIndex("foo", fooIntDecl);
     *   // Returns: 1 (if foo_int is second in deterministic order)
     * @endcode
     */
    int getOverloadIndex(const std::string& baseName,
                         const clang::FunctionDecl* decl) const;

    /**
     * @brief Get mangled name for specific declaration
     * @param baseName Base function name
     * @param decl Function declaration to look up
     * @return Mangled name, or empty string if not registered
     *
     * Direct lookup of mangled name by declaration pointer.
     *
     * Example:
     * @code
     *   std::string mangled = registry.getMangledName("foo", fooIntDecl);
     *   // Returns: "foo_int"
     * @endcode
     */
    std::string getMangledName(const std::string& baseName,
                               const clang::FunctionDecl* decl) const;

    /**
     * @brief Check if function has multiple overloads
     * @param baseName Base function name
     * @return true if 2+ overloads registered, false otherwise
     *
     * Useful for optimization: single overload doesn't need parameter encoding.
     *
     * Example:
     * @code
     *   if (!registry.hasMultipleOverloads("foo")) {
     *       // Can use simple name "foo" without parameter suffix
     *   }
     * @endcode
     */
    bool hasMultipleOverloads(const std::string& baseName) const;

    /**
     * @brief Count number of overloads for function
     * @param baseName Base function name
     * @return Number of registered overloads (0 if none)
     *
     * Example:
     * @code
     *   size_t count = registry.countOverloads("foo");
     *   // Returns: 3 (if foo has 3 overloads)
     * @endcode
     */
    size_t countOverloads(const std::string& baseName) const;

    /**
     * @brief Clear all registered overloads
     *
     * Resets registry to empty state. Useful for:
     * - Testing (isolate tests)
     * - Multiple transpilation runs (fresh state each time)
     *
     * Example:
     * @code
     *   registry.reset();  // Clear all overloads
     * @endcode
     */
    void reset();

    // Deleted copy/move operations (singleton pattern)
    OverloadRegistry(const OverloadRegistry&) = delete;
    OverloadRegistry& operator=(const OverloadRegistry&) = delete;
    OverloadRegistry(OverloadRegistry&&) = delete;
    OverloadRegistry& operator=(OverloadRegistry&&) = delete;

private:
    /**
     * @brief Private constructor (singleton pattern)
     */
    OverloadRegistry() = default;

    /**
     * @brief Private destructor (singleton pattern)
     */
    ~OverloadRegistry() = default;

    /**
     * @brief Information about a single overload
     */
    struct OverloadInfo {
        const clang::FunctionDecl* decl;  ///< Pointer to declaration
        std::string mangledName;          ///< Mangled C name

        /**
         * @brief Comparison operator for deterministic ordering
         *
         * Orders by signature to ensure deterministic results:
         * 1. Parameter count (ascending)
         * 2. Parameter types (lexicographic on mangled names)
         * 3. Return type (tie-breaker)
         * 4. Declaration pointer (final tie-breaker for stability)
         */
        bool operator<(const OverloadInfo& other) const;
    };

    /**
     * @brief Ordered set of overloads for a single function name
     *
     * Uses std::set with custom comparison for deterministic ordering.
     * Automatically maintains sorted order on insertion.
     */
    using OverloadSet = std::set<OverloadInfo>;

    /**
     * @brief Map from base name to overload set
     *
     * Key: Base function name (e.g., "foo", "ns::bar", "Class::method")
     * Value: Ordered set of all overloads for that name
     */
    std::map<std::string, OverloadSet> overloadSets_;

    /**
     * @brief Fast lookup map: (baseName, decl) -> mangledName
     *
     * Enables O(log n) lookup of mangled name by declaration.
     * Key: (baseName, FunctionDecl*)
     * Value: Mangled name
     */
    std::map<std::pair<std::string, const clang::FunctionDecl*>, std::string> declToMangledName_;
};

} // namespace cpptoc

#endif // OVERLOAD_REGISTRY_H
