/**
 * @file NodeMapper.h
 * @brief Generic template for mapping C++ AST nodes to created C AST nodes
 *
 * Single Responsibility: Provide a unified, type-safe mapping interface for all AST node types.
 *
 * This generic template eliminates code duplication across DeclMapper, TypeMapper,
 * ExprMapper, and StmtMapper by providing a single implementation that works for all.
 *
 * Design Principles:
 * - DRY: Single implementation for all mapper types
 * - KISS: Simple, straightforward template design
 * - Type Safety: Compile-time type checking via templates
 * - Zero Overhead: Templates are compile-time, no runtime cost
 *
 * Example Usage:
 * ```cpp
 * // Create mapper instances
 * NodeMapper<clang::Decl, clang::Decl*> declMapper;
 * NodeMapper<clang::Type, clang::QualType> typeMapper;
 *
 * // Store mapping
 * declMapper.setCreated(cppDecl, cDecl);
 * typeMapper.setCreated(cppType, cType);
 *
 * // Retrieve mapping
 * clang::Decl* cDecl = declMapper.getCreated(cppDecl);
 * clang::QualType cType = typeMapper.getCreated(cppType);
 *
 * // Check existence
 * if (declMapper.hasCreated(cppDecl)) { ... }
 * ```
 */

#pragma once

#include <map>
#include <cassert>

namespace cpptoc {

/**
 * @class NodeMapper
 * @brief Generic template for managing mappings from C++ AST nodes to created C AST nodes
 *
 * @tparam KeyT The C++ AST node type (e.g., clang::Decl, clang::Type)
 * @tparam ValueT The C AST node type (e.g., clang::Decl*, clang::QualType)
 *
 * Responsibilities:
 * - Store C++ → C AST node mappings
 * - Retrieve C nodes for given C++ nodes
 * - Support Chain of Responsibility pattern for handlers
 *
 * Type Requirements:
 * - KeyT must be a pointer-compatible type
 * - ValueT must be default-constructible (returns ValueT{} when not found)
 * - For pointer types: ValueT{} = nullptr
 * - For QualType: ValueT{} = null QualType
 */
template<typename KeyT, typename ValueT>
class NodeMapper {
public:
    /**
     * @brief Default constructor
     */
    NodeMapper() = default;

    /**
     * @brief Store mapping from C++ node to created C node
     * @param cppNode Source C++ AST node
     * @param cNode Created C AST node
     *
     * Enables parent handlers to retrieve child nodes created by child handlers.
     *
     * Example:
     * ```cpp
     * // Handler creates C node and stores mapping
     * NodeMapper<clang::Expr, clang::Expr*> exprMapper;
     * clang::IntegerLiteral* cLit = createIntegerLiteral(...);
     * exprMapper.setCreated(cppLit, cLit);
     *
     * // Parent handler retrieves created node
     * clang::Expr* cExpr = exprMapper.getCreated(cppLit);
     * ```
     */
    void setCreated(const KeyT* cppNode, ValueT cNode) {
        assert(cppNode && "C++ node must not be null");
        mapping_[cppNode] = cNode;
    }

    /**
     * @brief Get C node created for a C++ node
     * @param cppNode Source C++ AST node
     * @return Created C node, or ValueT{} if not found
     *
     * Retrieves C node previously stored via setCreated().
     * Returns ValueT{} if no mapping exists:
     * - For pointer types: nullptr
     * - For QualType: null QualType
     */
    ValueT getCreated(const KeyT* cppNode) const {
        assert(cppNode && "C++ node must not be null");
        auto it = mapping_.find(cppNode);
        return (it != mapping_.end()) ? it->second : ValueT{};
    }

    /**
     * @brief Check if a C++ node has a mapped C node
     * @param cppNode Source C++ AST node
     * @return true if mapping exists, false otherwise
     *
     * Use this to check for duplicate processing or verify translation occurred.
     *
     * Example:
     * ```cpp
     * if (exprMapper.hasCreated(cppExpr)) {
     *     // Already translated, skip
     *     return;
     * }
     * ```
     */
    bool hasCreated(const KeyT* cppNode) const {
        assert(cppNode && "C++ node must not be null");
        return mapping_.find(cppNode) != mapping_.end();
    }

private:
    std::map<const KeyT*, ValueT> mapping_;
    ///< Maps C++ source nodes to created C nodes
    ///< Key is always const pointer to C++ node
    ///< Value can be pointer (Decl*, Expr*, Stmt*) or value type (QualType)
};

} // namespace cpptoc
