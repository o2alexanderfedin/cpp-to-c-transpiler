/**
 * @file TypeMapper.h
 * @brief RAII mapper for C++ types to created C types
 *
 * This provides a per-instance mapper around NodeMapper using RAII pattern.
 * Each instance maintains its own mapping state.
 *
 * Single Responsibility: Provide type-specific mapper for NodeMapper.
 *
 * Phase 1 Extension: Adds layout context tracking for dual layout support
 * in virtual inheritance scenarios (base-subobject vs complete-object layouts).
 *
 * Usage:
 * - Create: TypeMapper typeMapper;
 * - Usage: typeMapper.setCreated(cppType, cType)
 * - Usage: typeMapper.getCreated(cppType)
 * - Usage: typeMapper.hasCreated(cppType)
 * - Usage: typeMapper.getCTypeForContext(record, context)
 * - Usage: typeMapper.determineLayoutContext(expr, record)
 */

#pragma once

#include "mapping/NodeMapper.h"
#include "clang/AST/Type.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"

namespace cpptoc {

/**
 * @enum LayoutContext
 * @brief Specifies which memory layout to use for classes with virtual bases
 *
 * Per Itanium C++ ABI, classes with virtual bases require dual layouts:
 * - CompleteObject: Full layout including virtual base fields (struct ClassName)
 * - BaseSubobject: Partial layout excluding virtual base fields (struct ClassName__base)
 *
 * Context determination rules:
 * Rule 1: Local variables → CompleteObject
 * Rule 2: Non-virtual base member → BaseSubobject
 * Rule 3: Virtual base member → CompleteObject
 * Rule 4: Most-derived class → CompleteObject
 * Rule 5: Cast target → analyze cast path
 */
enum class LayoutContext {
    CompleteObject,   ///< Use struct ClassName (includes virtual base fields)
    BaseSubobject,    ///< Use struct ClassName__base (excludes virtual base fields)
    Unknown           ///< Context needs further analysis
};

/**
 * @class TypeMapper
 * @brief RAII wrapper for mapping C++ types to created C types
 *
 * Wraps NodeMapper<clang::Type, clang::QualType> with RAII semantics.
 * Each test/thread creates its own instance for complete isolation.
 *
 * Note: ValueT is QualType (value type), not QualType* (pointer)
 * QualType is a lightweight handle that acts like a pointer internally.
 *
 * Example:
 * ```cpp
 * auto typeMapper = std::make_unique<TypeMapper>();
 * typeMapper->setCreated(cppRefType, cPtrType);
 * clang::QualType cType = typeMapper->getCreated(cppRefType);
 * if (typeMapper->hasCreated(cppRefType)) { ... }
 * ```
 */
class TypeMapper {
public:
  /**
   * @brief Public constructor for RAII pattern
   *
   * **RAII Pattern**: Each test creates its own TypeMapper instance
   * **Thread Safety**: Each thread/test has isolated instance - fully thread-safe
   */
  TypeMapper() = default;

  /**
   * @brief Store mapping from C++ type to created C type
   * @param cppNode Source C++ type
   * @param cNode Created C type (QualType)
   */
  void setCreated(const clang::Type* cppNode, clang::QualType cNode) {
    mapper_.setCreated(cppNode, cNode);
  }

  /**
   * @brief Get C type created for a C++ type
   * @param cppNode Source C++ type
   * @return Created C type, or null QualType if not found
   */
  clang::QualType getCreated(const clang::Type* cppNode) const {
    return mapper_.getCreated(cppNode);
  }

  /**
   * @brief Check if a C++ type has a mapped C type
   * @param cppNode Source C++ type
   * @return true if mapping exists, false otherwise
   */
  bool hasCreated(const clang::Type* cppNode) const {
    return mapper_.hasCreated(cppNode);
  }

  /**
   * @brief Get C type for a C++ record with specific layout context
   * @param record Source C++ record declaration
   * @param context Layout context (CompleteObject or BaseSubobject)
   * @return C QualType for the specified layout, or null QualType if not found
   *
   * For classes with virtual bases:
   * - CompleteObject → struct ClassName (includes virtual base fields)
   * - BaseSubobject → struct ClassName__base (excludes virtual base fields)
   *
   * For classes without virtual bases:
   * - Both contexts → struct ClassName (single layout)
   */
  clang::QualType getCTypeForContext(const clang::CXXRecordDecl* record,
                                     LayoutContext context) const;

  /**
   * @brief Determine layout context from expression usage
   * @param expr Expression using the record type
   * @param record Record declaration being used
   * @return Determined layout context or Unknown if analysis needed
   *
   * Applies Itanium ABI context rules:
   * - Rule 1: Local variables → CompleteObject
   * - Rule 2: Non-virtual base member → BaseSubobject
   * - Rule 3: Virtual base member → CompleteObject
   * - Rule 4: Most-derived class → CompleteObject
   * - Rule 5: Cast target → analyze cast path
   */
  LayoutContext determineLayoutContext(const clang::Expr* expr,
                                       const clang::CXXRecordDecl* record) const;

  // Prevent copying (use move semantics or unique_ptr instead)
  TypeMapper(const TypeMapper&) = delete;
  TypeMapper& operator=(const TypeMapper&) = delete;

  // Allow move semantics for modern C++
  TypeMapper(TypeMapper&&) = default;
  TypeMapper& operator=(TypeMapper&&) = default;

private:
  NodeMapper<clang::Type, clang::QualType> mapper_;

  /**
   * @brief Check if expression represents a local variable declaration
   * @param expr Expression to analyze
   * @return true if expr is a local variable (stack-allocated)
   */
  bool isLocalVariable(const clang::Expr* expr) const;

  /**
   * @brief Check if expression represents a non-virtual base member
   * @param expr Expression to analyze
   * @return true if expr accesses a non-virtual base subobject
   */
  bool isNonVirtualBaseMember(const clang::Expr* expr) const;

  /**
   * @brief Check if expression represents a virtual base member
   * @param expr Expression to analyze
   * @return true if expr accesses a virtual base subobject
   */
  bool isVirtualBaseMember(const clang::Expr* expr) const;

  /**
   * @brief Check if record is the most-derived class in this context
   * @param expr Expression context
   * @param record Record declaration to check
   * @return true if record is the most-derived class (not used as base)
   */
  bool isMostDerivedClass(const clang::Expr* expr,
                          const clang::CXXRecordDecl* record) const;

  /**
   * @brief Analyze cast expression to determine target layout context
   * @param castExpr Cast expression to analyze
   * @param record Target record of the cast
   * @return Layout context for the cast target
   */
  LayoutContext analyzeCastContext(const clang::CastExpr* castExpr,
                                   const clang::CXXRecordDecl* record) const;
};

} // namespace cpptoc
