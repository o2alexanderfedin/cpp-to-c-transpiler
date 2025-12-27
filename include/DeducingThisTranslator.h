/**
 * @file DeducingThisTranslator.h
 * @brief Phase 4: Deducing This / Explicit Object Parameter Support (C++23 P0847R7)
 *
 * Translates C++23 explicit object parameters ("deducing this") to multiple C
 * function overloads. This is the most impactful C++23 feature, enabling unified
 * call syntax, recursive lambdas, and CRTP simplification.
 *
 * ## C++23 Feature: Deducing This (P0847R7)
 *
 * C++23 allows member functions to explicitly declare the implicit object parameter
 * (this) with cv-ref qualifiers, enabling a single function to handle multiple
 * qualification combinations:
 *
 * ```cpp
 * struct Buffer {
 *     std::string data;
 *
 *     // Single declaration works for all cv-ref combinations
 *     template<typename Self>
 *     auto&& get(this Self&& self) {
 *         return std::forward<Self>(self).data;
 *     }
 * };
 *
 * Buffer b;              // b.get() returns string&
 * const Buffer cb;       // cb.get() returns const string&
 * Buffer{}.get();        // temporary.get() returns string&&
 * ```
 *
 * ## Translation Strategy
 *
 * One C++23 method with explicit object parameter → Multiple C overloads:
 *
 * ### auto& self → 2 overloads
 * ```cpp
 * auto& get(this auto& self);
 * ```
 * Becomes:
 * ```c
 * T* Buffer__get_lvalue(struct Buffer* self);
 * const T* Buffer__get_const(const struct Buffer* self);
 * ```
 *
 * ### const auto& self → 1 overload
 * ```cpp
 * const T& get(this const auto& self);
 * ```
 * Becomes:
 * ```c
 * const T* Buffer__get_const(const struct Buffer* self);
 * ```
 *
 * ### auto&& self → 4 overloads (forwarding reference)
 * ```cpp
 * auto&& get(this auto&& self);
 * ```
 * Becomes:
 * ```c
 * T* Buffer__get_lvalue(struct Buffer* self);
 * const T* Buffer__get_const(const struct Buffer* self);
 * T* Buffer__get_rvalue(struct Buffer* self);
 * const T* Buffer__get_const_rvalue(const struct Buffer* self);
 * ```
 *
 * ### auto self → 1 overload (by value)
 * ```cpp
 * T get(this auto self);
 * ```
 * Becomes:
 * ```c
 * T Buffer__get_value(struct Buffer self);
 * ```
 *
 * ## Implementation Architecture
 *
 * Follows the proven translator pattern from Phase 2 (StaticOperatorTranslator):
 * 1. **Detection**: Check isExplicitObjectMemberFunction() on CXXMethodDecl
 * 2. **Overload Expansion**: Analyze parameter type to determine needed overloads
 * 3. **Function Generation**: Create C function for each cv-ref combination
 * 4. **Call Translation**: Analyze call site qualifiers and route to correct overload
 *
 * ## Design Principles
 *
 * - **SOLID**: Single Responsibility (only handles deducing this)
 * - **KISS**: Start simple (auto&, const auto&), add complexity incrementally
 * - **DRY**: Reuses CNodeBuilder for C AST construction
 * - **YAGNI**: Implements what Phase 33 tests require, documents limitations
 *
 * ## Call Site Qualifier Analysis
 *
 * At each call site, we analyze the object expression to determine qualifiers:
 *
 * ```cpp
 * Buffer b;              // lvalue, non-const → call Buffer__get_lvalue
 * const Buffer cb;       // lvalue, const → call Buffer__get_const
 * Buffer{}.get();        // rvalue, non-const → call Buffer__get_rvalue
 * std::move(b).get();    // rvalue, non-const → call Buffer__get_rvalue
 * ```
 *
 * ## References
 * - C++23 P0847R7: Deducing this
 * - Clang implementation: https://reviews.llvm.org/D140828
 * - Phase 4 Implementation Plan: .planning/phases/04-deducing-this/
 * - Phase 33 Tests: tests/real-world/cpp23-validation/gcc-adapted/deducing-this-P0847/
 *
 * @see CppToCVisitor::VisitCXXMethodDecl for method detection
 * @see CppToCVisitor::VisitCXXMemberCallExpr for call site transformation
 */

#ifndef DEDUCING_THIS_TRANSLATOR_H
#define DEDUCING_THIS_TRANSLATOR_H

#include "clang/AST/AST.h"
#include "CNodeBuilder.h"
#include <vector>
#include <string>

/**
 * @struct QualifierSet
 * @brief Represents a specific cv-ref qualifier combination for overload generation
 *
 * Each QualifierSet corresponds to one C function overload.
 */
struct QualifierSet {
    bool isConst;      ///< const-qualified object
    bool isRValue;     ///< rvalue object (temporary or moved)
    bool isValue;      ///< Pass by value (not pointer)

    QualifierSet(bool c = false, bool r = false, bool v = false)
        : isConst(c), isRValue(r), isValue(v) {}

    /**
     * @brief Generate suffix for overload function name
     * @return Suffix like "_lvalue", "_const", "_rvalue", "_value"
     */
    std::string getSuffix() const {
        if (isValue) {
            return "_value";
        } else if (isRValue) {
            return isConst ? "_const_rvalue" : "_rvalue";
        } else {
            return isConst ? "_const" : "_lvalue";
        }
    }
};

/**
 * @class DeducingThisTranslator
 * @brief Translates C++23 explicit object parameters to C function overloads
 *
 * This class handles the transformation of methods with explicit object parameters
 * into multiple C function overloads, each specialized for a specific cv-ref
 * qualification combination.
 *
 * ## Thread Safety
 * - No shared mutable state (safe for parallel translation units)
 * - CNodeBuilder owns AST node creation (thread-local ASTContext)
 *
 * ## Performance Characteristics
 * - Detection: O(1) per method declaration
 * - Overload generation: O(k) where k = number of qualifiers (1-4)
 * - Call transformation: O(1) qualifier analysis
 */
class DeducingThisTranslator {
public:
    /**
     * @brief Construct translator with C AST builder
     * @param Builder CNodeBuilder for creating C AST nodes
     */
    explicit DeducingThisTranslator(clang::CNodeBuilder& Builder);

    /**
     * @brief Transform method with explicit object parameter to C function overloads
     * @param MD CXXMethodDecl with explicit object parameter
     * @param Ctx Clang AST context
     * @param C_TU C translation unit for generated declarations
     * @return Vector of FunctionDecls (one per cv-ref combination), empty if not explicit object method
     *
     * This method is called when CppToCVisitor encounters a method with
     * isExplicitObjectMemberFunction() == true. It analyzes the explicit object
     * parameter type and generates appropriate C function overloads.
     *
     * Example:
     * ```cpp
     * // Input C++ AST
     * struct Buffer {
     *     auto& get(this auto& self) { return self.data; }
     * };
     *
     * // Output C AST (2 overloads)
     * int* Buffer__get_lvalue(struct Buffer* self);
     * const int* Buffer__get_const(const struct Buffer* self);
     * ```
     *
     * @note Returns empty vector if method is not an explicit object member function
     */
    std::vector<clang::FunctionDecl*> transformMethod(
        clang::CXXMethodDecl* MD,
        clang::ASTContext& Ctx,
        clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Transform call to method with explicit object parameter
     * @param Call CXXMemberCallExpr calling explicit object member function
     * @param Ctx Clang AST context
     * @return CallExpr to appropriate C overload, or nullptr if not applicable
     *
     * This method is called when CppToCVisitor encounters a call to a method
     * with explicit object parameter. It analyzes the call site object expression
     * to determine cv-ref qualifiers and selects the matching C overload.
     *
     * Example:
     * ```cpp
     * // Input C++ AST
     * Buffer b;
     * b.get();  // CXXMemberCallExpr, object = b (lvalue, non-const)
     *
     * // Output C AST
     * Buffer__get_lvalue(&b);  // CallExpr to lvalue overload
     * ```
     *
     * @note Returns nullptr if call is not to explicit object member function
     */
    clang::CallExpr* transformCall(
        clang::CXXMemberCallExpr* Call,
        clang::ASTContext& Ctx);

private:
    clang::CNodeBuilder& m_builder;

    /**
     * @brief Determine which overloads to generate based on parameter type
     * @param ParamType Type of the explicit object parameter
     * @return Vector of QualifierSets describing needed overloads
     *
     * Analysis:
     * - auto& → [lvalue, const] (2 overloads)
     * - const auto& → [const] (1 overload)
     * - auto&& → [lvalue, const, rvalue, const_rvalue] (4 overloads)
     * - auto → [value] (1 overload)
     */
    std::vector<QualifierSet> determineOverloads(clang::QualType ParamType);

    /**
     * @brief Generate one C function overload for a specific qualifier set
     * @param MD Original C++ method declaration
     * @param Quals Qualifier set for this overload
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return FunctionDecl for the C overload
     *
     * Creates function with signature:
     * ```c
     * ReturnType ClassName__methodName_suffix(QualifiedType* self, ...);
     * ```
     */
    clang::FunctionDecl* generateOverload(
        clang::CXXMethodDecl* MD,
        const QualifierSet& Quals,
        clang::ASTContext& Ctx,
        clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Analyze call site to determine object qualifiers
     * @param Object The object expression (e.g., 'b' in 'b.get()')
     * @return QualifierSet describing object's cv-ref qualifiers
     *
     * Analysis rules:
     * - DeclRefExpr to const variable → const lvalue
     * - CXXTemporaryObjectExpr → non-const rvalue
     * - CallExpr returning && → rvalue
     * - MaterializeTemporaryExpr → rvalue
     */
    QualifierSet analyzeCallSiteQualifiers(clang::Expr* Object);

    /**
     * @brief Find matching overload for call site qualifiers
     * @param MD Original method declaration
     * @param CallQuals Qualifiers from call site analysis
     * @param C_TU C translation unit containing overloads
     * @return FunctionDecl for matching overload, or nullptr if not found
     */
    clang::FunctionDecl* findMatchingOverload(
        clang::CXXMethodDecl* MD,
        const QualifierSet& CallQuals,
        clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Generate function name for overload
     * @param Class The class containing the method
     * @param Method The original method
     * @param Quals Qualifier set for this overload
     * @return Function name (e.g., "Buffer__get_lvalue")
     */
    std::string generateOverloadName(
        const clang::CXXRecordDecl* Class,
        const clang::CXXMethodDecl* Method,
        const QualifierSet& Quals);

    /**
     * @brief Transform method body, substituting explicit object param with 'self'
     * @param Body Original method body
     * @param OrigParam Original explicit object parameter
     * @param NewParam New 'self' parameter
     * @return Transformed statement
     *
     * Replaces references to the explicit object parameter with references
     * to the new 'self' parameter in the C function.
     */
    clang::Stmt* transformBody(
        clang::Stmt* Body,
        clang::ParmVarDecl* OrigParam,
        clang::ParmVarDecl* NewParam);
};

#endif // DEDUCING_THIS_TRANSLATOR_H
