/**
 * @file ComparisonOperatorTranslator.h
 * @brief Phase 51: Comparison & Logical Operator Overloading Support (v2.11.0)
 *
 * Translates C++ comparison and logical operator overloading to equivalent C function calls.
 * Supports 9 distinct operators: relational (<, >, <=, >=), equality (==, !=),
 * and logical (!, &&, ||).
 *
 * ## Comparison & Logical Operators Coverage
 *
 * This translator handles ~30% of real-world operator overloading usage:
 * - Container operations: Sorting, searching, binary search trees
 * - Conditional logic: if (a < b), while (x != y)
 * - Standard algorithms: std::sort, std::find, std::lower_bound
 * - Custom types: Rational numbers, dates, strings, complex objects
 *
 * ## Translation Patterns
 *
 * ### Relational Operators (<, >, <=, >=)
 * ```cpp
 * class Date {
 *     bool operator<(const Date& other) const;
 * };
 * Date d1, d2;
 * if (d1 < d2) { }
 * ```
 * Translates to:
 * ```c
 * #include <stdbool.h>
 * bool Date_operator_less_const_Date_ref(const Date* this, const Date* other);
 * Date d1, d2;
 * if (Date_operator_less_const_Date_ref(&d1, &d2)) { }
 * ```
 *
 * ### Equality Operators (==, !=)
 * ```cpp
 * class Rational {
 *     bool operator==(const Rational& other) const;
 * };
 * Rational a, b;
 * if (a == b) { }
 * ```
 * Translates to:
 * ```c
 * bool Rational_operator_equal_const_Rational_ref(const Rational* this, const Rational* other);
 * Rational a, b;
 * if (Rational_operator_equal_const_Rational_ref(&a, &b)) { }
 * ```
 *
 * ### Logical NOT Operator (!)
 * ```cpp
 * class SmartPointer {
 *     bool operator!() const;
 * };
 * SmartPointer p;
 * if (!p) { }
 * ```
 * Translates to:
 * ```c
 * bool SmartPointer_operator_not_const(const SmartPointer* this);
 * SmartPointer p;
 * if (SmartPointer_operator_not_const(&p)) { }
 * ```
 *
 * ### Logical AND/OR Operators (&&, ||)
 * ```cpp
 * class Predicate {
 *     bool operator&&(const Predicate& other) const;
 * };
 * ```
 * Translates to:
 * ```c
 * bool Predicate_operator_and_const_Predicate_ref(const Predicate* this, const Predicate* other);
 * ```
 * **WARNING**: Loses short-circuit evaluation!
 *
 * ## Implementation Architecture
 *
 * Follows the proven translator pattern from ArithmeticOperatorTranslator:
 * 1. **Detection**: VisitCXXMethodDecl identifies comparison/logical operators
 * 2. **Function Generation**: Creates C function with explicit `this` parameter
 * 3. **Call Translation**: VisitCXXOperatorCallExpr transforms call sites
 * 4. **AST Replacement**: Replaces C++ operator call with C CallExpr
 *
 * ## Design Principles
 *
 * - **SOLID**: Single Responsibility (only handles comparison/logical operators)
 * - **KISS**: Straightforward operator-to-function mapping
 * - **DRY**: Common infrastructure for all 9 operators
 * - **Map-Reduce**: 9 independent operator handlers can run in parallel
 * - **Type Safety**: All operators return bool (via <stdbool.h>)
 *
 * ## Supported Operators
 *
 * | Operator | C++ Example | C Function Pattern | Return Type |
 * |----------|-------------|-------------------|-------------|
 * | `<` | `a < b` | `Class_operator_less` | bool |
 * | `>` | `a > b` | `Class_operator_greater` | bool |
 * | `<=` | `a <= b` | `Class_operator_less_equal` | bool |
 * | `>=` | `a >= b` | `Class_operator_greater_equal` | bool |
 * | `==` | `a == b` | `Class_operator_equal` | bool |
 * | `!=` | `a != b` | `Class_operator_not_equal` | bool |
 * | `!` | `!a` | `Class_operator_not` | bool |
 * | `&&` | `a && b` | `Class_operator_and` | bool |
 * | `||` | `a || b` | `Class_operator_or` | bool |
 *
 * ## Key Insights
 *
 * 1. **All return bool**: Every comparison/logical operator returns bool (C99's <stdbool.h>)
 * 2. **Const member functions**: Typically const (don't modify object state)
 * 3. **Short-circuit loss**: operator&& and operator|| lose short-circuit semantics
 * 4. **Equivalence relations**: operator== must be reflexive, symmetric, transitive
 * 5. **Strict weak ordering**: operator< must define total order for sorting
 * 6. **Friend operators**: Common for symmetrical operations (lhs == rhs)
 *
 * ## References
 * - Phase 51 Plan: .planning/phases/51-comparison-operators/PHASE51-PLAN.md
 * - Test Suite: tests/unit/comparison-operators/
 * - Integration Tests: tests/integration/comparison-operators/
 *
 * @see CppToCVisitor::VisitCXXMethodDecl for method detection
 * @see CppToCVisitor::VisitCXXOperatorCallExpr for call site transformation
 * @see NameMangler for operator name generation
 */

#ifndef COMPARISON_OPERATOR_TRANSLATOR_H
#define COMPARISON_OPERATOR_TRANSLATOR_H

#include "clang/AST/AST.h"
#include "CNodeBuilder.h"
#include "NameMangler.h"
#include <string>
#include <map>

/**
 * @class ComparisonOperatorTranslator
 * @brief Translates C++ comparison and logical operator overloading to C function calls
 *
 * This class handles the transformation of 9 distinct comparison and logical operators
 * into equivalent C function calls with explicit `this` parameters.
 * All operators return bool (via <stdbool.h>).
 *
 * ## Thread Safety
 * - No shared mutable state (safe for parallel translation units)
 * - CNodeBuilder owns AST node creation (thread-local ASTContext)
 * - MethodMap is local to each translator instance
 *
 * ## Performance Characteristics
 * - Detection: O(1) per method declaration
 * - Transformation: O(n) where n = number of arguments
 * - Memory: <1KB per operator translation
 */
class ComparisonOperatorTranslator {
public:
    /**
     * @brief Construct translator with C AST builder
     * @param Builder CNodeBuilder for creating C AST nodes
     */
    explicit ComparisonOperatorTranslator(clang::CNodeBuilder& Builder);

    /**
     * @brief Transform comparison/logical operator method to C function declaration
     * @param MD CXXMethodDecl representing operator method
     * @param Ctx Clang AST context
     * @param C_TU C translation unit for generated declarations
     * @return FunctionDecl for equivalent C function, or nullptr if not comparison/logical operator
     *
     * This method is called when CppToCVisitor encounters a comparison/logical operator
     * method declaration. It generates a C function with:
     * - Explicit `this` parameter (Class* this or const Class* this)
     * - Same parameter list as C++ operator
     * - bool return type (via <stdbool.h>)
     *
     * Example:
     * ```cpp
     * // Input C++ AST
     * class Date {
     *     bool operator<(const Date& other) const;  // CXXMethodDecl
     * };
     *
     * // Output C AST
     * bool Date_operator_less_const_Date_ref(
     *     const Date* this, const Date* other);  // FunctionDecl
     * ```
     *
     * @note Returns nullptr if method is not a comparison/logical operator
     */
    clang::FunctionDecl* transformMethod(clang::CXXMethodDecl* MD,
                                         clang::ASTContext& Ctx,
                                         clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Transform comparison/logical operator call site to C function call
     * @param E CXXOperatorCallExpr representing call to comparison/logical operator
     * @param Ctx Clang AST context
     * @return CallExpr for equivalent C function call, or nullptr if not comparison/logical
     *
     * This method is called when CppToCVisitor encounters a comparison/logical operator
     * call expression. It builds a CallExpr with:
     * - Reference to the generated C function
     * - Address-of expressions for object arguments
     * - bool return type
     *
     * Example:
     * ```cpp
     * // Input C++ AST
     * Date d1, d2;
     * if (d1 < d2) { }  // CXXOperatorCallExpr(op=<, args=[d1, d2])
     *
     * // Output C AST
     * if (Date_operator_less_const_Date_ref(&d1, &d2)) { }  // CallExpr
     * ```
     *
     * @note Returns nullptr if operator is not comparison/logical
     */
    clang::CallExpr* transformCall(clang::CXXOperatorCallExpr* E,
                                   clang::ASTContext& Ctx);

    /**
     * @brief Check if operator is a comparison/logical operator
     * @param Op OverloadedOperatorKind to check
     * @return true if operator is comparison/logical (one of 9 supported operators)
     */
    bool isComparisonOperator(clang::OverloadedOperatorKind Op) const;

private:
    clang::CNodeBuilder& m_builder;

    /// Map from C++ method to generated C function
    std::map<const clang::CXXMethodDecl*, clang::FunctionDecl*> m_methodMap;

    // ========================================================================
    // Relational Operator Translators (4 operators)
    // ========================================================================

    /**
     * @brief Translate less-than operator (<)
     * @param MD Method declaration for operator<
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator< (returns bool)
     */
    clang::FunctionDecl* translateLessThan(clang::CXXMethodDecl* MD,
                                           clang::ASTContext& Ctx,
                                           clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate greater-than operator (>)
     * @param MD Method declaration for operator>
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator> (returns bool)
     */
    clang::FunctionDecl* translateGreaterThan(clang::CXXMethodDecl* MD,
                                              clang::ASTContext& Ctx,
                                              clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate less-than-or-equal operator (<=)
     * @param MD Method declaration for operator<=
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator<= (returns bool)
     */
    clang::FunctionDecl* translateLessThanOrEqual(clang::CXXMethodDecl* MD,
                                                  clang::ASTContext& Ctx,
                                                  clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate greater-than-or-equal operator (>=)
     * @param MD Method declaration for operator>=
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator>= (returns bool)
     */
    clang::FunctionDecl* translateGreaterThanOrEqual(clang::CXXMethodDecl* MD,
                                                     clang::ASTContext& Ctx,
                                                     clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Equality Operator Translators (2 operators)
    // ========================================================================

    /**
     * @brief Translate equality operator (==)
     * @param MD Method declaration for operator==
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator== (returns bool)
     */
    clang::FunctionDecl* translateEqual(clang::CXXMethodDecl* MD,
                                        clang::ASTContext& Ctx,
                                        clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate inequality operator (!=)
     * @param MD Method declaration for operator!=
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator!= (returns bool)
     */
    clang::FunctionDecl* translateNotEqual(clang::CXXMethodDecl* MD,
                                           clang::ASTContext& Ctx,
                                           clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Logical Operator Translators (3 operators)
    // ========================================================================

    /**
     * @brief Translate logical NOT operator (!)
     * @param MD Method declaration for operator!
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator! (returns bool)
     * @note Unary operator (single operand)
     */
    clang::FunctionDecl* translateLogicalNot(clang::CXXMethodDecl* MD,
                                             clang::ASTContext& Ctx,
                                             clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate logical AND operator (&&)
     * @param MD Method declaration for operator&&
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator&& (returns bool)
     * @warning LOSES SHORT-CIRCUIT EVALUATION
     */
    clang::FunctionDecl* translateLogicalAnd(clang::CXXMethodDecl* MD,
                                             clang::ASTContext& Ctx,
                                             clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate logical OR operator (||)
     * @param MD Method declaration for operator||
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator|| (returns bool)
     * @warning LOSES SHORT-CIRCUIT EVALUATION
     */
    clang::FunctionDecl* translateLogicalOr(clang::CXXMethodDecl* MD,
                                            clang::ASTContext& Ctx,
                                            clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Call Site Transformation Helpers
    // ========================================================================

    /**
     * @brief Transform binary comparison operator call to C function call
     * @param E CXXOperatorCallExpr for binary operator
     * @param Ctx AST context
     * @return CallExpr for C function
     */
    clang::CallExpr* transformBinaryComparisonCall(clang::CXXOperatorCallExpr* E,
                                                   clang::ASTContext& Ctx);

    /**
     * @brief Transform unary logical operator call to C function call
     * @param E CXXOperatorCallExpr for unary operator
     * @param Ctx AST context
     * @return CallExpr for C function
     */
    clang::CallExpr* transformUnaryLogicalCall(clang::CXXOperatorCallExpr* E,
                                               clang::ASTContext& Ctx);

    // ========================================================================
    // Utility Functions
    // ========================================================================

    /**
     * @brief Generate C function name for comparison/logical operator
     * @param MD The operator method declaration
     * @return C function name (e.g., "Date_operator_less")
     *
     * Naming convention:
     * - Relational: `{Class}_operator_{less|greater|less_equal|greater_equal}_{params}`
     * - Equality: `{Class}_operator_{equal|not_equal}_{params}`
     * - Logical NOT: `{Class}_operator_not_{params}`
     * - Logical AND/OR: `{Class}_operator_{and|or}_{params}`
     */
    std::string generateOperatorName(const clang::CXXMethodDecl* MD);

    /**
     * @brief Find or create C function for comparison/logical operator
     * @param MD The C++ operator method
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return FunctionDecl for the C function
     *
     * Implements "get-or-create" pattern:
     * - Checks m_methodMap cache first
     * - If exists, returns cached FunctionDecl
     * - If not, creates new FunctionDecl with explicit `this` parameter
     */
    clang::FunctionDecl* findOrCreateFunction(const clang::CXXMethodDecl* MD,
                                              clang::ASTContext& Ctx,
                                              clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Create bool return type for comparison/logical operators
     * @param Ctx AST context
     * @return QualType for bool (via <stdbool.h>)
     */
    clang::QualType createBoolReturnType(clang::ASTContext& Ctx) const;

    /**
     * @brief Determine if operator is unary (vs binary)
     * @param MD Operator method declaration
     * @return true if unary operator (has 0 parameters), false if binary (1 parameter)
     */
    bool isUnaryOperator(const clang::CXXMethodDecl* MD) const;
};

#endif // COMPARISON_OPERATOR_TRANSLATOR_H
