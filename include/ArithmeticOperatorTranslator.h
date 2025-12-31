/**
 * @file ArithmeticOperatorTranslator.h
 * @brief Phase 50: Arithmetic Operator Overloading Support (v2.10.0)
 *
 * Translates C++ arithmetic operator overloading to equivalent C function calls.
 * Supports 10 distinct arithmetic operators: binary (+, -, *, /, %), unary (-, +),
 * increment/decrement (++, --), and compound assignment (+=, -=, *=, /=).
 *
 * ## Arithmetic Operators Coverage
 *
 * This translator handles ~40% of real-world operator overloading usage:
 * - Vector math: `Vector3D a + b`, `a * scalar`
 * - Matrix operations: `Matrix A * B`, `A += B`
 * - Complex numbers: `Complex c = -a + b * c`
 * - BigInteger: `BigInt a + b`, `a++`
 * - Custom numeric types: All arithmetic operations
 *
 * ## Translation Patterns
 *
 * ### Binary Operators (+, -, *, /, %)
 * ```cpp
 * class Vector {
 *     Vector operator+(const Vector& other) const;
 * };
 * Vector c = a + b;
 * ```
 * Translates to:
 * ```c
 * Vector Vector_operator_plus_const_Vector_ref(const Vector* this, const Vector* other);
 * Vector c = Vector_operator_plus_const_Vector_ref(&a, &b);
 * ```
 *
 * ### Unary Operators (-, +)
 * ```cpp
 * Complex operator-() const;
 * Complex neg = -c;
 * ```
 * Translates to:
 * ```c
 * Complex Complex_operator_negate_const(const Complex* this);
 * Complex neg = Complex_operator_negate_const(&c);
 * ```
 *
 * ### Prefix Increment/Decrement (++x, --x)
 * ```cpp
 * Counter& operator++();
 * ++counter;
 * ```
 * Translates to:
 * ```c
 * Counter* Counter_operator_increment_prefix(Counter* this);
 * Counter_operator_increment_prefix(&counter);
 * ```
 *
 * ### Postfix Increment/Decrement (x++, x--)
 * ```cpp
 * Iterator operator++(int);
 * it++;
 * ```
 * Translates to:
 * ```c
 * Iterator Iterator_operator_increment_postfix(Iterator* this, int dummy);
 * Iterator_operator_increment_postfix(&it, 0);
 * ```
 *
 * ### Compound Assignment (+=, -=, *=, /=)
 * ```cpp
 * BigInt& operator+=(const BigInt& other);
 * a += b;
 * ```
 * Translates to:
 * ```c
 * BigInt* BigInt_operator_plus_assign_const_BigInt_ref(BigInt* this, const BigInt* other);
 * BigInt_operator_plus_assign_const_BigInt_ref(&a, &b);
 * ```
 *
 * ## Implementation Architecture
 *
 * Follows the proven translator pattern from StaticOperatorTranslator:
 * 1. **Detection**: VisitCXXMethodDecl identifies arithmetic operators
 * 2. **Function Generation**: Creates C function with explicit `this` parameter
 * 3. **Call Translation**: VisitCXXOperatorCallExpr transforms call sites
 * 4. **AST Replacement**: Replaces C++ operator call with C CallExpr
 *
 * ## Design Principles
 *
 * - **SOLID**: Single Responsibility (only handles arithmetic operators)
 * - **KISS**: Straightforward operator-to-function mapping
 * - **DRY**: Common infrastructure for all 10 operators
 * - **Map-Reduce**: 10 independent operator handlers can run in parallel
 *
 * ## Supported Operators
 *
 * | Operator | C++ Example | C Function Pattern |
 * |----------|-------------|-------------------|
 * | `+` | `a + b` | `Class_operator_plus` |
 * | `-` (binary) | `a - b` | `Class_operator_minus` |
 * | `*` | `a * b` | `Class_operator_multiply` |
 * | `/` | `a / b` | `Class_operator_divide` |
 * | `%` | `a % b` | `Class_operator_modulo` |
 * | `-` (unary) | `-a` | `Class_operator_negate` |
 * | `+` (unary) | `+a` | `Class_operator_positive` |
 * | `++` (prefix) | `++a` | `Class_operator_increment_prefix` |
 * | `++` (postfix) | `a++` | `Class_operator_increment_postfix` |
 * | `--` (prefix) | `--a` | `Class_operator_decrement_prefix` |
 * | `--` (postfix) | `a--` | `Class_operator_decrement_postfix` |
 * | `+=` | `a += b` | `Class_operator_plus_assign` |
 * | `-=` | `a -= b` | `Class_operator_minus_assign` |
 * | `*=` | `a *= b` | `Class_operator_multiply_assign` |
 * | `/=` | `a /= b` | `Class_operator_divide_assign` |
 *
 * ## Key Insights
 *
 * 1. **Prefix vs Postfix**: Distinguished by dummy `int` parameter in postfix
 * 2. **Return Types**:
 *    - Binary operators: Return by value (new object)
 *    - Prefix inc/dec: Return reference (pointer in C)
 *    - Postfix inc/dec: Return by value (copy before modify)
 *    - Compound assignment: Return reference (pointer in C)
 * 3. **Const Correctness**: Const operators get `const This*` parameter
 * 4. **Operator Chaining**: `a + b + c` creates nested CallExpr nodes
 *
 * ## References
 * - Phase 50 Plan: .planning/phases/50-arithmetic-operators/PHASE50-PLAN.md
 * - Test Suite: tests/unit/arithmetic-operators/
 * - Integration Tests: tests/integration/arithmetic-operators/
 *
 * @see CppToCVisitor::VisitCXXMethodDecl for method detection
 * @see CppToCVisitor::VisitCXXOperatorCallExpr for call site transformation
 * @see NameMangler for operator name generation
 */

#ifndef ARITHMETIC_OPERATOR_TRANSLATOR_H
#define ARITHMETIC_OPERATOR_TRANSLATOR_H

#include "clang/AST/AST.h"
#include "CNodeBuilder.h"
#include "NameMangler.h"
#include <string>
#include <map>

/**
 * @class ArithmeticOperatorTranslator
 * @brief Translates C++ arithmetic operator overloading to C function calls
 *
 * This class handles the transformation of 10 distinct arithmetic operators
 * into equivalent C function calls with explicit `this` parameters.
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
class ArithmeticOperatorTranslator {
public:
    /**
     * @brief Construct translator with C AST builder
     * @param Builder CNodeBuilder for creating C AST nodes
     *
     * Note: Name mangling is handled by cpptoc::mangle_method() free function
     */
    explicit ArithmeticOperatorTranslator(clang::CNodeBuilder& Builder);

    /**
     * @brief Transform arithmetic operator method to C function declaration
     * @param MD CXXMethodDecl representing operator method
     * @param Ctx Clang AST context
     * @param C_TU C translation unit for generated declarations
     * @return FunctionDecl for equivalent C function, or nullptr if not arithmetic operator
     *
     * This method is called when CppToCVisitor encounters an arithmetic operator
     * method declaration. It generates a C function with:
     * - Explicit `this` parameter (Class* this or const Class* this)
     * - Same parameter list as C++ operator
     * - Same return type as C++ operator (or pointer for reference returns)
     *
     * Example:
     * ```cpp
     * // Input C++ AST
     * class Vector {
     *     Vector operator+(const Vector& other) const;  // CXXMethodDecl
     * };
     *
     * // Output C AST
     * Vector Vector_operator_plus_const_Vector_ref(
     *     const Vector* this, const Vector* other);  // FunctionDecl
     * ```
     *
     * @note Returns nullptr if method is not an arithmetic operator
     */
    clang::FunctionDecl* transformMethod(clang::CXXMethodDecl* MD,
                                         clang::ASTContext& Ctx,
                                         clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Transform arithmetic operator call site to C function call
     * @param E CXXOperatorCallExpr representing call to arithmetic operator
     * @param Ctx Clang AST context
     * @return CallExpr for equivalent C function call, or nullptr if not arithmetic
     *
     * This method is called when CppToCVisitor encounters an arithmetic operator
     * call expression. It builds a CallExpr with:
     * - Reference to the generated C function
     * - Address-of expressions for object arguments
     * - Value arguments for primitives
     *
     * Example:
     * ```cpp
     * // Input C++ AST
     * Vector c = a + b;  // CXXOperatorCallExpr(op=+, args=[a, b])
     *
     * // Output C AST
     * Vector c = Vector_operator_plus_const_Vector_ref(&a, &b);  // CallExpr
     * ```
     *
     * @note Returns nullptr if operator is not arithmetic
     */
    clang::CallExpr* transformCall(clang::CXXOperatorCallExpr* E,
                                   clang::ASTContext& Ctx);

    /**
     * @brief Check if operator is an arithmetic operator
     * @param Op OverloadedOperatorKind to check
     * @return true if operator is arithmetic (one of 10 supported operators)
     */
    bool isArithmeticOperator(clang::OverloadedOperatorKind Op) const;

private:
    clang::CNodeBuilder& m_builder;

    /// Map from C++ method to generated C function
    std::map<const clang::CXXMethodDecl*, clang::FunctionDecl*> m_methodMap;

    // ========================================================================
    // Binary Operator Translators (5 operators)
    // ========================================================================

    /**
     * @brief Translate binary plus operator (+)
     * @param MD Method declaration for operator+
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator+
     */
    clang::FunctionDecl* translateBinaryPlus(clang::CXXMethodDecl* MD,
                                             clang::ASTContext& Ctx,
                                             clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate binary minus operator (-)
     * @param MD Method declaration for operator-
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator-
     */
    clang::FunctionDecl* translateBinaryMinus(clang::CXXMethodDecl* MD,
                                              clang::ASTContext& Ctx,
                                              clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate binary multiply operator (*)
     * @param MD Method declaration for operator*
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator*
     */
    clang::FunctionDecl* translateBinaryMultiply(clang::CXXMethodDecl* MD,
                                                 clang::ASTContext& Ctx,
                                                 clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate binary divide operator (/)
     * @param MD Method declaration for operator/
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator/
     */
    clang::FunctionDecl* translateBinaryDivide(clang::CXXMethodDecl* MD,
                                               clang::ASTContext& Ctx,
                                               clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate binary modulo operator (%)
     * @param MD Method declaration for operator%
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator%
     */
    clang::FunctionDecl* translateBinaryModulo(clang::CXXMethodDecl* MD,
                                               clang::ASTContext& Ctx,
                                               clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Unary Operator Translators (2 operators)
    // ========================================================================

    /**
     * @brief Translate unary minus operator (-)
     * @param MD Method declaration for unary operator-
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for unary operator-
     * @note Distinguished from binary minus by parameter count (0 vs 1)
     */
    clang::FunctionDecl* translateUnaryMinus(clang::CXXMethodDecl* MD,
                                             clang::ASTContext& Ctx,
                                             clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate unary plus operator (+)
     * @param MD Method declaration for unary operator+
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for unary operator+
     */
    clang::FunctionDecl* translateUnaryPlus(clang::CXXMethodDecl* MD,
                                            clang::ASTContext& Ctx,
                                            clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Increment/Decrement Operator Translators (4 operators)
    // ========================================================================

    /**
     * @brief Translate prefix increment operator (++x)
     * @param MD Method declaration for operator++()
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for prefix operator++
     * @note Returns pointer (C's reference) to modified object
     */
    clang::FunctionDecl* translatePrefixIncrement(clang::CXXMethodDecl* MD,
                                                  clang::ASTContext& Ctx,
                                                  clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate postfix increment operator (x++)
     * @param MD Method declaration for operator++(int)
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for postfix operator++
     * @note Has dummy int parameter, returns copy by value
     */
    clang::FunctionDecl* translatePostfixIncrement(clang::CXXMethodDecl* MD,
                                                   clang::ASTContext& Ctx,
                                                   clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate prefix decrement operator (--x)
     * @param MD Method declaration for operator--()
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for prefix operator--
     */
    clang::FunctionDecl* translatePrefixDecrement(clang::CXXMethodDecl* MD,
                                                  clang::ASTContext& Ctx,
                                                  clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate postfix decrement operator (x--)
     * @param MD Method declaration for operator--(int)
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for postfix operator--
     */
    clang::FunctionDecl* translatePostfixDecrement(clang::CXXMethodDecl* MD,
                                                   clang::ASTContext& Ctx,
                                                   clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Compound Assignment Operator Translators (4 operators)
    // ========================================================================

    /**
     * @brief Translate compound assignment operators (+=, -=, *=, /=)
     * @param MD Method declaration for operator+=, -=, *=, or /=
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for compound assignment operator
     * @note All return pointer (C's reference) to modified object
     */
    clang::FunctionDecl* translateCompoundAssignment(clang::CXXMethodDecl* MD,
                                                     clang::ASTContext& Ctx,
                                                     clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Call Site Transformation Helpers
    // ========================================================================

    /**
     * @brief Transform binary operator call to C function call
     * @param E CXXOperatorCallExpr for binary operator
     * @param Ctx AST context
     * @return CallExpr for C function
     */
    clang::CallExpr* transformBinaryOpCall(clang::CXXOperatorCallExpr* E,
                                           clang::ASTContext& Ctx);

    /**
     * @brief Transform unary operator call to C function call
     * @param E CXXOperatorCallExpr for unary operator
     * @param Ctx AST context
     * @return CallExpr for C function
     */
    clang::CallExpr* transformUnaryOpCall(clang::CXXOperatorCallExpr* E,
                                          clang::ASTContext& Ctx);

    /**
     * @brief Transform increment/decrement operator call to C function call
     * @param E CXXOperatorCallExpr for ++/-- operator
     * @param Ctx AST context
     * @return CallExpr for C function
     */
    clang::CallExpr* transformIncrementDecrementCall(clang::CXXOperatorCallExpr* E,
                                                     clang::ASTContext& Ctx);

    /**
     * @brief Transform compound assignment operator call to C function call
     * @param E CXXOperatorCallExpr for +=, -=, *=, /= operator
     * @param Ctx AST context
     * @return CallExpr for C function
     */
    clang::CallExpr* transformCompoundAssignmentCall(clang::CXXOperatorCallExpr* E,
                                                     clang::ASTContext& Ctx);

    // ========================================================================
    // Utility Functions
    // ========================================================================

    /**
     * @brief Generate C function name for arithmetic operator
     * @param MD The operator method declaration
     * @return C function name (e.g., "Vector_operator_plus")
     *
     * Naming convention:
     * - Binary operators: `{Class}_operator_{op}_{params}`
     * - Unary operators: `{Class}_operator_{op}_unary_{params}`
     * - Prefix inc/dec: `{Class}_operator_increment_prefix`
     * - Postfix inc/dec: `{Class}_operator_increment_postfix`
     * - Compound: `{Class}_operator_plus_assign_{params}`
     */
    std::string generateOperatorName(const clang::CXXMethodDecl* MD);

    /**
     * @brief Find or create C function for arithmetic operator
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
     * @brief Determine if operator is binary (vs unary)
     * @param MD Operator method declaration
     * @return true if binary operator (has 1 parameter)
     */
    bool isBinaryOperator(const clang::CXXMethodDecl* MD) const;

    /**
     * @brief Determine if operator is prefix (vs postfix) increment/decrement
     * @param MD Operator method declaration
     * @return true if prefix (no parameters), false if postfix (int parameter)
     */
    bool isPrefixOperator(const clang::CXXMethodDecl* MD) const;
};

#endif // ARITHMETIC_OPERATOR_TRANSLATOR_H
