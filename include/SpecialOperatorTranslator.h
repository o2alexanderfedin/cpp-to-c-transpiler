/**
 * @file SpecialOperatorTranslator.h
 * @brief Phase 52: Special Operator Overloading Support (v2.12.0)
 *
 * Translates C++ special operator overloading to equivalent C function calls.
 * Supports 12 distinct special operators including subscript, call, smart pointer,
 * stream I/O, conversion, assignment, and rare operators.
 *
 * ## Special Operators Coverage
 *
 * This translator handles ~25% of real-world operator overloading usage:
 * - Smart pointers: `operator->`, `operator*`, `explicit operator bool()`
 * - Containers: `operator[]` (instance version)
 * - Functors: `operator()` (callable objects)
 * - Stream I/O: `operator<<`, `operator>>` for custom types
 * - Type conversions: `operator T()`, `explicit operator bool()`
 * - Assignment: Copy assignment `operator=`, move assignment `operator=(T&&)`
 * - Rare operators: `operator&`, `operator,`
 *
 * ## Translation Patterns
 *
 * ### Instance Subscript Operator ([])
 * ```cpp
 * class Array {
 *     int& operator[](size_t index);
 *     const int& operator[](size_t index) const;
 * };
 * arr[5] = 42;
 * ```
 * Translates to:
 * ```c
 * int* Array_operator_subscript_size_t(Array* this, size_t index);
 * const int* Array_operator_subscript_size_t_const(const Array* this, size_t index);
 * *Array_operator_subscript_size_t(&arr, 5) = 42;
 * ```
 *
 * ### Instance Call Operator (Functors)
 * ```cpp
 * class Adder {
 *     int operator()(int x) const;
 * };
 * Adder add10(10);
 * int result = add10(5);
 * ```
 * Translates to:
 * ```c
 * int Adder_operator_call_int_const(const Adder* this, int x);
 * Adder add10 = Adder_constructor(10);
 * int result = Adder_operator_call_int_const(&add10, 5);
 * ```
 *
 * ### Smart Pointer Operators (-> and *)
 * ```cpp
 * class SmartPtr {
 *     T* operator->() const;
 *     T& operator*() const;
 *     explicit operator bool() const;
 * };
 * ptr->method();
 * (*ptr).value = 42;
 * if (ptr) { }
 * ```
 * Translates to:
 * ```c
 * T* SmartPtr_operator_arrow_const(const SmartPtr* this);
 * T* SmartPtr_operator_star_const(const SmartPtr* this);
 * bool SmartPtr_operator_bool_const(const SmartPtr* this);
 * SmartPtr_operator_arrow_const(&ptr)->method(...);
 * SmartPtr_operator_star_const(&ptr)->value = 42;
 * if (SmartPtr_operator_bool_const(&ptr)) { }
 * ```
 *
 * ### Stream Operators (<< >>)
 * ```cpp
 * class Point {
 *     friend ostream& operator<<(ostream& os, const Point& p);
 * };
 * cout << p;
 * ```
 * Translates to:
 * ```c
 * void Point_operator_output(FILE* os, const Point* p);
 * Point_operator_output(stdout, &p);
 * ```
 *
 * ### Conversion Operators
 * ```cpp
 * class Celsius {
 *     operator double() const;
 *     explicit operator int() const;
 *     explicit operator bool() const;
 * };
 * double d = temp;
 * if (temp) { }
 * ```
 * Translates to:
 * ```c
 * double Celsius_operator_to_double_const(const Celsius* this);
 * int Celsius_operator_to_int_const(const Celsius* this);
 * bool Celsius_operator_to_bool_const(const Celsius* this);
 * double d = Celsius_operator_to_double_const(&temp);
 * if (Celsius_operator_to_bool_const(&temp)) { }
 * ```
 *
 * ### Assignment Operators (Copy and Move)
 * ```cpp
 * class String {
 *     String& operator=(const String& other);  // Copy assignment
 *     String& operator=(String&& other);       // Move assignment
 * };
 * s1 = s2;         // Copy
 * s1 = String();   // Move
 * ```
 * Translates to:
 * ```c
 * String* String_operator_assign_const_String_ref(String* this, const String* other);
 * String* String_operator_assign_String_rvalue_ref(String* this, String* other);
 * String_operator_assign_const_String_ref(&s1, &s2);
 * String temp = String_constructor();
 * String_operator_assign_String_rvalue_ref(&s1, &temp);
 * ```
 *
 * ## Implementation Architecture
 *
 * Follows the proven translator pattern from ArithmeticOperatorTranslator:
 * 1. **Detection**: VisitCXXMethodDecl and VisitCXXConversionDecl identify special operators
 * 2. **Function Generation**: Creates C function with explicit `this` parameter
 * 3. **Call Translation**: VisitCXXOperatorCallExpr transforms call sites
 * 4. **AST Replacement**: Replaces C++ operator call with C CallExpr
 *
 * ## Design Principles
 *
 * - **SOLID**: Single Responsibility (only handles special operators)
 * - **KISS**: Straightforward operator-to-function mapping
 * - **DRY**: Common infrastructure for all 12 operators
 * - **Map-Reduce**: 12 independent operator handlers
 *
 * ## Supported Operators
 *
 * | Operator | C++ Example | C Function Pattern |
 * |----------|-------------|-------------------|
 * | `[]` | `arr[i]` | `Class_operator_subscript` |
 * | `()` | `func(x)` | `Class_operator_call` |
 * | `->` | `ptr->member` | `Class_operator_arrow` |
 * | `*` (deref) | `*ptr` | `Class_operator_star` |
 * | `<<` | `cout << obj` | `Class_operator_output` |
 * | `>>` | `cin >> obj` | `Class_operator_input` |
 * | `operator T()` | `(double)obj` | `Class_operator_to_T` |
 * | `operator bool()` | `if (obj)` | `Class_operator_to_bool` |
 * | `=` (copy) | `a = b` | `Class_operator_assign` |
 * | `=` (move) | `a = move(b)` | `Class_operator_assign_move` |
 * | `&` | `&obj` | `Class_operator_addressof` |
 * | `,` | `(a, b)` | `Class_operator_comma` |
 *
 * ## Critical TODO Resolution
 *
 * This phase resolves two critical TODOs in CppToCVisitor.cpp:
 * - Line ~520: Copy assignment operator storage
 * - Move assignment operator storage (location TBD)
 *
 * ## References
 * - Phase 52 Plan: .planning/phases/52-special-operators/PHASE52-PLAN.md
 * - Test Suite: tests/unit/special-operators/
 * - Integration Tests: tests/integration/special-operators/
 *
 * @see CppToCVisitor::VisitCXXMethodDecl for method detection
 * @see CppToCVisitor::VisitCXXConversionDecl for conversion operator detection
 * @see CppToCVisitor::VisitCXXOperatorCallExpr for call site transformation
 * @see NameMangler for operator name generation
 */

#ifndef SPECIAL_OPERATOR_TRANSLATOR_H
#define SPECIAL_OPERATOR_TRANSLATOR_H

#include "clang/AST/AST.h"
#include "CNodeBuilder.h"
#include "NameMangler.h"
#include <string>
#include <map>

/**
 * @class SpecialOperatorTranslator
 * @brief Translates C++ special operator overloading to C function calls
 *
 * This class handles the transformation of 12 distinct special operators
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
class SpecialOperatorTranslator {
public:
    /**
     * @brief Construct translator with C AST builder and name mangler
     * @param Builder CNodeBuilder for creating C AST nodes
     * @param Mangler NameMangler for generating operator function names
     */
    explicit SpecialOperatorTranslator(clang::CNodeBuilder& Builder,
                                       NameMangler& Mangler);

    /**
     * @brief Transform special operator method to C function declaration
     * @param MD CXXMethodDecl representing operator method
     * @param Ctx Clang AST context
     * @param C_TU C translation unit for generated declarations
     * @return FunctionDecl for equivalent C function, or nullptr if not special operator
     *
     * Handles: operator[], operator(), operator->, operator*, operator<<, operator>>,
     * operator= (copy/move), operator&, operator,
     */
    clang::FunctionDecl* transformMethod(clang::CXXMethodDecl* MD,
                                         clang::ASTContext& Ctx,
                                         clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Transform conversion operator to C function declaration
     * @param CD CXXConversionDecl representing conversion operator
     * @param Ctx Clang AST context
     * @param C_TU C translation unit for generated declarations
     * @return FunctionDecl for equivalent C function, or nullptr on error
     *
     * Handles: operator T(), explicit operator bool(), etc.
     */
    clang::FunctionDecl* transformConversion(clang::CXXConversionDecl* CD,
                                             clang::ASTContext& Ctx,
                                             clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Transform special operator call site to C function call
     * @param E CXXOperatorCallExpr representing call to special operator
     * @param Ctx Clang AST context
     * @return CallExpr for equivalent C function call, or nullptr if not special operator
     */
    clang::CallExpr* transformCall(clang::CXXOperatorCallExpr* E,
                                   clang::ASTContext& Ctx);

    /**
     * @brief Check if operator is a special operator
     * @param Op OverloadedOperatorKind to check
     * @return true if operator is special (one of 12 supported operators)
     */
    bool isSpecialOperator(clang::OverloadedOperatorKind Op) const;

private:
    clang::CNodeBuilder& m_builder;
    NameMangler& m_mangler;

    /// Map from C++ method to generated C function
    std::map<const clang::CXXMethodDecl*, clang::FunctionDecl*> m_methodMap;

    /// Map from C++ conversion operator to generated C function
    std::map<const clang::CXXConversionDecl*, clang::FunctionDecl*> m_conversionMap;

    // ========================================================================
    // Instance Subscript and Call Operators (2 operators)
    // ========================================================================

    /**
     * @brief Translate instance subscript operator ([])
     * @param MD Method declaration for operator[]
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator[]
     * @note Returns pointer (reference in C++) for lvalue usage
     */
    clang::FunctionDecl* translateInstanceSubscript(clang::CXXMethodDecl* MD,
                                                    clang::ASTContext& Ctx,
                                                    clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate instance call operator (())
     * @param MD Method declaration for operator()
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator()
     * @note Supports variable arity (0, 1, 2+ parameters)
     */
    clang::FunctionDecl* translateInstanceCall(clang::CXXMethodDecl* MD,
                                               clang::ASTContext& Ctx,
                                               clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Smart Pointer Operators (2 operators)
    // ========================================================================

    /**
     * @brief Translate arrow operator (->)
     * @param MD Method declaration for operator->
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator->
     * @note Returns raw pointer for chained member access
     */
    clang::FunctionDecl* translateArrow(clang::CXXMethodDecl* MD,
                                        clang::ASTContext& Ctx,
                                        clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate dereference operator (*)
     * @param MD Method declaration for operator*
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator*
     * @note Returns pointer (reference in C++) to dereferenced object
     */
    clang::FunctionDecl* translateDereference(clang::CXXMethodDecl* MD,
                                              clang::ASTContext& Ctx,
                                              clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Stream I/O Operators (2 operators)
    // ========================================================================

    /**
     * @brief Translate stream output operator (<<)
     * @param MD Method declaration for operator<<
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator<<
     * @note Distinguishes from bitwise left shift by parameter types
     */
    clang::FunctionDecl* translateStreamOutput(clang::CXXMethodDecl* MD,
                                               clang::ASTContext& Ctx,
                                               clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate stream input operator (>>)
     * @param MD Method declaration for operator>>
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator>>
     * @note Distinguishes from bitwise right shift by parameter types
     */
    clang::FunctionDecl* translateStreamInput(clang::CXXMethodDecl* MD,
                                              clang::ASTContext& Ctx,
                                              clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Conversion Operators (2 categories)
    // ========================================================================

    /**
     * @brief Translate bool conversion operator (explicit operator bool())
     * @param CD Conversion declaration for operator bool()
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator bool()
     * @note Used in conditionals: if (obj), while (obj), !obj
     */
    clang::FunctionDecl* translateBoolConversion(clang::CXXConversionDecl* CD,
                                                 clang::ASTContext& Ctx,
                                                 clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate generic conversion operator (operator T())
     * @param CD Conversion declaration for operator T()
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator T()
     * @note Handles all conversion types: operator int(), operator double(), etc.
     */
    clang::FunctionDecl* translateConversionOperator(clang::CXXConversionDecl* CD,
                                                     clang::ASTContext& Ctx,
                                                     clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Assignment Operators (2 operators - CRITICAL for TODO resolution)
    // ========================================================================

    /**
     * @brief Translate copy assignment operator (operator=)
     * @param MD Method declaration for copy assignment
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for copy assignment
     * @note CRITICAL: Resolves TODO at CppToCVisitor.cpp:~520
     */
    clang::FunctionDecl* translateCopyAssignment(clang::CXXMethodDecl* MD,
                                                 clang::ASTContext& Ctx,
                                                 clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate move assignment operator (operator=(T&&))
     * @param MD Method declaration for move assignment
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for move assignment
     * @note CRITICAL: Resolves move assignment TODO
     */
    clang::FunctionDecl* translateMoveAssignment(clang::CXXMethodDecl* MD,
                                                 clang::ASTContext& Ctx,
                                                 clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Rare Operators (2 operators)
    // ========================================================================

    /**
     * @brief Translate address-of operator (operator&)
     * @param MD Method declaration for operator&
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator&
     * @note RARE: Almost never overloaded in practice
     */
    clang::FunctionDecl* translateAddressOf(clang::CXXMethodDecl* MD,
                                            clang::ASTContext& Ctx,
                                            clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Translate comma operator (operator,)
     * @param MD Method declaration for operator,
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return C FunctionDecl for operator,
     * @note VERY RARE: Almost never overloaded in practice
     */
    clang::FunctionDecl* translateComma(clang::CXXMethodDecl* MD,
                                        clang::ASTContext& Ctx,
                                        clang::TranslationUnitDecl* C_TU);

    // ========================================================================
    // Call Site Transformation Helpers
    // ========================================================================

    /**
     * @brief Transform subscript operator call to C function call
     * @param E CXXOperatorCallExpr for operator[]
     * @param Ctx AST context
     * @return CallExpr for C function
     */
    clang::CallExpr* transformSubscriptCall(clang::CXXOperatorCallExpr* E,
                                            clang::ASTContext& Ctx);

    /**
     * @brief Transform call operator call to C function call
     * @param E CXXOperatorCallExpr for operator()
     * @param Ctx AST context
     * @return CallExpr for C function
     */
    clang::CallExpr* transformCallOperatorCall(clang::CXXOperatorCallExpr* E,
                                               clang::ASTContext& Ctx);

    /**
     * @brief Transform arrow operator call to C function call
     * @param E CXXOperatorCallExpr for operator->
     * @param Ctx AST context
     * @return CallExpr for C function
     */
    clang::CallExpr* transformArrowCall(clang::CXXOperatorCallExpr* E,
                                        clang::ASTContext& Ctx);

    /**
     * @brief Transform dereference operator call to C function call
     * @param E CXXOperatorCallExpr for operator*
     * @param Ctx AST context
     * @return CallExpr for C function
     */
    clang::CallExpr* transformDereferenceCall(clang::CXXOperatorCallExpr* E,
                                              clang::ASTContext& Ctx);

    /**
     * @brief Transform stream operator call to C function call
     * @param E CXXOperatorCallExpr for operator<< or operator>>
     * @param Ctx AST context
     * @return CallExpr for C function
     */
    clang::CallExpr* transformStreamCall(clang::CXXOperatorCallExpr* E,
                                         clang::ASTContext& Ctx);

    /**
     * @brief Transform assignment operator call to C function call
     * @param E CXXOperatorCallExpr for operator= (copy or move)
     * @param Ctx AST context
     * @return CallExpr for C function
     */
    clang::CallExpr* transformAssignmentCall(clang::CXXOperatorCallExpr* E,
                                             clang::ASTContext& Ctx);

    // ========================================================================
    // Utility Functions
    // ========================================================================

    /**
     * @brief Generate C function name for special operator
     * @param MD The operator method declaration
     * @return C function name (e.g., "Array_operator_subscript")
     */
    std::string generateOperatorName(const clang::CXXMethodDecl* MD);

    // Phase 53: Removed generateConversionName() - now using NameMangler::mangleConversionOperator()

    /**
     * @brief Check if operator<< or operator>> is a stream operator
     * @param E Operator call expression
     * @return true if stream operator (first param is ostream/istream)
     * @note Distinguishes from bitwise shift operators
     */
    bool isStreamOperator(clang::CXXOperatorCallExpr* E) const;

    /**
     * @brief Check if operator<< or operator>> is a bitwise shift operator
     * @param E Operator call expression
     * @return true if bitwise shift (first param is class type)
     */
    bool isBitwiseShiftOperator(clang::CXXOperatorCallExpr* E) const;

    /**
     * @brief Find or create C function for special operator
     * @param MD The C++ operator method
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return FunctionDecl for the C function
     *
     * Implements "get-or-create" pattern with m_methodMap cache
     */
    clang::FunctionDecl* findOrCreateFunction(const clang::CXXMethodDecl* MD,
                                              clang::ASTContext& Ctx,
                                              clang::TranslationUnitDecl* C_TU);

    /**
     * @brief Find or create C function for conversion operator
     * @param CD The C++ conversion operator
     * @param Ctx AST context
     * @param C_TU C translation unit
     * @return FunctionDecl for the C function
     */
    clang::FunctionDecl* findOrCreateConversionFunction(const clang::CXXConversionDecl* CD,
                                                        clang::ASTContext& Ctx,
                                                        clang::TranslationUnitDecl* C_TU);
};

#endif // SPECIAL_OPERATOR_TRANSLATOR_H
