/**
 * @file ConstexprEnhancementHandler.h
 * @brief Phase 6: Partial Constexpr Enhancement Support (C++23)
 *
 * Handles C++23 constexpr enhancements with compile-time evaluation for simple
 * cases and runtime fallback for complex cases. This provides partial support
 * for expanded constexpr capabilities in C++23.
 *
 * ## C++23 Feature: Constexpr Enhancements
 *
 * C++23 expands what can be done in constexpr contexts:
 * - Non-literal types in constexpr functions (limited support)
 * - Static constexpr variables with non-literal types
 * - Expanded constexpr allocation (not supported here)
 * - Relaxed constexpr restrictions
 *
 * ```cpp
 * // Simple constexpr (supported - compile-time evaluation)
 * constexpr int add(int a, int b) {
 *     return a + b;
 * }
 *
 * // Complex constexpr (partial support - runtime fallback)
 * constexpr std::vector<int> make_vec() {
 *     std::vector<int> v;
 *     v.push_back(1);
 *     return v;
 * }
 * ```
 *
 * ## Translation Strategy
 *
 * ### Simple Constexpr → Compile-Time Evaluation
 * ```cpp
 * constexpr int answer() {
 *     return 42;
 * }
 * ```
 * Becomes:
 * ```c
 * // Function eliminated, calls replaced with literal
 * #define answer() 42
 * ```
 *
 * ### Complex Constexpr → Runtime Function
 * ```cpp
 * constexpr int compute(int x) {
 *     int result = 0;
 *     for (int i = 0; i < x; i++) {
 *         result += i;
 *     }
 *     return result;
 * }
 * ```
 * Becomes:
 * ```c
 * int compute(int x) {
 *     int result = 0;
 *     for (int i = 0; i < x; i++) {
 *         result += i;
 *     }
 *     return result;
 * }
 * ```
 *
 * ## Implementation Architecture
 *
 * Conservative approach prioritizing correctness:
 * 1. **Detection**: Check FunctionDecl::isConstexpr()
 * 2. **Analysis**: Determine if function is "simple" (return literal)
 * 3. **Evaluation**: Attempt compile-time evaluation using Clang's evaluator
 * 4. **Fallback**: Emit runtime function if evaluation fails
 * 5. **Warning**: Log when falling back to runtime
 *
 * ## Design Principles
 *
 * - **SOLID**: Single Responsibility (only handles constexpr evaluation)
 * - **KISS**: Simple heuristics for detectability
 * - **DRY**: Reuses Clang's APValue evaluation infrastructure
 * - **YAGNI**: Implements what's feasible, documents limitations
 *
 * ## Limitations (Partial Support)
 *
 * - Only simple cases evaluated at compile-time
 * - Complex control flow → runtime fallback
 * - Non-literal types → runtime fallback
 * - Allocation/deallocation → runtime fallback
 * - Virtual functions → runtime fallback
 *
 * This is acceptable for Phase 6 - the goal is C++23 feature coverage,
 * not complete constexpr evaluation. Runtime fallback maintains correctness.
 *
 * ## References
 * - C++23 Constexpr Enhancements (multiple proposals)
 * - Clang APValue evaluation: https://clang.llvm.org/doxygen/APValue_8h.html
 * - Phase 6 Implementation Plan: .planning/phases/06-constexpr-enhancement/
 *
 * @see CppToCVisitor::VisitFunctionDecl for constexpr detection
 */

#ifndef CONSTEXPR_ENHANCEMENT_HANDLER_H
#define CONSTEXPR_ENHANCEMENT_HANDLER_H

#include "clang/AST/AST.h"
#include "clang/AST/Expr.h"
#include "CNodeBuilder.h"
#include <string>

/**
 * @enum ConstexprStrategy
 * @brief Strategy for handling a constexpr function
 */
enum class ConstexprStrategy {
    CompileTime,    ///< Evaluate at compile-time, replace with literal
    Runtime,        ///< Emit as runtime function (too complex)
    NotConstexpr    ///< Not a constexpr function
};

/**
 * @class ConstexprEnhancementHandler
 * @brief Handles C++23 constexpr enhancements with partial support
 *
 * This class attempts compile-time evaluation for simple constexpr functions
 * and falls back to runtime for complex cases, maintaining correctness while
 * providing best-effort optimization.
 *
 * ## Thread Safety
 * - No shared mutable state (safe for parallel translation units)
 * - CNodeBuilder owns AST node creation (thread-local ASTContext)
 *
 * ## Performance Characteristics
 * - Detection: O(1) per function declaration
 * - Simple analysis: O(n) where n = number of statements
 * - Evaluation: O(complexity) via Clang evaluator
 */
class ConstexprEnhancementHandler {
public:
    /**
     * @brief Construct handler with C AST builder
     * @param Builder CNodeBuilder for creating C AST nodes
     */
    explicit ConstexprEnhancementHandler(clang::CNodeBuilder& Builder);

    /**
     * @brief Handle constexpr function declaration
     * @param FD Function declaration (may be constexpr)
     * @param Ctx Clang AST context
     * @return true if function was handled (compile-time or runtime), false if not constexpr
     *
     * This method is called when CppToCVisitor encounters a function declaration.
     * If the function is constexpr, it determines the appropriate strategy:
     * - CompileTime: Simple function, can be evaluated and inlined
     * - Runtime: Complex function, emit as normal C function
     *
     * Example:
     * ```cpp
     * // Input C++ AST
     * constexpr int answer() { return 42; }
     *
     * // Strategy: CompileTime
     * // Calls to answer() will be replaced with literal 42
     * ```
     *
     * @note Returns false if function is not constexpr (no action taken)
     */
    bool handleConstexprFunction(clang::FunctionDecl* FD,
                                 clang::ASTContext& Ctx);

    /**
     * @brief Get strategy for handling a constexpr function
     * @param FD Function declaration
     * @param Ctx AST context
     * @return Strategy recommendation
     *
     * Analyzes function to determine if it's simple enough for compile-time
     * evaluation or requires runtime fallback.
     */
    ConstexprStrategy determineStrategy(clang::FunctionDecl* FD,
                                       clang::ASTContext& Ctx);

    /**
     * @brief Check if function call can be evaluated at compile-time
     * @param Call CallExpr to potentially evaluate
     * @param Ctx AST context
     * @return true if call was evaluated and replaced
     *
     * Called when visiting CallExpr nodes. If the callee is a simple constexpr
     * function, attempts to evaluate and replace with literal.
     */
    bool tryEvaluateCall(clang::CallExpr* Call,
                        clang::ASTContext& Ctx);

private:
    clang::CNodeBuilder& m_builder;

    /**
     * @brief Detect if function uses C++23 constexpr features
     * @param FD Function declaration
     * @return true if function uses C++23-specific constexpr features
     *
     * Checks for:
     * - Non-literal return types
     * - Static variables with non-literal types
     * - Other C++23 relaxations
     */
    bool detectC23ConstexprFeatures(clang::FunctionDecl* FD);

    /**
     * @brief Attempt compile-time evaluation of function
     * @param FD Function declaration to evaluate
     * @param Result Output parameter for evaluation result
     * @param Ctx AST context
     * @return true if evaluation succeeded
     *
     * Uses Clang's APValue evaluation infrastructure to attempt compile-time
     * evaluation. Returns false if function is too complex or evaluation fails.
     */
    bool attemptCompileTimeEval(clang::FunctionDecl* FD,
                               clang::Expr::EvalResult& Result,
                               clang::ASTContext& Ctx);

    /**
     * @brief Check if function is simple return of literal
     * @param FD Function declaration
     * @return true if function body is just "return <literal>;"
     *
     * Heuristic for detectability:
     * - Single return statement
     * - Return value is literal (IntegerLiteral, FloatingLiteral, etc.)
     * - No parameters (or all parameters unused)
     */
    bool isSimpleReturnLiteral(clang::FunctionDecl* FD);

    /**
     * @brief Check if statement contains only literals
     * @param S Statement to check
     * @return true if statement is free of non-literal expressions
     *
     * Recursive check for:
     * - IntegerLiteral, FloatingLiteral, StringLiteral → true
     * - DeclRefExpr, CallExpr, etc. → false
     */
    bool isLiteralOnly(clang::Stmt* S);

    /**
     * @brief Generate warning for runtime fallback
     * @param FD Function declaration
     * @param Reason Reason for fallback
     *
     * Emits diagnostic message when constexpr function cannot be evaluated
     * at compile-time and will be emitted as runtime function.
     */
    void emitFallbackWarning(clang::FunctionDecl* FD,
                            const std::string& Reason);

    /**
     * @brief Replace function call with evaluated literal
     * @param Call Original call expression
     * @param Result Evaluation result (APValue)
     * @param Ctx AST context
     * @return Literal expression replacing the call
     */
    clang::Expr* createLiteralFromAPValue(clang::CallExpr* Call,
                                         const clang::APValue& Result,
                                         clang::ASTContext& Ctx);
};

#endif // CONSTEXPR_ENHANCEMENT_HANDLER_H
