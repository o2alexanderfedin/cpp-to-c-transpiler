/**
 * @file SuspendPointIdentifier.h
 * @brief Story #103: Suspend Point Identification
 *
 * Identifies and classifies all suspend points in coroutines
 * (co_await, co_yield, co_return) with location and ordering information.
 */

#ifndef SUSPEND_POINT_IDENTIFIER_H
#define SUSPEND_POINT_IDENTIFIER_H

#include "clang/AST/AST.h"
#include <string>
#include <vector>

/**
 * @struct SuspendPoint
 * @brief Represents a single suspend point in a coroutine
 */
struct SuspendPoint {
    std::string kind;        // "co_await", "co_yield", or "co_return"
    unsigned int line;       // Line number in source
    unsigned int column;     // Column number in source
    unsigned int stateId;    // State machine state ID (0, 1, 2, ...)
    const clang::Stmt* stmt; // AST statement pointer
};

/**
 * @class SuspendPointIdentifier
 * @brief Identifies and analyzes suspend points in coroutines
 *
 * Suspend Point Types:
 * - co_await: Suspend until awaitable completes
 * - co_yield: Suspend and produce a value
 * - co_return: Final suspend and return
 *
 * State Numbering:
 * - State 0: Initial (function entry)
 * - State 1+: Each suspend point in execution order
 *
 * Example:
 * generator count_to(int n) {
 *     co_yield 1;  // State 1
 *     co_yield 2;  // State 2
 *     co_return;   // State 3 (final)
 * }
 *
 * Generated State Labels:
 * enum count_to_state {
 *     count_to_STATE_INITIAL = 0,
 *     count_to_STATE_SUSPEND_1,
 *     count_to_STATE_SUSPEND_2,
 *     count_to_STATE_SUSPEND_3
 * };
 */
class SuspendPointIdentifier {
public:
    /**
     * @brief Construct identifier with AST context
     * @param Context Clang AST context
     */
    explicit SuspendPointIdentifier(clang::ASTContext& Context);

    /**
     * @brief Identify all suspend points in a coroutine
     * @param FD Coroutine function
     * @return Vector of suspend points in execution order
     */
    std::vector<SuspendPoint> identifySuspendPoints(const clang::FunctionDecl* FD);

    /**
     * @brief Generate state enum labels for suspend points
     * @param FD Coroutine function
     * @return C code for state enum
     */
    std::string generateStateLabels(const clang::FunctionDecl* FD);

    /**
     * @brief Get total number of suspend points
     * @param FD Coroutine function
     * @return Count of suspend points
     */
    size_t getSuspendPointCount(const clang::FunctionDecl* FD);

private:
    /**
     * @brief Classify suspend point type
     * @param S Statement to classify
     * @return "co_await", "co_yield", "co_return", or empty string
     */
    std::string classifySuspendPoint(const clang::Stmt* S);

    /**
     * @brief Get source location info for statement
     * @param S Statement
     * @param line Output line number
     * @param column Output column number
     */
    void getLocation(const clang::Stmt* S, unsigned int& line, unsigned int& column);

    clang::ASTContext& Context;
};

#endif // SUSPEND_POINT_IDENTIFIER_H
