/**
 * @file CoroutineDetector.h
 * @brief Story #102: Coroutine Detection and Frame Structure Generation
 *
 * Detects C++20 coroutines (co_await, co_yield, co_return) and generates
 * coroutine frame structures for state machine transformation.
 */

#ifndef COROUTINE_DETECTOR_H
#define COROUTINE_DETECTOR_H

#include "clang/AST/AST.h"
#include <string>
#include <vector>

/**
 * @class CoroutineDetector
 * @brief Detects coroutines and generates frame structures
 *
 * Coroutine Frame Structure:
 * struct FunctionName_frame {
 *     int state;                    // Current suspend point (0, 1, 2, ...)
 *     void (*resume_fn)(void*);     // Resume function pointer
 *     void (*destroy_fn)(void*);    // Destroy function pointer
 *     PromiseType promise;          // Promise object
 *     ParamType param1;             // Copied parameters
 *     LocalType local1;             // Locals spanning suspend points
 * };
 *
 * Detection:
 * - Checks for CoroutineBodyStmt in function AST
 * - Identifies co_await, co_yield, co_return expressions
 *
 * Example:
 * generator count_to(int n) {
 *     for (int i = 0; i < n; ++i) {
 *         co_yield i;  // Suspend point
 *     }
 * }
 *
 * Generates:
 * struct count_to_frame {
 *     int state;
 *     void (*resume_fn)(void*);
 *     void (*destroy_fn)(void*);
 *     generator_promise_type promise;
 *     int n;  // Parameter
 *     int i;  // Local spanning suspends
 * };
 */
class CoroutineDetector {
public:
    /**
     * @brief Construct detector with AST context
     * @param Context Clang AST context
     */
    explicit CoroutineDetector(clang::ASTContext& Context);

    /**
     * @brief Check if function is a coroutine
     * @param FD Function to check
     * @return true if function contains co_await/co_yield/co_return
     */
    bool isCoroutine(const clang::FunctionDecl* FD) const;

    /**
     * @brief Generate coroutine frame structure
     * @param FD Coroutine function
     * @return C code for frame struct
     */
    std::string generateFrameStructure(const clang::FunctionDecl* FD);

    /**
     * @brief Count suspend points in coroutine
     * @param FD Coroutine function
     * @return Number of co_await/co_yield/co_return points
     */
    size_t countSuspendPoints(const clang::FunctionDecl* FD) const;

    /**
     * @brief Get frame structure name for coroutine
     * @param FD Coroutine function
     * @return Frame struct name (e.g., "count_to_frame")
     */
    std::string getFrameName(const clang::FunctionDecl* FD) const;

private:
    /**
     * @brief Generate state enum for suspend points
     * @param FD Coroutine function
     * @param suspendCount Number of suspend points
     * @return C code for state enum
     */
    std::string generateStateEnum(const clang::FunctionDecl* FD, size_t suspendCount);

    /**
     * @brief Generate parameter fields in frame
     * @param FD Coroutine function
     * @return C code for parameter fields
     */
    std::string generateParameterFields(const clang::FunctionDecl* FD);

    /**
     * @brief Get C type string from Clang QualType
     * @param Type Clang type
     * @return C type string
     */
    std::string getTypeString(clang::QualType Type);

    clang::ASTContext& Context;
};

#endif // COROUTINE_DETECTOR_H
