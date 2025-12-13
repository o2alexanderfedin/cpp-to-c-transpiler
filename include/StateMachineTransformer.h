/**
 * @file StateMachineTransformer.h
 * @brief Story #104: State Machine Transformation
 *
 * Transforms coroutine bodies into switch-based state machines
 * where each suspend point becomes a case label.
 */

#ifndef STATE_MACHINE_TRANSFORMER_H
#define STATE_MACHINE_TRANSFORMER_H

#include "clang/AST/AST.h"
#include "SuspendPointIdentifier.h"
#include <string>
#include <vector>

/**
 * @class StateMachineTransformer
 * @brief Transforms coroutines into C state machines
 *
 * Transformation Pattern:
 *
 * C++ Coroutine:
 * generator count_to(int n) {
 *     for (int i = 0; i < n; ++i) {
 *         co_yield i;
 *     }
 * }
 *
 * Transformed C State Machine:
 * void count_to_resume(void* frame_ptr) {
 *     struct count_to_frame* frame = (struct count_to_frame*)frame_ptr;
 *
 *     switch (frame->state) {
 *         case 0:  // Initial state
 *             frame->i = 0;
 *             goto suspend_1;
 *
 *         case 1:  // Resume after first yield
 *             frame->i++;
 *             if (frame->i < frame->n) goto suspend_1;
 *             goto final;
 *
 *         suspend_1:
 *             frame->promise.value = frame->i;
 *             frame->state = 1;
 *             return;  // Suspend
 *
 *         final:
 *             frame->state = -1;  // Done
 *             return;
 *     }
 * }
 *
 * Key Transformations:
 * 1. Function body wrapped in switch(state)
 * 2. Each suspend point gets a unique case label
 * 3. Local variables moved to frame structure
 * 4. State saved before each suspend/return
 * 5. Execution resumes at previous suspend point
 */
class StateMachineTransformer {
public:
    /**
     * @brief Construct transformer with AST context
     * @param Context Clang AST context
     */
    explicit StateMachineTransformer(clang::ASTContext& Context);

    /**
     * @brief Transform coroutine to state machine
     * @param FD Coroutine function
     * @return C code for state machine
     */
    std::string transformToStateMachine(const clang::FunctionDecl* FD);

    /**
     * @brief Generate resume function
     * @param FD Coroutine function
     * @return C code for resume function
     */
    std::string generateResumeFunction(const clang::FunctionDecl* FD);

    /**
     * @brief Generate destroy function
     * @param FD Coroutine function
     * @return C code for destroy function
     */
    std::string generateDestroyFunction(const clang::FunctionDecl* FD);

private:
    /**
     * @brief Generate switch statement wrapper
     * @param FD Coroutine function
     * @param suspendPoints Suspend points to handle
     * @return Switch statement code
     */
    std::string generateSwitchStatement(const clang::FunctionDecl* FD,
                                       const std::vector<SuspendPoint>& suspendPoints);

    /**
     * @brief Generate case label for suspend point
     * @param sp Suspend point
     * @param FD Function declaration
     * @return Case label code
     */
    std::string generateCaseLabel(const SuspendPoint& sp, const clang::FunctionDecl* FD);

    /**
     * @brief Extract code segment between suspend points
     * @param start Start statement
     * @param end End statement
     * @return Code between start and end
     */
    std::string extractCodeSegment(const clang::Stmt* start, const clang::Stmt* end);

    /**
     * @brief Generate state save code
     * @param stateId State ID to save
     * @return State assignment code
     */
    std::string generateStateSave(unsigned int stateId);

    clang::ASTContext& Context;
    SuspendPointIdentifier Identifier;
};

#endif // STATE_MACHINE_TRANSFORMER_H
