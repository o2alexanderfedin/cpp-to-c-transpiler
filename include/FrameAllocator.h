/**
 * @file FrameAllocator.h
 * @brief Story #107: Frame Allocation and Coroutine Handle
 *
 * Generates heap allocation for coroutine frames and coroutine handle operations.
 */

#ifndef FRAME_ALLOCATOR_H
#define FRAME_ALLOCATOR_H

#include "clang/AST/AST.h"
#include <string>

/**
 * @class FrameAllocator
 * @brief Generates frame allocation and coroutine handle code
 *
 * Translation Pattern:
 *
 * C++ Coroutine Creation:
 * task coro(int x) {
 *     co_return;
 * }
 *
 * Translated C Frame Allocation:
 * struct task coro(int x) {
 *     // Allocate frame on heap
 *     struct coro_frame* frame = (struct coro_frame*)
 *         malloc(sizeof(struct coro_frame));
 *
 *     // Initialize frame
 *     frame->state = 0;
 *     frame->resume_fn = (void(*)(void*))coro_resume;
 *     frame->destroy_fn = (void(*)(void*))coro_destroy;
 *
 *     // Copy parameters to frame
 *     frame->x = x;
 *
 *     // Return coroutine handle
 *     struct task handle;
 *     handle.frame = frame;
 *     return handle;
 * }
 *
 * Coroutine Handle Operations:
 * void task_resume(struct task* handle) {
 *     if (handle->frame) {
 *         coro_resume(handle->frame);
 *     }
 * }
 *
 * void task_destroy(struct task* handle) {
 *     if (handle->frame) {
 *         coro_destroy(handle->frame);
 *         handle->frame = NULL;
 *     }
 * }
 *
 * Key Transformations:
 * 1. Allocate coroutine frame on heap
 * 2. Initialize frame state and function pointers
 * 3. Copy parameters to frame
 * 4. Return coroutine handle
 * 5. Generate resume/destroy operations
 */
class FrameAllocator {
public:
    /**
     * @brief Construct allocator with AST context
     * @param Context Clang AST context
     */
    explicit FrameAllocator(clang::ASTContext& Context);

    /**
     * @brief Generate frame allocation code
     * @param FD Coroutine function
     * @return C code for frame allocation
     */
    std::string generateFrameAllocation(const clang::FunctionDecl* FD);

    /**
     * @brief Generate coroutine handle structure
     * @param FD Coroutine function
     * @return C struct for coroutine handle
     */
    std::string generateCoroutineHandle(const clang::FunctionDecl* FD);

    /**
     * @brief Generate resume operation
     * @param FD Coroutine function
     * @return C code for resume operation
     */
    std::string generateResumeOperation(const clang::FunctionDecl* FD);

    /**
     * @brief Generate destroy operation
     * @param FD Coroutine function
     * @return C code for destroy operation
     */
    std::string generateDestroyOperation(const clang::FunctionDecl* FD);

    /**
     * @brief Generate frame initialization code
     * @param FD Coroutine function
     * @return C code for frame initialization
     */
    std::string generateFrameInitialization(const clang::FunctionDecl* FD);

    /**
     * @brief Generate handle return code
     * @param FD Coroutine function
     * @return C code for returning handle
     */
    std::string generateHandleReturn(const clang::FunctionDecl* FD);

private:
    /**
     * @brief Get frame type name
     * @param FD Coroutine function
     * @return Frame struct name
     */
    std::string getFrameTypeName(const clang::FunctionDecl* FD);

    /**
     * @brief Get handle type name
     * @param FD Coroutine function
     * @return Handle struct name
     */
    std::string getHandleTypeName(const clang::FunctionDecl* FD);

    clang::ASTContext& Context;
};

#endif // FRAME_ALLOCATOR_H
