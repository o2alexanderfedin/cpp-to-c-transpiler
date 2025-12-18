// exception_runtime.h - Exception handling runtime library header
// Story #81: Implement Exception Runtime Library
//
// This header provides the runtime API for C++ exception handling using
// the PNaCl-style SJLJ (setjmp/longjmp) pattern with action tables.
//
// SOLID Principles:
//   - Single Responsibility: Provides exception handling runtime interface
//   - Interface Segregation: Clean, minimal API for exception operations
//   - Dependency Inversion: Depends on standard C library abstractions

#ifndef __EXCEPTION_RUNTIME_H__
#define __EXCEPTION_RUNTIME_H__

#include <setjmp.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

// ============================================================================
// Exception Handling Data Structures
// ============================================================================

/// @brief Action table entry - describes one destructor to call during
/// unwinding
///
/// Action tables are static arrays that list all destructors to be called
/// during stack unwinding. Entries are in reverse construction order
/// (objects constructed last are destroyed first).
struct __cxx_action_entry {
  void (*destructor)(void *); ///< Destructor function pointer
  void *object;               ///< Object address to pass to destructor
};

/// @brief Exception frame - one per try block
///
/// Exception frames form a thread-local stack tracking active try blocks.
/// Each frame contains:
/// - setjmp buffer for non-local jump to catch handler
/// - Link to previous frame (stack linkage)
/// - Action table for destructor unwinding
/// - Current exception information (object and type)
struct __cxx_exception_frame {
  jmp_buf jmpbuf;                           ///< setjmp/longjmp state
  struct __cxx_exception_frame *next;       ///< Previous frame (stack linkage)
  const struct __cxx_action_entry *actions; ///< Destructor sequence
  void *exception_object;                   ///< Thrown exception object
  const char *exception_type; ///< Exception type (for catch matching)
};

// ============================================================================
// ACSL Predicate Definitions for Formal Verification
// ============================================================================

/*@ predicate valid_exception_frame(struct __cxx_exception_frame *f) =
        \valid(f) &&
        \valid(&f->jmpbuf);
*/

/*@ predicate valid_exception_stack(struct __cxx_exception_frame *stack) =
        stack == \null || valid_exception_frame(stack);
*/

// ============================================================================
// Thread-Local Exception Stack
// ============================================================================

/// @brief Thread-local exception frame stack
///
/// CRITICAL: Must be thread-local for thread-safe exception handling.
/// Each thread maintains its own independent exception frame stack.
/// Initialized to NULL (no active exception frames).
#ifdef __cplusplus
extern thread_local struct __cxx_exception_frame *__cxx_exception_stack;
#else
extern _Thread_local struct __cxx_exception_frame *__cxx_exception_stack;
#endif

// ============================================================================
// Runtime Functions
// ============================================================================

/// @brief Throw an exception and unwind the stack
///
/// This function implements the two-phase exception handling:
/// 1. UNWIND PHASE: Walk action table and call all destructors
/// 2. TRANSFER PHASE: longjmp to the catch handler
///
/// Behavior:
/// - If __cxx_exception_stack is NULL: abort (uncaught exception)
/// - Iterate action table and call each destructors
/// - Pop frame from exception stack
/// - Store exception_object and exception_type in frame
/// - longjmp to frame->jmpbuf (never returns)
///
/// @param exception Pointer to exception object (heap-allocated)
/// @param type_info Exception type name (for catch handler matching)
///
/// @note This function never returns - it performs longjmp to catch handler
/// @note Caller is responsible for allocating and constructing exception object
/*@ requires valid_exception: exception != \null;
    requires valid_type: type_info != \null && \valid_read(type_info);
    requires valid_stack: valid_exception_stack(__cxx_exception_stack);
    requires has_handler: __cxx_exception_stack != \null;
    ensures \false;  // Function never returns (longjmp)
    assigns *__cxx_exception_stack;
*/
void cxx_throw(void *exception, const char *type_info);

#ifdef __cplusplus
}
#endif

#endif // __EXCEPTION_RUNTIME_H__
