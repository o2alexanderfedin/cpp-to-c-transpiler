// exception_runtime.c - Exception handling runtime library implementation
// Story #81: Implement Exception Runtime Library
//
// This file implements the core exception handling runtime for C++ to C
// transpilation using the PNaCl-style SJLJ (setjmp/longjmp) pattern with action
// tables.
//
// Total size: ~800-1200 bytes (as specified in requirements)
//
// SOLID Principles:
//   - Single Responsibility: Implements exception throwing and unwinding
//   - KISS: Simple, straightforward implementation following proven pattern
//   - DRY: No code duplication

#include "exception_runtime.h"
#include <stdio.h>
#include <stdlib.h>

// ============================================================================
// Thread-Local Exception Stack Definition
// ============================================================================

// Note: When compiling as C++, we need to use C linkage to ensure
// the thread_local variable is accessible from both C and C++ code.
// The C version uses _Thread_local, C++ uses thread_local.

#ifdef __cplusplus
// C++ version - use thread_local with C linkage
extern "C" {
thread_local struct __cxx_exception_frame *__cxx_exception_stack = nullptr;
}
#else
// C version - use _Thread_local
_Thread_local struct __cxx_exception_frame *__cxx_exception_stack = NULL;
#endif

// ============================================================================
// Runtime Functions Implementation
// ============================================================================

/// @brief Throw an exception and unwind the stack
///
/// This function implements the two-phase exception handling:
/// 1. UNWIND PHASE: Walk action table and call all destructors
/// 2. TRANSFER PHASE: longjmp to the catch handler
///
/// Implementation follows the PNaCl SJLJ pattern:
/// - Check for uncaught exception (null stack)
/// - Execute action table (call destructors in sequence)
/// - Pop frame from exception stack
/// - Store exception info in frame
/// - Perform longjmp to catch handler
///
/// @param exception Pointer to exception object (heap-allocated)
/// @param type_info Exception type name (for catch handler matching)
///
/// @note This function never returns - it performs longjmp to catch handler
void cxx_throw(void *exception, const char *type_info) {
  // Get current exception frame from thread-local stack
  struct __cxx_exception_frame *frame = __cxx_exception_stack;

  // AC #5: Uncaught exception handling
  // If no exception frame is active, we have an uncaught exception
  if (frame == NULL) {
    fprintf(stderr, "Uncaught exception: %s\n", type_info);
    abort();
  }

  // AC #2: Action table execution
  // Walk the action table and call each destructor in sequence
  // Action tables list destructors in reverse construction order
  const struct __cxx_action_entry *action = frame->actions;
  if (action != NULL) {
    while (action->destructor != NULL) {
      // Call destructor with object address
      action->destructor(action->object);
      action++;
    }
  }

  // AC #3: Stack unwinding - pop frame from exception stack
  // This restores the previous exception frame before we jump
  __cxx_exception_stack = frame->next;

  // AC #4: Exception storage - store exception info in frame
  // The catch handler will read these fields after longjmp
  frame->exception_object = exception;
  frame->exception_type = type_info;

  // AC #1: Perform longjmp to catch handler
  // The second argument (1) becomes the return value of setjmp
  // This transfers control to the catch handler
  longjmp(frame->jmpbuf, 1);

  // Never reached - longjmp does not return
}
