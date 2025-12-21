// memory_runtime.h - Memory management runtime library header
// Story #116: Implement Inline Runtime Mode
//
// This header provides runtime memory management for C++ features including
// coroutine frames and heap allocation wrappers.
//
// SOLID Principles:
//   - Single Responsibility: Provides memory management runtime interface
//   - Interface Segregation: Clean, minimal API for memory operations
//   - Dependency Inversion: Depends on standard C library abstractions

#ifndef __MEMORY_RUNTIME_H__
#define __MEMORY_RUNTIME_H__

#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif

// ============================================================================
// Memory Management Functions
// ============================================================================

/// @brief Allocate memory with alignment requirements
/// @param size Number of bytes to allocate
/// @param alignment Required alignment (must be power of 2)
/// @return Pointer to allocated memory, or NULL on failure
///
/// This function allocates memory with specified alignment requirements,
/// commonly needed for coroutine frames and aligned data structures.
/*@ requires size_valid: size > 0;
    requires align_valid: alignment > 0 && (alignment & (alignment - 1)) == 0;
    ensures valid_result: \result == \null || \valid((char*)\result + (0..size-1));
    ensures aligned_result: \result == \null || ((size_t)\result % alignment) == 0;
    assigns \nothing;
*/
static inline void *__cxx_allocate(size_t size, size_t alignment) {
  // Simple aligned allocation using malloc and alignment padding
  void *ptr = malloc(size + alignment);
  if (!ptr) return NULL;

  // Align pointer to required boundary
  size_t addr = (size_t)ptr;
  size_t aligned = (addr + alignment - 1) & ~(alignment - 1);
  return (void*)aligned;
}

/// @brief Free memory allocated by __cxx_allocate
/// @param ptr Pointer to memory to free
///
/// Frees memory previously allocated by __cxx_allocate.
/*@ requires valid_ptr: ptr == \null || \freeable(ptr);
    assigns \nothing;
    ensures \allocable(ptr);
*/
static inline void __cxx_deallocate(void *ptr) {
  if (ptr) {
    free(ptr);
  }
}

/// @brief Zero-initialize memory region
/// @param ptr Pointer to memory region
/// @param size Number of bytes to zero
///
/// Initializes a memory region to all zeros.
/*@ requires valid_region: ptr != \null && \valid((char*)ptr + (0..size-1));
    requires size_valid: size > 0;
    ensures zeroed: \forall integer i; 0 <= i < size ==> ((char*)ptr)[i] == 0;
    assigns ((char*)ptr)[0..size-1];
*/
static inline void __cxx_zero_memory(void *ptr, size_t size) {
  memset(ptr, 0, size);
}

#ifdef __cplusplus
}
#endif

#endif // __MEMORY_RUNTIME_H__
