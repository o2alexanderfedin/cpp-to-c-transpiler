// resource_manager.h - C transpilation of C++ ResourceManager
// Transpiled from: tests/real-world/resource-manager/include/ResourceManager.h
//
// This file provides comprehensive resource management in C with ACSL annotations
// for formal verification. It transpiles advanced C++ features including:
// - Template metaprogramming (manually instantiated)
// - Smart pointers (unique_ptr, shared_ptr semantics)
// - RAII patterns (converted to explicit cleanup)
// - Move semantics (ownership transfer)
// - Custom deleters (function pointers)
// - Reference counting (with atomic-like semantics)
//
// ACSL annotations provide formal verification for:
// - Memory safety (no leaks, no double-frees)
// - Reference counting correctness
// - Resource ownership invariants
// - Exception safety guarantees (via error codes)

#ifndef RESOURCE_MANAGER_H
#define RESOURCE_MANAGER_H

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

// ============================================================================
// Error Codes (C++ exceptions → C error codes)
// ============================================================================

typedef enum {
    RESMAN_OK = 0,
    RESMAN_ERROR_NULL_POINTER,
    RESMAN_ERROR_INVALID_RESOURCE,
    RESMAN_ERROR_FILE_OPEN_FAILED,
    RESMAN_ERROR_FILE_NOT_OPEN,
    RESMAN_ERROR_POOL_EXHAUSTED,
    RESMAN_ERROR_POOL_CAPACITY,
    RESMAN_ERROR_INVALID_POOL_RESOURCE,
    RESMAN_ERROR_DOUBLE_FREE,
    RESMAN_ERROR_RESOURCE_ALREADY_RELEASED,
    RESMAN_ERROR_OUT_OF_MEMORY
} resman_error_t;

// Get error message for error code
const char* resman_error_message(resman_error_t error);

// ============================================================================
// ACSL Axiomatic Definitions - Global Predicates
// ============================================================================

/*@ axiomatic ResourceManagement {
  @   // Predicate: Pointer is either NULL or valid
  @   predicate valid_or_null{L}(void *ptr) =
  @     ptr == \null || \valid((char*)ptr);
  @
  @   // Predicate: Resource is owned (not NULL and valid)
  @   predicate owned{L}(void *resource) =
  @     resource != \null && \valid((char*)resource);
  @
  @   // Predicate: Reference count is valid (positive)
  @   predicate valid_refcount(int *count) =
  @     \valid(count) && *count > 0;
  @ }
  */

// ============================================================================
// Function Pointer Types for Custom Deleters
// ============================================================================

// Generic deleter function: void (*)(void*)
typedef void (*resman_deleter_fn)(void* resource);

// Type-specific deleters
/*@
  requires valid_or_null(resource);
  assigns \nothing;
  ensures \true;
*/
void resman_deleter_default(void* resource);

/*@
  requires valid_or_null(resource);
  assigns \nothing;
  ensures \true;
*/
void resman_deleter_file(void* resource);

/*@
  requires valid_or_null(resource);
  assigns \nothing;
  ensures \true;
*/
void resman_deleter_memory(void* resource);

/*@
  requires valid_or_null(resource);
  assigns \nothing;
  ensures \true;
*/
void resman_deleter_array(void* resource);

// ============================================================================
// Reference Counter (for SharedResource)
// ============================================================================

typedef struct resman_refcounter {
    int* count;  // Heap-allocated reference count
} resman_refcounter_t;

// ACSL predicate for valid reference counter
/*@
  predicate valid_refcounter(resman_refcounter_t *rc) =
    \valid(rc) &&
    (rc->count == \null || valid_refcount(rc->count));
*/

// Initialize new reference counter
/*@
  requires \valid(rc);
  assigns rc->count;
  ensures rc->count != \null;
  ensures valid_refcounter(rc);
  ensures \valid(rc->count) && *(rc->count) == 1;
*/
resman_error_t resman_refcounter_init(resman_refcounter_t* rc);

// Copy reference counter (increment count)
/*@
  requires \valid(dest);
  requires valid_refcounter(src);
  assigns dest->count, *src->count;
  ensures dest->count == src->count;
  ensures valid_refcounter(dest);
*/
resman_error_t resman_refcounter_copy(resman_refcounter_t* dest, const resman_refcounter_t* src);

// Move reference counter (transfer ownership, no count change)
/*@
  requires \valid(dest) && \valid(src);
  requires valid_refcounter(src);
  assigns dest->count, src->count;
  ensures src->count == \null;
  ensures valid_refcounter(dest);
*/
resman_error_t resman_refcounter_move(resman_refcounter_t* dest, resman_refcounter_t* src);

// Get current reference count
/*@
  requires valid_refcounter(rc);
  assigns \nothing;
  ensures rc->count == \null ==> \result == 0;
  ensures rc->count != \null ==> \result == *(rc->count);
  ensures \result >= 0;
*/
int resman_refcounter_count(const resman_refcounter_t* rc);

// Release reference (decrement, free if zero)
/*@
  requires \valid(rc);
  requires valid_refcounter(rc);
  assigns rc->count;
  ensures rc->count == \null;
*/
void resman_refcounter_release(resman_refcounter_t* rc);

// ============================================================================
// ResourceHandle (unique_ptr semantics) - Generic Version
// ============================================================================

typedef struct resman_resource_handle {
    void* resource;
    resman_deleter_fn deleter;
    bool owns;
} resman_resource_handle_t;

// ACSL predicate for valid resource handle
/*@
  predicate valid_resource_handle(resman_resource_handle_t *handle) =
    \valid(handle) &&
    \valid_function(handle->deleter) &&
    (handle->resource == \null || \valid((char*)handle->resource));
*/

// Initialize resource handle
/*@
  requires \valid(handle);
  requires valid_or_null(resource);
  requires \valid_function(deleter);
  assigns handle->resource, handle->deleter, handle->owns;
  ensures handle->resource == resource;
  ensures handle->deleter == deleter;
  ensures handle->owns == (resource != \null);
  ensures valid_resource_handle(handle);
*/
void resman_resource_handle_init(resman_resource_handle_t* handle,
                                  void* resource,
                                  resman_deleter_fn deleter);

// Destroy resource handle (calls deleter if owns resource)
/*@
  requires \valid(handle);
  requires valid_resource_handle(handle);
  assigns handle->resource, handle->owns;
  ensures handle->resource == \null;
  ensures handle->owns == false;
*/
void resman_resource_handle_destroy(resman_resource_handle_t* handle);

// Move resource handle (transfer ownership)
/*@
  requires \valid(dest) && \valid(src);
  requires valid_resource_handle(src);
  assigns dest->resource, dest->deleter, dest->owns,
          src->resource, src->owns;
  ensures src->resource == \null;
  ensures src->owns == false;
  ensures valid_resource_handle(dest);
*/
void resman_resource_handle_move(resman_resource_handle_t* dest,
                                  resman_resource_handle_t* src);

// Reset handle with new resource (deletes old resource)
/*@
  requires \valid(handle);
  requires valid_resource_handle(handle);
  requires valid_or_null(new_resource);
  assigns handle->resource, handle->owns;
  ensures handle->resource == new_resource;
  ensures handle->owns == (new_resource != \null);
*/
void resman_resource_handle_reset(resman_resource_handle_t* handle,
                                   void* new_resource);

// Release ownership without deleting
/*@
  requires \valid(handle);
  requires valid_resource_handle(handle);
  assigns handle->resource, handle->owns;
  ensures handle->resource == \null;
  ensures handle->owns == false;
*/
void* resman_resource_handle_release(resman_resource_handle_t* handle);

// Get resource pointer
/*@
  requires valid_resource_handle(handle);
  assigns \nothing;
  ensures \result == handle->resource;
*/
void* resman_resource_handle_get(const resman_resource_handle_t* handle);

// Check if handle owns a resource
/*@
  requires valid_resource_handle(handle);
  assigns \nothing;
  ensures \result == (handle->resource != \null);
*/
bool resman_resource_handle_is_valid(const resman_resource_handle_t* handle);

// Swap two handles
/*@
  requires \valid(h1) && \valid(h2);
  requires valid_resource_handle(h1);
  requires valid_resource_handle(h2);
  assigns h1->resource, h1->deleter, h1->owns,
          h2->resource, h2->deleter, h2->owns;
*/
void resman_resource_handle_swap(resman_resource_handle_t* h1,
                                  resman_resource_handle_t* h2);

// ============================================================================
// SharedResource (shared_ptr semantics)
// ============================================================================

typedef struct resman_shared_resource {
    void* resource;
    resman_refcounter_t refcount;
    resman_deleter_fn deleter;
} resman_shared_resource_t;

// ACSL predicate for valid shared resource
/*@
  predicate valid_shared_resource(resman_shared_resource_t *shared) =
    \valid(shared) &&
    \valid_function(shared->deleter) &&
    valid_refcounter(&shared->refcount) &&
    (shared->resource == \null || \valid((char*)shared->resource));
*/

// Initialize shared resource
/*@
  requires \valid(shared);
  requires valid_or_null(resource);
  requires \valid_function(deleter);
  assigns shared->resource, shared->deleter, shared->refcount;
  ensures shared->resource == resource;
  ensures shared->deleter == deleter;
  ensures valid_shared_resource(shared);
*/
resman_error_t resman_shared_resource_init(resman_shared_resource_t* shared,
                                            void* resource,
                                            resman_deleter_fn deleter);

// Destroy shared resource (decrements ref count, deletes if last)
/*@
  requires \valid(shared);
  requires valid_shared_resource(shared);
  assigns shared->resource, shared->refcount;
  ensures shared->resource == \null;
*/
void resman_shared_resource_destroy(resman_shared_resource_t* shared);

// Copy shared resource (increment reference count)
/*@
  requires \valid(dest) && \valid(src);
  requires valid_shared_resource(src);
  assigns dest->resource, dest->deleter, dest->refcount, *src->refcount.count;
  ensures dest->resource == src->resource;
  ensures dest->deleter == src->deleter;
  ensures dest->refcount.count == src->refcount.count;
  ensures valid_shared_resource(dest);
*/
resman_error_t resman_shared_resource_copy(resman_shared_resource_t* dest,
                                            const resman_shared_resource_t* src);

// Move shared resource (transfer ownership)
/*@
  requires \valid(dest) && \valid(src);
  requires valid_shared_resource(src);
  assigns dest->resource, dest->deleter, dest->refcount,
          src->resource, src->refcount;
  ensures src->resource == \null;
  ensures src->refcount.count == \null;
  ensures valid_shared_resource(dest);
*/
void resman_shared_resource_move(resman_shared_resource_t* dest,
                                  resman_shared_resource_t* src);

// Get resource pointer
/*@
  requires valid_shared_resource(shared);
  assigns \nothing;
  ensures \result == shared->resource;
*/
void* resman_shared_resource_get(const resman_shared_resource_t* shared);

// Get reference count
/*@
  requires valid_shared_resource(shared);
  assigns \nothing;
  ensures \result >= 0;
*/
int resman_shared_resource_use_count(const resman_shared_resource_t* shared);

// Check if shared resource is valid
/*@
  requires valid_shared_resource(shared);
  assigns \nothing;
  ensures \result == (shared->resource != \null);
*/
bool resman_shared_resource_is_valid(const resman_shared_resource_t* shared);

// ============================================================================
// ScopeGuard (RAII cleanup via GCC cleanup attribute)
// ============================================================================

typedef void (*resman_cleanup_fn)(void* user_data);

typedef struct resman_scope_guard {
    resman_cleanup_fn cleanup;
    void* user_data;
    bool active;
} resman_scope_guard_t;

// ACSL predicate for valid scope guard
/*@
  predicate valid_scope_guard(resman_scope_guard_t *guard) =
    \valid(guard) &&
    \valid_function(guard->cleanup) &&
    valid_or_null(guard->user_data);
*/

// Initialize scope guard
/*@
  requires \valid(guard);
  requires \valid_function(cleanup);
  requires valid_or_null(user_data);
  assigns guard->cleanup, guard->user_data, guard->active;
  ensures guard->cleanup == cleanup;
  ensures guard->user_data == user_data;
  ensures guard->active == true;
  ensures valid_scope_guard(guard);
*/
void resman_scope_guard_init(resman_scope_guard_t* guard,
                              resman_cleanup_fn cleanup,
                              void* user_data);

// Execute scope guard (calls cleanup if active)
/*@
  requires \valid(guard);
  requires valid_scope_guard(guard);
  assigns guard->active;
  ensures guard->active == false;
*/
void resman_scope_guard_execute(resman_scope_guard_t* guard);

// Dismiss scope guard (prevent cleanup)
/*@
  requires \valid(guard);
  requires valid_scope_guard(guard);
  assigns guard->active;
  ensures guard->active == false;
*/
void resman_scope_guard_dismiss(resman_scope_guard_t* guard);

// GCC cleanup attribute helper
/*@
  requires \valid(guard_ptr);
  requires valid_scope_guard(*guard_ptr);
  assigns (*guard_ptr)->active;
*/
void resman_scope_guard_cleanup_helper(resman_scope_guard_t** guard_ptr);

// Macro for automatic scope guard (GCC attribute)
#ifdef __GNUC__
#define RESMAN_SCOPE_GUARD(guard) \
    __attribute__((cleanup(resman_scope_guard_cleanup_helper))) resman_scope_guard_t* guard
#else
#define RESMAN_SCOPE_GUARD(guard) resman_scope_guard_t* guard
#endif

// ============================================================================
// FileResource (RAII wrapper for FILE*)
// ============================================================================

typedef struct resman_file_resource {
    resman_resource_handle_t handle;
    char* filename;
    char* mode;
} resman_file_resource_t;

// ACSL predicate for valid file resource
/*@
  predicate valid_file_resource(resman_file_resource_t *file) =
    \valid(file) &&
    valid_resource_handle(&file->handle) &&
    (file->filename == \null || \valid_read(file->filename)) &&
    (file->mode == \null || \valid_read(file->mode));
*/

// Open file resource
/*@
  requires \valid(file);
  requires \valid_read(filename);
  requires \valid_read(mode);
  assigns file->handle, file->filename, file->mode;
  ensures valid_file_resource(file);
*/
resman_error_t resman_file_resource_open(resman_file_resource_t* file,
                                          const char* filename,
                                          const char* mode);

// Close file resource
/*@
  requires \valid(file);
  requires valid_file_resource(file);
  assigns file->handle;
  ensures file->handle.resource == \null;
*/
void resman_file_resource_close(resman_file_resource_t* file);

// Destroy file resource (closes file, frees memory)
/*@
  requires \valid(file);
  requires valid_file_resource(file);
  assigns file->handle, file->filename, file->mode;
  ensures file->handle.resource == \null;
  ensures file->filename == \null;
  ensures file->mode == \null;
*/
void resman_file_resource_destroy(resman_file_resource_t* file);

// Get FILE* pointer
/*@
  requires valid_file_resource(file);
  assigns \nothing;
  ensures \result == file->handle.resource;
*/
FILE* resman_file_resource_get(const resman_file_resource_t* file);

// Check if file is open
/*@
  requires valid_file_resource(file);
  assigns \nothing;
  ensures \result == (file->handle.resource != \null);
*/
bool resman_file_resource_is_open(const resman_file_resource_t* file);

// Write string to file
/*@
  requires \valid(file);
  requires valid_file_resource(file);
  requires \valid_read(data);
  assigns *file->handle.resource;
*/
resman_error_t resman_file_resource_write(resman_file_resource_t* file,
                                           const char* data);

// Read all content from file
/*@
  requires \valid(file);
  requires valid_file_resource(file);
  requires \valid(out_buffer);
  requires \valid(out_size);
  assigns *file->handle.resource, *out_buffer, *out_size;
*/
resman_error_t resman_file_resource_read_all(resman_file_resource_t* file,
                                              char** out_buffer,
                                              size_t* out_size);

// ============================================================================
// MemoryPool (Template instantiated for generic type T)
// ============================================================================

// We'll create a type-erased memory pool that can work with any type
typedef struct resman_memory_pool_block {
    void* data;           // Pointer to actual data
    bool in_use;          // Is this block allocated?
    struct resman_memory_pool_block* next;  // Free list linkage
} resman_memory_pool_block_t;

typedef struct resman_memory_pool {
    resman_memory_pool_block_t** blocks;  // Array of blocks
    resman_memory_pool_block_t* free_list;  // Head of free list
    size_t capacity;      // Maximum number of blocks
    size_t used;          // Currently allocated blocks
    size_t element_size;  // Size of each element
} resman_memory_pool_t;

// ACSL predicate for valid memory pool
/*@
  predicate valid_memory_pool(resman_memory_pool_t *pool) =
    \valid(pool) &&
    pool->capacity > 0 &&
    pool->used <= pool->capacity &&
    pool->element_size > 0 &&
    \valid(pool->blocks + (0 .. pool->capacity - 1)) &&
    (pool->free_list == \null || \valid(pool->free_list));
*/

// Initialize memory pool
/*@
  requires \valid(pool);
  requires capacity > 0;
  requires element_size > 0;
  assigns pool->blocks, pool->free_list, pool->capacity,
          pool->used, pool->element_size;
  ensures pool->capacity == capacity;
  ensures pool->element_size == element_size;
  ensures pool->used == 0;
  ensures valid_memory_pool(pool);
  ensures \result == RESMAN_OK || \result == RESMAN_ERROR_OUT_OF_MEMORY;
*/
resman_error_t resman_memory_pool_init(resman_memory_pool_t* pool,
                                        size_t capacity,
                                        size_t element_size);

// Destroy memory pool (frees all blocks)
/*@
  requires \valid(pool);
  requires valid_memory_pool(pool);
  assigns pool->blocks, pool->free_list, pool->used;
  ensures pool->blocks == \null;
  ensures pool->free_list == \null;
  ensures pool->used == 0;
*/
void resman_memory_pool_destroy(resman_memory_pool_t* pool);

// Allocate element from pool
/*@
  requires \valid(pool);
  requires valid_memory_pool(pool);
  assigns pool->free_list, pool->used;
  ensures valid_memory_pool(pool);
*/
void* resman_memory_pool_allocate(resman_memory_pool_t* pool);

// Deallocate element back to pool
/*@
  requires \valid(pool);
  requires valid_memory_pool(pool);
  requires valid_or_null(ptr);
  assigns pool->free_list, pool->used;
  ensures valid_memory_pool(pool);
*/
resman_error_t resman_memory_pool_deallocate(resman_memory_pool_t* pool,
                                              void* ptr);

// Get pool statistics
/*@
  requires valid_memory_pool(pool);
  assigns \nothing;
  ensures \result == pool->capacity;
*/
size_t resman_memory_pool_capacity(const resman_memory_pool_t* pool);

/*@
  requires valid_memory_pool(pool);
  assigns \nothing;
  ensures \result == pool->used;
*/
size_t resman_memory_pool_used(const resman_memory_pool_t* pool);

/*@
  requires valid_memory_pool(pool);
  assigns \nothing;
  ensures \result == pool->capacity - pool->used;
*/
size_t resman_memory_pool_available(const resman_memory_pool_t* pool);

// ============================================================================
// ResourcePool (Generic pool for complex resources)
// ============================================================================

typedef struct resman_resource_pool {
    resman_resource_handle_t* resources;  // Array of owned resources
    void** available;     // Array of available resource pointers
    size_t capacity;      // Maximum resources
    size_t total;         // Total resources added
    size_t available_count;  // Number of available resources
} resman_resource_pool_t;

// ACSL predicate for valid resource pool
/*@
  predicate valid_resource_pool(resman_resource_pool_t *pool) =
    \valid(pool) &&
    pool->capacity > 0 &&
    pool->total <= pool->capacity &&
    pool->available_count <= pool->total &&
    \valid(pool->resources + (0 .. pool->capacity - 1)) &&
    \valid(pool->available + (0 .. pool->capacity - 1));
*/

// Initialize resource pool
/*@
  requires \valid(pool);
  requires capacity > 0;
  assigns pool->resources, pool->available, pool->capacity,
          pool->total, pool->available_count;
  ensures pool->capacity == capacity;
  ensures pool->total == 0;
  ensures pool->available_count == 0;
  ensures valid_resource_pool(pool);
  ensures \result == RESMAN_OK || \result == RESMAN_ERROR_OUT_OF_MEMORY;
*/
resman_error_t resman_resource_pool_init(resman_resource_pool_t* pool,
                                          size_t capacity);

// Destroy resource pool
/*@
  requires \valid(pool);
  requires valid_resource_pool(pool);
  assigns pool->resources, pool->available, pool->total, pool->available_count;
  ensures pool->resources == \null;
  ensures pool->available == \null;
  ensures pool->total == 0;
  ensures pool->available_count == 0;
*/
void resman_resource_pool_destroy(resman_resource_pool_t* pool);

// Add resource to pool (takes ownership)
/*@
  requires \valid(pool);
  requires valid_resource_pool(pool);
  requires valid_or_null(resource);
  requires \valid_function(deleter);
  assigns pool->resources, pool->available, pool->total, pool->available_count;
  ensures valid_resource_pool(pool);
*/
resman_error_t resman_resource_pool_add(resman_resource_pool_t* pool,
                                         void* resource,
                                         resman_deleter_fn deleter);

// Acquire resource from pool
/*@
  requires \valid(pool);
  requires valid_resource_pool(pool);
  assigns pool->available_count;
  ensures valid_resource_pool(pool);
*/
void* resman_resource_pool_acquire(resman_resource_pool_t* pool);

// Release resource back to pool
/*@
  requires \valid(pool);
  requires valid_resource_pool(pool);
  requires valid_or_null(resource);
  assigns pool->available, pool->available_count;
  ensures valid_resource_pool(pool);
*/
resman_error_t resman_resource_pool_release(resman_resource_pool_t* pool,
                                             void* resource);

// Get pool statistics
/*@
  requires valid_resource_pool(pool);
  assigns \nothing;
  ensures \result == pool->capacity;
*/
size_t resman_resource_pool_capacity(const resman_resource_pool_t* pool);

/*@
  requires valid_resource_pool(pool);
  assigns \nothing;
  ensures \result == pool->available_count;
*/
size_t resman_resource_pool_available(const resman_resource_pool_t* pool);

/*@
  requires valid_resource_pool(pool);
  assigns \nothing;
  ensures \result == pool->total - pool->available_count;
*/
size_t resman_resource_pool_in_use(const resman_resource_pool_t* pool);

// ============================================================================
// PooledResource (RAII wrapper for pooled resources)
// ============================================================================

typedef struct resman_pooled_resource {
    resman_resource_pool_t* pool;
    void* resource;
} resman_pooled_resource_t;

// ACSL predicate for valid pooled resource
/*@
  predicate valid_pooled_resource(resman_pooled_resource_t *pr) =
    \valid(pr) &&
    (pr->pool == \null || valid_resource_pool(pr->pool)) &&
    valid_or_null(pr->resource);
*/

// Acquire from pool (RAII constructor)
/*@
  requires \valid(pr);
  requires \valid(pool);
  requires valid_resource_pool(pool);
  assigns pr->pool, pr->resource, pool->available_count;
  ensures pr->pool == pool;
  ensures valid_pooled_resource(pr);
*/
resman_error_t resman_pooled_resource_acquire(resman_pooled_resource_t* pr,
                                               resman_resource_pool_t* pool);

// Release back to pool (RAII destructor)
/*@
  requires \valid(pr);
  requires valid_pooled_resource(pr);
  assigns pr->pool, pr->resource;
  ensures pr->pool == \null;
  ensures pr->resource == \null;
*/
void resman_pooled_resource_release(resman_pooled_resource_t* pr);

// Move pooled resource
/*@
  requires \valid(dest) && \valid(src);
  requires valid_pooled_resource(src);
  assigns dest->pool, dest->resource, src->pool, src->resource;
  ensures src->pool == \null;
  ensures src->resource == \null;
  ensures valid_pooled_resource(dest);
*/
void resman_pooled_resource_move(resman_pooled_resource_t* dest,
                                  resman_pooled_resource_t* src);

// Get resource pointer
/*@
  requires valid_pooled_resource(pr);
  assigns \nothing;
  ensures \result == pr->resource;
*/
void* resman_pooled_resource_get(const resman_pooled_resource_t* pr);

// ============================================================================
// Factory Functions (equivalent to makeResource, makeSharedResource, etc.)
// ============================================================================

// Create unique resource handle
/*@
  requires valid_or_null(resource);
  requires \valid_function(deleter);
  requires \valid(out_handle);
  assigns *out_handle;
  ensures valid_resource_handle(out_handle);
  ensures out_handle->resource == resource;
  ensures out_handle->deleter == deleter;
  ensures \result == RESMAN_OK;
*/
resman_error_t resman_make_resource(resman_resource_handle_t* out_handle,
                                     void* resource,
                                     resman_deleter_fn deleter);

// Create shared resource
/*@
  requires valid_or_null(resource);
  requires \valid_function(deleter);
  requires \valid(out_shared);
  assigns *out_shared;
  ensures valid_shared_resource(out_shared);
  ensures out_shared->resource == resource;
  ensures out_shared->deleter == deleter;
  ensures \result == RESMAN_OK;
*/
resman_error_t resman_make_shared_resource(resman_shared_resource_t* out_shared,
                                            void* resource,
                                            resman_deleter_fn deleter);

// Allocate array
/*@
  requires size > 0;
  requires element_size > 0;
  ensures \result == \null || \valid((char*)\result);
*/
void* resman_make_array(size_t size, size_t element_size);

#ifdef __cplusplus
}
#endif

#endif // RESOURCE_MANAGER_H
