// resource_manager.c - Implementation of C resource manager
// Transpiled from: tests/real-world/resource-manager/include/ResourceManager.h
//
// This file implements all resource management functions with comprehensive
// ACSL annotations for formal verification.

#include "resource_manager.h"
#include <assert.h>

// ============================================================================
// Error Messages
// ============================================================================

/*@
  requires 0 <= error < 12;
  assigns \nothing;
  ensures \valid_read(\result);
*/
const char* resman_error_message(resman_error_t error) {
    static const char* messages[] = {
        "Success",
        "Null pointer error",
        "Invalid resource",
        "File open failed",
        "File not open",
        "Memory pool exhausted",
        "Resource pool at capacity",
        "Invalid pool resource",
        "Double free detected",
        "Resource already released",
        "Out of memory"
    };

    if (error < 0 || error >= sizeof(messages) / sizeof(messages[0])) {
        return "Unknown error";
    }
    return messages[error];
}

// ============================================================================
// Custom Deleters Implementation
// ============================================================================

/*@
  requires valid_or_null(resource);
  assigns \nothing;
*/
void resman_deleter_default(void* resource) {
    if (resource) {
        free(resource);
    }
}

/*@
  requires valid_or_null(resource);
  assigns \nothing;
*/
void resman_deleter_file(void* resource) {
    if (resource) {
        FILE* file = (FILE*)resource;
        fclose(file);
    }
}

/*@
  requires valid_or_null(resource);
  assigns \nothing;
*/
void resman_deleter_memory(void* resource) {
    if (resource) {
        free(resource);
    }
}

/*@
  requires valid_or_null(resource);
  assigns \nothing;
*/
void resman_deleter_array(void* resource) {
    if (resource) {
        free(resource);
    }
}

// ============================================================================
// Reference Counter Implementation
// ============================================================================

/*@
  requires \valid(rc);
  assigns rc->count;
  ensures rc->count != \null ==> *(rc->count) == 1;
  ensures valid_refcounter(rc);
*/
resman_error_t resman_refcounter_init(resman_refcounter_t* rc) {
    if (!rc) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    rc->count = (int*)malloc(sizeof(int));
    if (!rc->count) {
        return RESMAN_ERROR_OUT_OF_MEMORY;
    }

    *(rc->count) = 1;
    return RESMAN_OK;
}

/*@
  requires \valid(dest);
  requires valid_refcounter(src);
  assigns dest->count, *src->count;
  ensures dest->count == src->count;
  ensures src->count != \null ==> *(dest->count) == \old(*(src->count)) + 1;
*/
resman_error_t resman_refcounter_copy(resman_refcounter_t* dest,
                                       const resman_refcounter_t* src) {
    if (!dest || !src) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    dest->count = src->count;
    if (dest->count) {
        (*(dest->count))++;
    }

    return RESMAN_OK;
}

/*@
  requires \valid(dest) && \valid(src);
  requires valid_refcounter(src);
  assigns dest->count, src->count;
  ensures dest->count == \old(src->count);
  ensures src->count == \null;
*/
resman_error_t resman_refcounter_move(resman_refcounter_t* dest,
                                       resman_refcounter_t* src) {
    if (!dest || !src) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    dest->count = src->count;
    src->count = NULL;

    return RESMAN_OK;
}

/*@
  requires valid_refcounter(rc);
  assigns \nothing;
  ensures rc->count == \null ==> \result == 0;
  ensures rc->count != \null ==> \result == *(rc->count);
*/
int resman_refcounter_count(const resman_refcounter_t* rc) {
    if (!rc || !rc->count) {
        return 0;
    }
    return *(rc->count);
}

/*@
  requires \valid(rc);
  requires valid_refcounter(rc);
  assigns rc->count;
  ensures rc->count == \null;
*/
void resman_refcounter_release(resman_refcounter_t* rc) {
    if (!rc || !rc->count) {
        return;
    }

    (*(rc->count))--;
    if (*(rc->count) == 0) {
        free(rc->count);
    }
    rc->count = NULL;
}

// ============================================================================
// ResourceHandle Implementation
// ============================================================================

/*@
  requires \valid(handle);
  requires valid_or_null(resource);
  requires \valid_function(deleter);
  assigns handle->resource, handle->deleter, handle->owns;
  ensures valid_resource_handle(handle);
*/
void resman_resource_handle_init(resman_resource_handle_t* handle,
                                  void* resource,
                                  resman_deleter_fn deleter) {
    assert(handle != NULL);
    assert(deleter != NULL);

    handle->resource = resource;
    handle->deleter = deleter;
    handle->owns = (resource != NULL);
}

/*@
  requires \valid(handle);
  requires valid_resource_handle(handle);
  assigns handle->resource, handle->owns;
  ensures handle->resource == \null;
  ensures handle->owns == false;
*/
void resman_resource_handle_destroy(resman_resource_handle_t* handle) {
    if (!handle) {
        return;
    }

    if (handle->resource && handle->owns && handle->deleter) {
        handle->deleter(handle->resource);
    }

    handle->resource = NULL;
    handle->owns = false;
}

/*@
  requires \valid(dest) && \valid(src);
  requires valid_resource_handle(src);
  assigns dest->resource, dest->deleter, dest->owns,
          src->resource, src->owns;
  ensures dest->resource == \old(src->resource);
  ensures dest->deleter == \old(src->deleter);
  ensures dest->owns == \old(src->owns);
  ensures src->resource == \null;
  ensures src->owns == false;
*/
void resman_resource_handle_move(resman_resource_handle_t* dest,
                                  resman_resource_handle_t* src) {
    assert(dest != NULL);
    assert(src != NULL);

    dest->resource = src->resource;
    dest->deleter = src->deleter;
    dest->owns = src->owns;

    src->resource = NULL;
    src->owns = false;
}

/*@
  requires \valid(handle);
  requires valid_resource_handle(handle);
  requires valid_or_null(new_resource);
  assigns handle->resource, handle->owns;
  ensures handle->resource == new_resource;
*/
void resman_resource_handle_reset(resman_resource_handle_t* handle,
                                   void* new_resource) {
    assert(handle != NULL);

    // Delete current resource if owned
    if (handle->resource && handle->owns && handle->deleter) {
        handle->deleter(handle->resource);
    }

    handle->resource = new_resource;
    handle->owns = (new_resource != NULL);
}

/*@
  requires \valid(handle);
  requires valid_resource_handle(handle);
  assigns handle->resource, handle->owns;
  ensures \result == \old(handle->resource);
  ensures handle->resource == \null;
  ensures handle->owns == false;
*/
void* resman_resource_handle_release(resman_resource_handle_t* handle) {
    assert(handle != NULL);

    void* temp = handle->resource;
    handle->resource = NULL;
    handle->owns = false;
    return temp;
}

/*@
  requires valid_resource_handle(handle);
  assigns \nothing;
  ensures \result == handle->resource;
*/
void* resman_resource_handle_get(const resman_resource_handle_t* handle) {
    if (!handle) {
        return NULL;
    }
    return handle->resource;
}

/*@
  requires valid_resource_handle(handle);
  assigns \nothing;
  ensures \result == (handle->resource != \null);
*/
bool resman_resource_handle_is_valid(const resman_resource_handle_t* handle) {
    return handle && handle->resource != NULL;
}

/*@
  requires \valid(h1) && \valid(h2);
  requires valid_resource_handle(h1);
  requires valid_resource_handle(h2);
  assigns h1->resource, h1->deleter, h1->owns,
          h2->resource, h2->deleter, h2->owns;
*/
void resman_resource_handle_swap(resman_resource_handle_t* h1,
                                  resman_resource_handle_t* h2) {
    assert(h1 != NULL);
    assert(h2 != NULL);

    void* temp_resource = h1->resource;
    resman_deleter_fn temp_deleter = h1->deleter;
    bool temp_owns = h1->owns;

    h1->resource = h2->resource;
    h1->deleter = h2->deleter;
    h1->owns = h2->owns;

    h2->resource = temp_resource;
    h2->deleter = temp_deleter;
    h2->owns = temp_owns;
}

// ============================================================================
// SharedResource Implementation
// ============================================================================

/*@
  requires \valid(shared);
  requires valid_or_null(resource);
  requires \valid_function(deleter);
  assigns shared->resource, shared->deleter, shared->refcount;
  ensures valid_shared_resource(shared);
*/
resman_error_t resman_shared_resource_init(resman_shared_resource_t* shared,
                                            void* resource,
                                            resman_deleter_fn deleter) {
    if (!shared || !deleter) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    shared->resource = resource;
    shared->deleter = deleter;

    if (resource != NULL) {
        resman_error_t err = resman_refcounter_init(&shared->refcount);
        if (err != RESMAN_OK) {
            return err;
        }
    } else {
        shared->refcount.count = NULL;
    }

    return RESMAN_OK;
}

/*@
  requires \valid(shared);
  requires valid_shared_resource(shared);
  assigns shared->resource, shared->refcount;
  ensures shared->resource == \null;
*/
void resman_shared_resource_destroy(resman_shared_resource_t* shared) {
    if (!shared) {
        return;
    }

    // Check if we're the last reference
    if (shared->resource && shared->refcount.count && *(shared->refcount.count) == 1) {
        // Last reference - delete the resource
        if (shared->deleter) {
            shared->deleter(shared->resource);
        }
    }

    // Release our reference
    resman_refcounter_release(&shared->refcount);
    shared->resource = NULL;
}

/*@
  requires \valid(dest) && \valid(src);
  requires valid_shared_resource(src);
  assigns dest->resource, dest->deleter, dest->refcount, *src->refcount.count;
  ensures dest->resource == src->resource;
  ensures valid_shared_resource(dest);
*/
resman_error_t resman_shared_resource_copy(resman_shared_resource_t* dest,
                                            const resman_shared_resource_t* src) {
    if (!dest || !src) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    dest->resource = src->resource;
    dest->deleter = src->deleter;

    return resman_refcounter_copy(&dest->refcount, &src->refcount);
}

/*@
  requires \valid(dest) && \valid(src);
  requires valid_shared_resource(src);
  assigns dest->resource, dest->deleter, dest->refcount,
          src->resource, src->refcount;
  ensures dest->resource == \old(src->resource);
  ensures src->resource == \null;
*/
void resman_shared_resource_move(resman_shared_resource_t* dest,
                                  resman_shared_resource_t* src) {
    assert(dest != NULL);
    assert(src != NULL);

    dest->resource = src->resource;
    dest->deleter = src->deleter;
    resman_refcounter_move(&dest->refcount, &src->refcount);

    src->resource = NULL;
}

/*@
  requires valid_shared_resource(shared);
  assigns \nothing;
  ensures \result == shared->resource;
*/
void* resman_shared_resource_get(const resman_shared_resource_t* shared) {
    if (!shared) {
        return NULL;
    }
    return shared->resource;
}

/*@
  requires valid_shared_resource(shared);
  assigns \nothing;
  ensures \result >= 0;
*/
int resman_shared_resource_use_count(const resman_shared_resource_t* shared) {
    if (!shared) {
        return 0;
    }
    return resman_refcounter_count(&shared->refcount);
}

/*@
  requires valid_shared_resource(shared);
  assigns \nothing;
  ensures \result == (shared->resource != \null);
*/
bool resman_shared_resource_is_valid(const resman_shared_resource_t* shared) {
    return shared && shared->resource != NULL;
}

// ============================================================================
// ScopeGuard Implementation
// ============================================================================

/*@
  requires \valid(guard);
  requires \valid_function(cleanup);
  requires valid_or_null(user_data);
  assigns guard->cleanup, guard->user_data, guard->active;
  ensures valid_scope_guard(guard);
*/
void resman_scope_guard_init(resman_scope_guard_t* guard,
                              resman_cleanup_fn cleanup,
                              void* user_data) {
    assert(guard != NULL);
    assert(cleanup != NULL);

    guard->cleanup = cleanup;
    guard->user_data = user_data;
    guard->active = true;
}

/*@
  requires \valid(guard);
  requires valid_scope_guard(guard);
  assigns guard->active;
  ensures guard->active == false;
*/
void resman_scope_guard_execute(resman_scope_guard_t* guard) {
    if (!guard) {
        return;
    }

    if (guard->active && guard->cleanup) {
        guard->cleanup(guard->user_data);
    }
    guard->active = false;
}

/*@
  requires \valid(guard);
  requires valid_scope_guard(guard);
  assigns guard->active;
  ensures guard->active == false;
*/
void resman_scope_guard_dismiss(resman_scope_guard_t* guard) {
    if (guard) {
        guard->active = false;
    }
}

/*@
  requires \valid(guard_ptr);
  requires \valid(*guard_ptr);
  requires valid_scope_guard(*guard_ptr);
  assigns (*guard_ptr)->active;
*/
void resman_scope_guard_cleanup_helper(resman_scope_guard_t** guard_ptr) {
    if (guard_ptr && *guard_ptr) {
        resman_scope_guard_execute(*guard_ptr);
    }
}

// ============================================================================
// FileResource Implementation
// ============================================================================

/*@
  requires \valid(file);
  requires \valid_read(filename);
  requires \valid_read(mode);
  assigns file->handle, file->filename, file->mode;
  ensures valid_file_resource(file);
*/
resman_error_t resman_file_resource_open(resman_file_resource_t* file,
                                          const char* filename,
                                          const char* mode) {
    if (!file || !filename || !mode) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    // Open the file
    FILE* fp = fopen(filename, mode);
    if (!fp) {
        // Initialize handle with NULL
        resman_resource_handle_init(&file->handle, NULL, resman_deleter_file);
        file->filename = NULL;
        file->mode = NULL;
        return RESMAN_ERROR_FILE_OPEN_FAILED;
    }

    // Initialize handle with file pointer
    resman_resource_handle_init(&file->handle, fp, resman_deleter_file);

    // Copy filename and mode strings
    file->filename = (char*)malloc(strlen(filename) + 1);
    file->mode = (char*)malloc(strlen(mode) + 1);

    if (!file->filename || !file->mode) {
        resman_resource_handle_destroy(&file->handle);
        free(file->filename);
        free(file->mode);
        return RESMAN_ERROR_OUT_OF_MEMORY;
    }

    strcpy(file->filename, filename);
    strcpy(file->mode, mode);

    return RESMAN_OK;
}

/*@
  requires \valid(file);
  requires valid_file_resource(file);
  assigns file->handle;
  ensures file->handle.resource == \null;
*/
void resman_file_resource_close(resman_file_resource_t* file) {
    if (file) {
        resman_resource_handle_destroy(&file->handle);
    }
}

/*@
  requires \valid(file);
  requires valid_file_resource(file);
  assigns file->handle, file->filename, file->mode;
  ensures file->handle.resource == \null;
  ensures file->filename == \null;
  ensures file->mode == \null;
*/
void resman_file_resource_destroy(resman_file_resource_t* file) {
    if (!file) {
        return;
    }

    resman_resource_handle_destroy(&file->handle);
    free(file->filename);
    free(file->mode);
    file->filename = NULL;
    file->mode = NULL;
}

/*@
  requires valid_file_resource(file);
  assigns \nothing;
  ensures \result == file->handle.resource;
*/
FILE* resman_file_resource_get(const resman_file_resource_t* file) {
    if (!file) {
        return NULL;
    }
    return (FILE*)file->handle.resource;
}

/*@
  requires valid_file_resource(file);
  assigns \nothing;
  ensures \result == (file->handle.resource != \null);
*/
bool resman_file_resource_is_open(const resman_file_resource_t* file) {
    return file && file->handle.resource != NULL;
}

/*@
  requires \valid(file);
  requires valid_file_resource(file);
  requires \valid_read(data);
  assigns *file->handle.resource;
*/
resman_error_t resman_file_resource_write(resman_file_resource_t* file,
                                           const char* data) {
    if (!file || !data) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    if (!file->handle.resource) {
        return RESMAN_ERROR_FILE_NOT_OPEN;
    }

    FILE* fp = (FILE*)file->handle.resource;
    size_t len = strlen(data);
    size_t written = fwrite(data, 1, len, fp);

    if (written != len) {
        return RESMAN_ERROR_INVALID_RESOURCE;
    }

    return RESMAN_OK;
}

/*@
  requires \valid(file);
  requires valid_file_resource(file);
  requires \valid(out_buffer);
  requires \valid(out_size);
  assigns *file->handle.resource, *out_buffer, *out_size;
*/
resman_error_t resman_file_resource_read_all(resman_file_resource_t* file,
                                              char** out_buffer,
                                              size_t* out_size) {
    if (!file || !out_buffer || !out_size) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    if (!file->handle.resource) {
        return RESMAN_ERROR_FILE_NOT_OPEN;
    }

    FILE* fp = (FILE*)file->handle.resource;

    // Get file size
    fseek(fp, 0, SEEK_END);
    long size = ftell(fp);
    fseek(fp, 0, SEEK_SET);

    if (size < 0) {
        return RESMAN_ERROR_INVALID_RESOURCE;
    }

    // Allocate buffer
    char* buffer = (char*)malloc(size + 1);
    if (!buffer) {
        return RESMAN_ERROR_OUT_OF_MEMORY;
    }

    // Read file
    size_t read_bytes = fread(buffer, 1, size, fp);
    buffer[read_bytes] = '\0';

    *out_buffer = buffer;
    *out_size = read_bytes;

    return RESMAN_OK;
}

// ============================================================================
// MemoryPool Implementation
// ============================================================================

/*@
  requires \valid(pool);
  requires capacity > 0;
  requires element_size > 0;
  assigns pool->blocks, pool->free_list, pool->capacity,
          pool->used, pool->element_size;
  ensures valid_memory_pool(pool);
*/
resman_error_t resman_memory_pool_init(resman_memory_pool_t* pool,
                                        size_t capacity,
                                        size_t element_size) {
    if (!pool || capacity == 0 || element_size == 0) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    pool->capacity = capacity;
    pool->element_size = element_size;
    pool->used = 0;
    pool->free_list = NULL;

    // Allocate array of block pointers
    pool->blocks = (resman_memory_pool_block_t**)calloc(capacity,
                                                         sizeof(resman_memory_pool_block_t*));
    if (!pool->blocks) {
        return RESMAN_ERROR_OUT_OF_MEMORY;
    }

    // Allocate and link all blocks
    for (size_t i = 0; i < capacity; i++) {
        resman_memory_pool_block_t* block =
            (resman_memory_pool_block_t*)malloc(sizeof(resman_memory_pool_block_t));
        if (!block) {
            // Cleanup on failure
            for (size_t j = 0; j < i; j++) {
                free(pool->blocks[j]->data);
                free(pool->blocks[j]);
            }
            free(pool->blocks);
            return RESMAN_ERROR_OUT_OF_MEMORY;
        }

        block->data = malloc(element_size);
        if (!block->data) {
            free(block);
            for (size_t j = 0; j < i; j++) {
                free(pool->blocks[j]->data);
                free(pool->blocks[j]);
            }
            free(pool->blocks);
            return RESMAN_ERROR_OUT_OF_MEMORY;
        }

        block->in_use = false;
        block->next = pool->free_list;
        pool->free_list = block;
        pool->blocks[i] = block;
    }

    return RESMAN_OK;
}

/*@
  requires \valid(pool);
  requires valid_memory_pool(pool);
  assigns pool->blocks, pool->free_list, pool->used;
  ensures pool->blocks == \null;
  ensures pool->free_list == \null;
*/
void resman_memory_pool_destroy(resman_memory_pool_t* pool) {
    if (!pool || !pool->blocks) {
        return;
    }

    for (size_t i = 0; i < pool->capacity; i++) {
        if (pool->blocks[i]) {
            free(pool->blocks[i]->data);
            free(pool->blocks[i]);
        }
    }

    free(pool->blocks);
    pool->blocks = NULL;
    pool->free_list = NULL;
    pool->used = 0;
}

/*@
  requires \valid(pool);
  requires valid_memory_pool(pool);
  assigns pool->free_list, pool->used;
  ensures valid_memory_pool(pool);
*/
void* resman_memory_pool_allocate(resman_memory_pool_t* pool) {
    if (!pool || !pool->free_list) {
        return NULL;
    }

    resman_memory_pool_block_t* block = pool->free_list;
    pool->free_list = block->next;
    block->in_use = true;
    block->next = NULL;
    pool->used++;

    return block->data;
}

/*@
  requires \valid(pool);
  requires valid_memory_pool(pool);
  requires valid_or_null(ptr);
  assigns pool->free_list, pool->used;
  ensures valid_memory_pool(pool);
*/
resman_error_t resman_memory_pool_deallocate(resman_memory_pool_t* pool,
                                              void* ptr) {
    if (!pool) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    if (!ptr) {
        return RESMAN_OK;
    }

    // Find the block containing this pointer
    resman_memory_pool_block_t* block = NULL;
    for (size_t i = 0; i < pool->capacity; i++) {
        if (pool->blocks[i]->data == ptr) {
            block = pool->blocks[i];
            break;
        }
    }

    if (!block) {
        return RESMAN_ERROR_INVALID_RESOURCE;
    }

    if (!block->in_use) {
        return RESMAN_ERROR_DOUBLE_FREE;
    }

    block->in_use = false;
    block->next = pool->free_list;
    pool->free_list = block;
    pool->used--;

    return RESMAN_OK;
}

/*@
  requires valid_memory_pool(pool);
  assigns \nothing;
  ensures \result == pool->capacity;
*/
size_t resman_memory_pool_capacity(const resman_memory_pool_t* pool) {
    return pool ? pool->capacity : 0;
}

/*@
  requires valid_memory_pool(pool);
  assigns \nothing;
  ensures \result == pool->used;
*/
size_t resman_memory_pool_used(const resman_memory_pool_t* pool) {
    return pool ? pool->used : 0;
}

/*@
  requires valid_memory_pool(pool);
  assigns \nothing;
  ensures \result == pool->capacity - pool->used;
*/
size_t resman_memory_pool_available(const resman_memory_pool_t* pool) {
    return pool ? (pool->capacity - pool->used) : 0;
}

// ============================================================================
// ResourcePool Implementation
// ============================================================================

/*@
  requires \valid(pool);
  requires capacity > 0;
  assigns pool->resources, pool->available, pool->capacity,
          pool->total, pool->available_count;
  ensures valid_resource_pool(pool);
*/
resman_error_t resman_resource_pool_init(resman_resource_pool_t* pool,
                                          size_t capacity) {
    if (!pool || capacity == 0) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    pool->capacity = capacity;
    pool->total = 0;
    pool->available_count = 0;

    pool->resources = (resman_resource_handle_t*)calloc(capacity,
                                                         sizeof(resman_resource_handle_t));
    pool->available = (void**)calloc(capacity, sizeof(void*));

    if (!pool->resources || !pool->available) {
        free(pool->resources);
        free(pool->available);
        return RESMAN_ERROR_OUT_OF_MEMORY;
    }

    return RESMAN_OK;
}

/*@
  requires \valid(pool);
  requires valid_resource_pool(pool);
  assigns pool->resources, pool->available, pool->total, pool->available_count;
  ensures pool->resources == \null;
  ensures pool->available == \null;
*/
void resman_resource_pool_destroy(resman_resource_pool_t* pool) {
    if (!pool) {
        return;
    }

    if (pool->resources) {
        for (size_t i = 0; i < pool->total; i++) {
            resman_resource_handle_destroy(&pool->resources[i]);
        }
        free(pool->resources);
    }

    free(pool->available);
    pool->resources = NULL;
    pool->available = NULL;
    pool->total = 0;
    pool->available_count = 0;
}

/*@
  requires \valid(pool);
  requires valid_resource_pool(pool);
  requires valid_or_null(resource);
  requires \valid_function(deleter);
  assigns pool->resources, pool->available, pool->total, pool->available_count;
*/
resman_error_t resman_resource_pool_add(resman_resource_pool_t* pool,
                                         void* resource,
                                         resman_deleter_fn deleter) {
    if (!pool || !deleter) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    if (pool->total >= pool->capacity) {
        return RESMAN_ERROR_POOL_CAPACITY;
    }

    // Initialize resource handle
    resman_resource_handle_init(&pool->resources[pool->total], resource, deleter);

    // Add to available list
    pool->available[pool->available_count] = resource;
    pool->available_count++;
    pool->total++;

    return RESMAN_OK;
}

/*@
  requires \valid(pool);
  requires valid_resource_pool(pool);
  assigns pool->available_count;
  ensures valid_resource_pool(pool);
*/
void* resman_resource_pool_acquire(resman_resource_pool_t* pool) {
    if (!pool || pool->available_count == 0) {
        return NULL;
    }

    void* resource = pool->available[pool->available_count - 1];
    pool->available_count--;
    return resource;
}

/*@
  requires \valid(pool);
  requires valid_resource_pool(pool);
  requires valid_or_null(resource);
  assigns pool->available, pool->available_count;
*/
resman_error_t resman_resource_pool_release(resman_resource_pool_t* pool,
                                             void* resource) {
    if (!pool) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    if (!resource) {
        return RESMAN_OK;
    }

    // Verify resource belongs to this pool
    bool found = false;
    for (size_t i = 0; i < pool->total; i++) {
        if (pool->resources[i].resource == resource) {
            found = true;
            break;
        }
    }

    if (!found) {
        return RESMAN_ERROR_INVALID_POOL_RESOURCE;
    }

    // Check if already in available list
    for (size_t i = 0; i < pool->available_count; i++) {
        if (pool->available[i] == resource) {
            return RESMAN_ERROR_RESOURCE_ALREADY_RELEASED;
        }
    }

    // Add to available list
    pool->available[pool->available_count] = resource;
    pool->available_count++;

    return RESMAN_OK;
}

/*@
  requires valid_resource_pool(pool);
  assigns \nothing;
*/
size_t resman_resource_pool_capacity(const resman_resource_pool_t* pool) {
    return pool ? pool->capacity : 0;
}

/*@
  requires valid_resource_pool(pool);
  assigns \nothing;
*/
size_t resman_resource_pool_available(const resman_resource_pool_t* pool) {
    return pool ? pool->available_count : 0;
}

/*@
  requires valid_resource_pool(pool);
  assigns \nothing;
*/
size_t resman_resource_pool_in_use(const resman_resource_pool_t* pool) {
    return pool ? (pool->total - pool->available_count) : 0;
}

// ============================================================================
// PooledResource Implementation
// ============================================================================

/*@
  requires \valid(pr);
  requires \valid(pool);
  requires valid_resource_pool(pool);
  assigns pr->pool, pr->resource, pool->available_count;
  ensures valid_pooled_resource(pr);
*/
resman_error_t resman_pooled_resource_acquire(resman_pooled_resource_t* pr,
                                               resman_resource_pool_t* pool) {
    if (!pr || !pool) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    pr->pool = pool;
    pr->resource = resman_resource_pool_acquire(pool);

    if (!pr->resource) {
        pr->pool = NULL;
        return RESMAN_ERROR_POOL_EXHAUSTED;
    }

    return RESMAN_OK;
}

/*@
  requires \valid(pr);
  requires valid_pooled_resource(pr);
  assigns pr->pool, pr->resource;
  ensures pr->pool == \null;
  ensures pr->resource == \null;
*/
void resman_pooled_resource_release(resman_pooled_resource_t* pr) {
    if (!pr) {
        return;
    }

    if (pr->pool && pr->resource) {
        resman_resource_pool_release(pr->pool, pr->resource);
    }

    pr->pool = NULL;
    pr->resource = NULL;
}

/*@
  requires \valid(dest) && \valid(src);
  requires valid_pooled_resource(src);
  assigns dest->pool, dest->resource, src->pool, src->resource;
  ensures valid_pooled_resource(dest);
*/
void resman_pooled_resource_move(resman_pooled_resource_t* dest,
                                  resman_pooled_resource_t* src) {
    assert(dest != NULL);
    assert(src != NULL);

    dest->pool = src->pool;
    dest->resource = src->resource;

    src->pool = NULL;
    src->resource = NULL;
}

/*@
  requires valid_pooled_resource(pr);
  assigns \nothing;
  ensures \result == pr->resource;
*/
void* resman_pooled_resource_get(const resman_pooled_resource_t* pr) {
    return pr ? pr->resource : NULL;
}

// ============================================================================
// Factory Functions Implementation
// ============================================================================

/*@
  requires valid_or_null(resource);
  requires \valid_function(deleter);
  requires \valid(out_handle);
  assigns *out_handle;
  ensures valid_resource_handle(out_handle);
*/
resman_error_t resman_make_resource(resman_resource_handle_t* out_handle,
                                     void* resource,
                                     resman_deleter_fn deleter) {
    if (!out_handle || !deleter) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    resman_resource_handle_init(out_handle, resource, deleter);
    return RESMAN_OK;
}

/*@
  requires valid_or_null(resource);
  requires \valid_function(deleter);
  requires \valid(out_shared);
  assigns *out_shared;
  ensures valid_shared_resource(out_shared);
*/
resman_error_t resman_make_shared_resource(resman_shared_resource_t* out_shared,
                                            void* resource,
                                            resman_deleter_fn deleter) {
    if (!out_shared || !deleter) {
        return RESMAN_ERROR_NULL_POINTER;
    }

    return resman_shared_resource_init(out_shared, resource, deleter);
}

/*@
  requires size > 0;
  requires element_size > 0;
  ensures \result == \null || \valid((char*)\result);
*/
void* resman_make_array(size_t size, size_t element_size) {
    if (size == 0 || element_size == 0) {
        return NULL;
    }

    return calloc(size, element_size);
}
