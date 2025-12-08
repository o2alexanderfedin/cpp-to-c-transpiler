# RUNTIME LIBRARY DESIGN

**Design Date:** 2025-12-08
**Purpose:** Specify runtime library architecture for C++ to C converter

---

## EXECUTIVE SUMMARY

**Recommendation:** **HYBRID MODE** - Support both inline and separate runtime library

**Default:** Inline runtime (self-contained, no dependencies)
**Optional:** Separate runtime library (smaller code, faster compilation)

**Rationale:** Different use cases have different requirements. Flexibility is key.

---

## DESIGN DECISION

### Mode 1: Inline Runtime (Default)

**Architecture:**
```
Generated C File
├── Runtime implementation (inline)
│   ├── Exception handling functions
│   ├── RTTI functions
│   ├── Type info structures
│   └── Helper functions
└── Generated C code
    ├── Structs
    ├── Functions
    └── VTables
```

**Characteristics:**
- ✅ Self-contained (no external dependencies)
- ✅ Single-file distribution
- ✅ Preferred for safety-critical (no external lib to certify)
- ❌ Larger code size (runtime duplicated per file)
- ❌ Longer compile times

### Mode 2: Runtime Library

**Architecture:**
```
cpptoc_runtime.h (header)
├── Structure declarations
├── Function declarations
└── Macros

cpptoc_runtime.c (implementation)
├── Exception handling
├── RTTI implementation
├── Memory management
└── Helper functions

Generated C Files
├── #include "cpptoc_runtime.h"
└── Use runtime functions
```

**Characteristics:**
- ✅ Smaller generated code
- ✅ Faster compilation
- ✅ Runtime verified once with Frama-C
- ❌ External dependency
- ❌ Link-time dependency

---

## RUNTIME LIBRARY MODULES

### Module 1: Exception Handling (PNaCl SJLJ)

#### Data Structures:

```c
// Exception frame (one per try block)
struct __cxx_exception_frame {
    jmp_buf jmpbuf;
    const struct __cxx_action_entry *actions;
    struct __cxx_exception_frame *next;
    void *exception_object;
    const void *exception_type_info;
};

// Action table entry (destructor to call during unwinding)
struct __cxx_action_entry {
    void (*destructor)(void *object);
    void *object_ptr;
};

// Thread-local exception stack
_Thread_local struct __cxx_exception_frame *__cxx_exception_stack = NULL;
```

#### Core Functions:

```c
// Throw exception
void __cxx_throw(void *exception_object, const void *type_info);

// Begin try block
void __cxx_try_begin(struct __cxx_exception_frame *frame,
                     const struct __cxx_action_entry *actions);

// End try block (normal exit)
void __cxx_try_end(struct __cxx_exception_frame *frame);

// Unwind (call destructors in action table)
void __cxx_unwind(struct __cxx_exception_frame *frame);

// Check if exception matches catch handler
int __cxx_type_matches(const void *thrown_type, const void *catch_type);
```

#### Inline Mode Implementation:

```c
// In generated C file
_Thread_local struct __cxx_exception_frame *__cxx_exception_stack = NULL;

void __cxx_throw(void *exception_object, const void *type_info) {
    if (__cxx_exception_stack == NULL) {
        abort();  // Uncaught exception
    }

    struct __cxx_exception_frame *frame = __cxx_exception_stack;
    frame->exception_object = exception_object;
    frame->exception_type_info = type_info;

    // Call destructors (unwind)
    __cxx_unwind(frame);

    // Jump to catch handler
    longjmp(frame->jmpbuf, 1);
}

void __cxx_unwind(struct __cxx_exception_frame *frame) {
    const struct __cxx_action_entry *actions = frame->actions;
    while (actions && actions->destructor) {
        actions->destructor(actions->object_ptr);
        actions++;
    }
}

// ... other functions
```

#### Frama-C Annotations:

```c
/*@ requires \valid(exception_object);
  @ requires __cxx_exception_stack != NULL;
  @ ensures \false;  // Never returns normally
  @ assigns __cxx_exception_stack->exception_object;
  @*/
void __cxx_throw(void *exception_object, const void *type_info);

/*@ requires \valid(frame);
  @ requires \valid(actions);
  @ ensures frame->actions == actions;
  @ assigns __cxx_exception_stack, frame->next;
  @*/
void __cxx_try_begin(struct __cxx_exception_frame *frame,
                     const struct __cxx_action_entry *actions);
```

---

### Module 2: RTTI (Runtime Type Information)

#### Data Structures:

```c
// Base type_info structure
struct __class_type_info {
    const void *__vtable;
    const char *__type_name;
};

// Single inheritance type_info
struct __si_class_type_info {
    struct __class_type_info base;
    const struct __class_type_info *__base_type;
};

// Multiple/virtual inheritance type_info
struct __vmi_class_type_info {
    struct __class_type_info base;
    unsigned int __flags;
    unsigned int __base_count;
    struct __base_class_type_info {
        const struct __class_type_info *__base_type;
        long __offset_flags;
    } __base_info[1];  // Flexible array
};
```

#### Core Functions:

```c
// Dynamic cast
void* __cxx_dynamic_cast(const void *sub_ptr,
                         const struct __class_type_info *src_type,
                         const struct __class_type_info *dst_type,
                         ptrdiff_t src_to_dst_offset);

// Type comparison
int __cxx_type_matches(const struct __class_type_info *type1,
                       const struct __class_type_info *type2);

// Helper: Traverse class hierarchy
const void* __cxx_find_base_class(const void *obj_ptr,
                                   const struct __vmi_class_type_info *type_info,
                                   const struct __class_type_info *target_type);
```

#### Inline Mode Implementation:

```c
void* __cxx_dynamic_cast(const void *sub_ptr,
                         const struct __class_type_info *src_type,
                         const struct __class_type_info *dst_type,
                         ptrdiff_t src_to_dst_offset) {
    // Null pointer check
    if (sub_ptr == NULL) {
        return NULL;
    }

    // Same type check
    if (src_type == dst_type) {
        return (void*)sub_ptr;
    }

    // Downcast check (src is base of dst)
    if (src_to_dst_offset != -1) {
        return (char*)sub_ptr + src_to_dst_offset;
    }

    // Upcast check (search hierarchy)
    // Implementation based on libcxxabi __dynamic_cast
    // ... hierarchy traversal code
}
```

#### Frama-C Annotations:

```c
/*@ requires sub_ptr == NULL || \valid((char*)sub_ptr + (0..sizeof(void*)));
  @ requires \valid(src_type) && \valid(dst_type);
  @ ensures sub_ptr == NULL ==> \result == NULL;
  @ ensures src_type == dst_type ==> \result == sub_ptr;
  @ assigns \nothing;
  @*/
void* __cxx_dynamic_cast(const void *sub_ptr,
                         const struct __class_type_info *src_type,
                         const struct __class_type_info *dst_type,
                         ptrdiff_t src_to_dst_offset);
```

---

### Module 3: Memory Management

#### Core Functions:

```c
// Coroutine frame allocation
void* __cxx_coro_alloc(size_t size);
void __cxx_coro_free(void *ptr, size_t size);

// Smart pointer helpers (if needed)
void __cxx_shared_ptr_increment(int *refcount);
int __cxx_shared_ptr_decrement(int *refcount);
```

#### Inline Mode Implementation:

```c
void* __cxx_coro_alloc(size_t size) {
    return malloc(size);
}

void __cxx_coro_free(void *ptr, size_t size) {
    (void)size;  // Unused in standard implementation
    free(ptr);
}
```

---

### Module 4: Virtual Inheritance Support

#### Data Structures:

```c
// Virtual Table Table (VTT)
typedef const void **__cxx_VTT;

// VTable with vbase offsets
struct __cxx_vtable_with_vbase {
    ptrdiff_t vbase_offset[1];  // Flexible array, before standard vtable
    void (*vfuncs[1])(void);     // Standard vtable entries
};
```

#### Core Functions:

```c
// Get virtual base pointer
void* __cxx_get_vbase_ptr(const void *obj_ptr,
                          const void *vtable,
                          unsigned int vbase_index);

// Helper for construction
void __cxx_set_vbase_ptr(void *obj_ptr,
                         void *vbase_ptr,
                         unsigned int vbase_offset);
```

---

## CODE SIZE ANALYSIS

### Inline Mode Size Estimation:

| Module | Per-File Size | Notes |
|--------|---------------|-------|
| Exception Handling | 800-1200 bytes | setjmp/longjmp + unwinding |
| RTTI | 600-1000 bytes | dynamic_cast + type matching |
| Memory Management | 100-200 bytes | Mostly wrappers |
| Virtual Inheritance | 200-400 bytes | vbase access |
| **TOTAL** | **1700-2800 bytes** | Per generated C file |

**For 100 generated C files:** 170-280 KB runtime overhead

### Library Mode Size Estimation:

| Module | Library Size | Notes |
|--------|--------------|-------|
| Exception Handling | 800-1200 bytes | One implementation |
| RTTI | 600-1000 bytes | One implementation |
| Memory Management | 100-200 bytes | One implementation |
| Virtual Inheritance | 200-400 bytes | One implementation |
| **TOTAL** | **1700-2800 bytes** | Shared library |

**For 100 generated C files:** 1.7-2.8 KB runtime overhead (plus link)

**Size Reduction:** ~99% for large projects

---

## COMPILATION TIME ANALYSIS

### Inline Mode:

**Per C File Compilation:**
- Runtime code: 0.2-0.5s
- Generated code: 0.5-1.0s
- **Total: 0.7-1.5s per file**

**For 100 files:** 70-150s (parallel compilation reduces this)

### Library Mode:

**Runtime Library Compilation:**
- One-time: 0.7-1.5s

**Per C File Compilation:**
- Generated code only: 0.5-1.0s
- **Total: 0.5-1.0s per file**

**For 100 files:** 50-100s + 1.5s (runtime) = 51.5-101.5s

**Time Reduction:** ~27% for large projects

---

## FRAMA-C VERIFICATION STRATEGY

### Inline Mode Verification:

**Challenge:** Runtime code duplicated in every file

**Strategy:**
1. Verify runtime implementation once (in prototype file)
2. Generate identical runtime code in all files
3. Deterministic generation ensures same properties
4. User verifies only once, trusts generation

**Annotations:**
```c
// In generated files (identical across all)
/*@ verified: yes
  @ verification_date: 2025-12-08
  @ verification_tool: Frama-C 28.0
  @ verification_hash: sha256:...
  @*/
void __cxx_throw(...) {
    // ... implementation
}
```

### Library Mode Verification:

**Challenge:** Runtime library separate from generated code

**Strategy:**
1. Verify cpptoc_runtime.c with Frama-C
2. Export verification results
3. Generated code imports verified library properties
4. Much simpler verification workflow

**Annotations:**
```c
// In cpptoc_runtime.h
/*@ verified: yes
  @ verification_date: 2025-12-08
  @ verification_tool: Frama-C 28.0
  @*/
void __cxx_throw(...);

// Generated code trusts verified library
#include "cpptoc_runtime.h"  // Brings verified properties
```

**Verdict:** Library mode is MUCH better for Frama-C verification

---

## PORTABILITY CONSIDERATIONS

### Platform-Specific Code:

**Thread-Local Storage:**
```c
// C11 standard
_Thread_local struct __cxx_exception_frame *__cxx_exception_stack;

// Fallback for non-C11
#if !defined(__STDC_VERSION__) || __STDC_VERSION__ < 201112L
#  if defined(__GNUC__)
#    define _Thread_local __thread
#  elif defined(_MSC_VER)
#    define _Thread_local __declspec(thread)
#  else
#    error "Thread-local storage not supported"
#  endif
#endif
```

**setjmp/longjmp:**
```c
// Standard C (portable)
#include <setjmp.h>

jmp_buf buf;
if (setjmp(buf) == 0) {
    // Normal execution
} else {
    // Exception caught
}
```

### Dependency Management:

**Standard C Library:**
- Required: `<stdlib.h>`, `<string.h>`, `<setjmp.h>`
- Optional: `<stdint.h>`, `<stdbool.h>`

**No other dependencies**

---

## COMMAND-LINE INTERFACE

### Runtime Mode Selection:

```bash
# Inline runtime (default)
cpptoc input.cpp -o output.c

# Inline runtime (explicit)
cpptoc --runtime-mode=inline input.cpp -o output.c

# Runtime library
cpptoc --runtime-mode=library input.cpp -o output.c

# Generate runtime library
cpptoc --generate-runtime -o cpptoc_runtime.c cpptoc_runtime.h
```

### Runtime Options:

```bash
# Disable specific runtime modules (size optimization)
cpptoc --no-rtti input.cpp            # Disable RTTI runtime
cpptoc --no-exceptions input.cpp      # Disable exception runtime
cpptoc --no-coroutines input.cpp      # Disable coroutine runtime

# Optimize for size
cpptoc --optimize=size input.cpp      # Minimal runtime

# Optimize for speed
cpptoc --optimize=speed input.cpp     # Full runtime with optimizations
```

---

## TESTING STRATEGY

### Unit Tests:

**Runtime Function Tests:**
```c
// Test exception throwing
void test_exception_throw() {
    struct __cxx_exception_frame frame;
    // ... test setup
    __cxx_throw(exception, &type_info);
    // Verify correct unwinding
}

// Test dynamic_cast
void test_dynamic_cast() {
    // ... test hierarchy
    void *result = __cxx_dynamic_cast(obj, src_type, dst_type, -1);
    assert(result != NULL);
}
```

**Integration Tests:**
```c
// Test generated code with inline runtime
void test_generated_code_inline() {
    // Compile generated C file (inline runtime)
    // Execute and verify behavior
}

// Test generated code with library runtime
void test_generated_code_library() {
    // Compile generated C file + runtime library
    // Execute and verify behavior
}
```

### Frama-C Tests:

```bash
# Verify runtime library
frama-c -wp cpptoc_runtime.c

# Verify generated code
frama-c -wp generated_output.c
```

---

## IMPLEMENTATION PRIORITIES

### Phase 1: Exception Runtime (Weeks 1-2)

- ✅ Basic SJLJ implementation
- ✅ Action tables
- ✅ Thread-local exception stack
- ✅ Inline mode

**Deliverable:** Working exception handling in inline mode

### Phase 2: Library Mode (Weeks 3-4)

- ✅ Extract runtime to separate files
- ✅ cpptoc_runtime.h/.c
- ✅ Command-line flags
- ✅ Build system integration

**Deliverable:** Both modes working

### Phase 3: RTTI Runtime (Weeks 5-6)

- ✅ type_info structures
- ✅ dynamic_cast implementation
- ✅ Type matching
- ✅ Both modes

**Deliverable:** RTTI working in both modes

### Phase 4: Additional Modules (Weeks 7-8)

- ✅ Memory management (coroutines)
- ✅ Virtual inheritance support
- ✅ Optimizations

**Deliverable:** Complete runtime

### Phase 5: Frama-C Verification (Weeks 9-10)

- ✅ Add ACSL annotations
- ✅ Verify all runtime functions
- ✅ Document verification results
- ✅ Export verification certificates

**Deliverable:** Verified runtime library

---

## CONCLUSION

### Runtime Library Design Summary:

**Architecture:** Hybrid mode (inline or separate library)
**Default:** Inline (self-contained)
**Recommended for Large Projects:** Library mode
**Recommended for Safety-Critical:** Inline mode

**Modules:**
1. Exception Handling (PNaCl SJLJ) - 800-1200 bytes
2. RTTI (dynamic_cast, typeid) - 600-1000 bytes
3. Memory Management (coroutines) - 100-200 bytes
4. Virtual Inheritance Support - 200-400 bytes

**Total Size:** 1.7-2.8 KB

**Frama-C Strategy:** Verify library once, reuse verification

**Implementation Timeline:** 10 weeks to fully verified runtime

**Next Steps:**
1. Implement exception handling runtime (Phase 1)
2. Add library mode support (Phase 2)
3. Extend with RTTI and other modules (Phases 3-4)
4. Verify with Frama-C (Phase 5)

---

## APPENDIX: Example Generated Code

### With Inline Runtime:

```c
// Generated file: example.c

// ===== INLINE RUNTIME BEGIN =====

_Thread_local struct __cxx_exception_frame *__cxx_exception_stack = NULL;

struct __cxx_exception_frame {
    jmp_buf jmpbuf;
    const struct __cxx_action_entry *actions;
    struct __cxx_exception_frame *next;
    void *exception_object;
};

struct __cxx_action_entry {
    void (*destructor)(void *);
    void *object_ptr;
};

void __cxx_throw(void *exception_object, const void *type_info) {
    // ... implementation
}

// ... other runtime functions

// ===== INLINE RUNTIME END =====

// ===== GENERATED CODE BEGIN =====

struct MyClass {
    int x;
};

void MyClass__ctor(struct MyClass *this, int x) {
    this->x = x;
}

void example(void) {
    struct MyClass obj;
    MyClass__ctor(&obj, 42);
}

// ===== GENERATED CODE END =====
```

### With Runtime Library:

```c
// Generated file: example.c

#include "cpptoc_runtime.h"

// ===== GENERATED CODE BEGIN =====

struct MyClass {
    int x;
};

void MyClass__ctor(struct MyClass *this, int x) {
    this->x = x;
}

void example(void) {
    struct MyClass obj;
    MyClass__ctor(&obj, 42);
}

// ===== GENERATED CODE END =====
```

**Much cleaner with library mode!**
