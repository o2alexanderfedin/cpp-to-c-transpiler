# ACSL Annotation Guide for Runtime Library

**User Story #185:** ACSL Annotation Infrastructure for Runtime Library
**Epic #15:** Frama-C Compatibility & Formal Verification (#47)

## Overview

This document describes the ACSL (ANSI/ISO C Specification Language) annotations added to the runtime library for formal verification with Frama-C.

ACSL annotations provide formal specifications for C code, enabling:
- **Formal verification** of correctness properties
- **Static analysis** for undefined behavior detection
- **Certification compliance** for safety-critical applications (DO-178C, ISO 26262, IEC 62304)

## Files with ACSL Annotations

1. `runtime/exception_runtime.h` - Exception handling runtime
2. `runtime/rtti_runtime.h` - RTTI (Run-Time Type Information) runtime

## Exception Runtime Annotations

### Location
`runtime/exception_runtime.h`

### Predicates

#### `valid_exception_frame`
```c
/*@ predicate valid_exception_frame(struct __cxx_exception_frame *f) =
        \valid(f) &&
        \valid(&f->jmpbuf);
*/
```

**Purpose:** Validates that an exception frame pointer is valid and its jmpbuf field is accessible.

**Used in:** Exception stack validation

#### `valid_exception_stack`
```c
/*@ predicate valid_exception_stack(struct __cxx_exception_frame *stack) =
        stack == \null || valid_exception_frame(stack);
*/
```

**Purpose:** Validates that the exception stack is either NULL or points to a valid exception frame.

**Used in:** `cxx_throw` preconditions

### Function Specifications

#### `cxx_throw`
```c
/*@ requires valid_exception: exception != \null;
    requires valid_type: type_info != \null && \valid_read(type_info);
    requires valid_stack: valid_exception_stack(__cxx_exception_stack);
    requires has_handler: __cxx_exception_stack != \null;
    ensures \false;  // Function never returns (longjmp)
    assigns *__cxx_exception_stack;
*/
void cxx_throw(void *exception, const char *type_info);
```

**Preconditions:**
- `exception` must not be NULL
- `type_info` must be a valid, readable string
- Exception stack must be in a valid state
- At least one exception handler must be active (stack not NULL)

**Postconditions:**
- `\false` indicates this function never returns (performs longjmp)

**Side effects:**
- Modifies the exception stack (`*__cxx_exception_stack`)

## RTTI Runtime Annotations

### Location
`runtime/rtti_runtime.h`

### Predicates

#### `valid_type_info`
```c
/*@ predicate valid_type_info(struct __class_type_info *t) =
        \valid_read(t) &&
        \valid_read(t->type_name);
*/
```

**Purpose:** Validates that a type_info structure is readable and has a valid type name.

**Used in:** RTTI function preconditions

#### `valid_si_type_info`
```c
/*@ predicate valid_si_type_info(struct __si_class_type_info *t) =
        \valid_read(t) &&
        \valid_read(t->type_name) &&
        (t->base_type == \null || valid_type_info((struct __class_type_info*)t->base_type));
*/
```

**Purpose:** Validates single-inheritance type_info structures, including optional base type.

**Used in:** Single inheritance hierarchy validation

### Function Specifications

#### `traverse_hierarchy`
```c
/*@ requires valid_src: valid_type_info((struct __class_type_info*)src);
    requires valid_dst: valid_type_info((struct __class_type_info*)dst);
    requires valid_ptr: ptr == \null || \valid_read((char*)ptr);
    ensures null_preserving: ptr == \null ==> \result == \null;
    ensures same_type: src == dst ==> \result == (void*)ptr;
    ensures valid_result: \result == \null || \valid_read((char*)\result);
    assigns \nothing;
*/
void *traverse_hierarchy(const void *ptr, const struct __class_type_info *src,
                         const struct __class_type_info *dst);
```

**Preconditions:**
- Source and destination type_info must be valid
- Object pointer must be NULL or valid

**Postconditions:**
- NULL input produces NULL output (null_preserving)
- Same source and destination types return the original pointer (same_type)
- Result is either NULL or a valid pointer (valid_result)

**Side effects:**
- Pure function - no modifications (`assigns \nothing`)

#### `cross_cast_traverse`
```c
/*@ requires valid_src: valid_type_info((struct __class_type_info*)src);
    requires valid_dst: valid_type_info((struct __class_type_info*)dst);
    requires valid_dynamic: valid_type_info((struct __class_type_info*)dynamic_type);
    requires valid_ptr: ptr == \null || \valid_read((char*)ptr);
    ensures null_preserving: ptr == \null ==> \result == \null;
    ensures same_type: src == dst ==> \result == (void*)ptr);
    ensures valid_result: \result == \null || \valid_read((char*)\result);
    assigns \nothing;
*/
void *cross_cast_traverse(const void *ptr,
                          const struct __class_type_info *src,
                          const struct __class_type_info *dst,
                          const struct __class_type_info *dynamic_type);
```

**Preconditions:**
- Source, destination, and dynamic type_info must all be valid
- Object pointer must be NULL or valid

**Postconditions:**
- Same as `traverse_hierarchy`

**Side effects:**
- Pure function - no modifications

## ACSL Syntax Validation

### Running Tests

```bash
./tests/verify_acsl.sh
```

This script validates all ACSL annotations using Frama-C's parser.

**Expected output:**
```
=========================================
ACSL Annotation Validation Test
=========================================

[Test 1] Validating exception_runtime.h ACSL annotations...
✓ exception_runtime.h: ACSL syntax valid
[Test 2] Validating rtti_runtime.h ACSL annotations...
✓ rtti_runtime.h: ACSL syntax valid
[Test 3] Validating rtti_runtime.c ACSL annotations...
✓ rtti_runtime.c: ACSL syntax valid

=========================================
All ACSL validation tests passed!
=========================================
```

### Manual Validation

To manually validate a single file:

```bash
frama-c -cpp-extra-args="-Iruntime" runtime/exception_runtime.h
```

If no errors are reported, the ACSL syntax is valid.

## ACSL Annotation Conventions

### 1. Predicate Naming
- Use descriptive names: `valid_exception_frame`, not `vef`
- Prefix with domain: `valid_*` for validity predicates

### 2. Preconditions (`requires`)
- Label each requirement: `requires valid_ptr: ...`
- Check NULL before dereferencing
- Validate all pointer arguments with `\valid` or `\valid_read`

### 3. Postconditions (`ensures`)
- Label guarantees: `ensures null_preserving: ...`
- Use `\result` to reference return value
- Document non-returning functions with `ensures \false`

### 4. Side Effects (`assigns`)
- List all modified variables/memory locations
- Use `assigns \nothing` for pure functions
- Be explicit about global variable modifications

### 5. Type Casts in ACSL
- Use explicit casts when needed: `(struct __class_type_info*)src`
- ACSL type system is stricter than C

## Future Enhancements

### Planned for Story #186-#192:
1. **Loop invariants** for iterative algorithms
2. **Function contracts** for runtime implementations (.c files)
3. **Axiomatic definitions** for complex predicates
4. **Lemmas** for proving properties
5. **WP (Weakest Precondition)** verification
6. **Value analysis** for undefined behavior detection

## References

- [ACSL Specification](https://frama-c.com/download/acsl.pdf)
- [Frama-C User Manual](https://frama-c.com/download/frama-c-user-manual.pdf)
- [Epic #15: Frama-C Compatibility](https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/47)
- [Story #185: ACSL Annotation Infrastructure](https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/185)

## Verification Status

| File | ACSL Annotations | Syntax Valid | WP Verified | Value Analysis |
|------|------------------|--------------|-------------|----------------|
| exception_runtime.h | ✅ | ✅ | ⏳ Story #186 | ⏳ Story #189 |
| rtti_runtime.h | ✅ | ✅ | ⏳ Story #187 | ⏳ Story #189 |
| rtti_runtime.c | ⏳ | ✅ | ⏳ Story #187 | ⏳ Story #189 |

---

**Created:** 2025-12-13
**Story:** #185
**Epic:** #15 (#47)

🤖 Generated with [Claude Code](https://claude.com/claude-code)

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
