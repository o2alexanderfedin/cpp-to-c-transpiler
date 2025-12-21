<objective>
Transpile the Resource Manager real-world test project from C++ to C with comprehensive ACSL (ANSI/ISO C Specification Language) annotations.

This is the most sophisticated real-world test project in the codebase, featuring advanced template metaprogramming, custom memory management, SFINAE patterns, and reference counting. The transpilation will validate the transpiler's capability to handle enterprise-grade C++ code while adding formal verification annotations.
</objective>

<context>
**Project Location**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/resource-manager`

**Project Complexity**:
- 2 files, 1,162 total lines of code
- Advanced template metaprogramming with SFINAE
- Custom reference-counted smart pointers
- Generic resource handle templates with customizable deleters
- Move-only semantics throughout
- RAII scope guards and cleanup utilities
- Memory pool pattern implementation
- Resource factory pattern
- Exception safety guarantees

**Key C++ Features to Transpile**:
- Template specialization and SFINAE patterns
- Custom deleters for files and memory
- Reference counting implementation
- Move semantics (move constructors/assignment)
- Operator overloading (operator->(), operator*(), operator bool())
- RAII patterns

**Output Requirements**:
- Transpiled C code in subdirectory: `./tests/real-world/resource-manager/transpiled/`
- Preserve all functionality and semantics
- Add comprehensive ACSL annotations for formal verification
- Maintain type safety through C constructs
</context>

<requirements>

## Functional Requirements

1. **Complete Transpilation**: Convert all C++ source files to equivalent C code
   - `resource_manager.hpp` → `resource_manager.h` + `resource_manager.c`
   - `resource_manager.cpp` → integrate into `resource_manager.c`

2. **ACSL Annotations**: Add comprehensive formal verification annotations
   - Function preconditions (`/*@ requires ... */`)
   - Function postconditions (`/*@ ensures ... */`)
   - Loop invariants (`/*@ loop invariant ... */`)
   - Memory safety assertions (`/*@ assert \valid(ptr) */`)
   - Reference counting invariants
   - Resource ownership annotations

3. **Template Resolution**: Manually instantiate all template patterns
   - Resource handles for different types (FILE*, memory blocks, etc.)
   - Custom deleter functions for each resource type
   - Type-specific reference counting structures

4. **Memory Management**: Translate smart pointer semantics to C
   - Reference counting with atomic operations or mutex protection
   - Custom deleter function pointers
   - Proper cleanup on zero reference count
   - Move semantics through explicit ownership transfer

5. **RAII Translation**: Convert RAII patterns to explicit cleanup
   - Scope guard structures with cleanup callbacks
   - Explicit initialization and cleanup functions
   - Stack-based automatic cleanup using GCC cleanup attribute or manual tracking

## ACSL Annotation Requirements

For each function, include:
```c
/*@
  requires <preconditions: pointer validity, reference counts, resource states>;
  assigns <modified variables and memory regions>;
  ensures <postconditions: return values, state changes, reference counts>;
  behavior <specific_case>:
    assumes <conditions for this behavior>;
    requires <additional preconditions>;
    ensures <specific postconditions>;
*/
```

For reference counting:
```c
/*@
  predicate valid_refcount(struct ref_counted *rc) =
    \valid(rc) && rc->ref_count > 0;

  predicate resource_owned(struct resource_handle *rh) =
    \valid(rh) && valid_refcount(rh->ref_control);
*/
```

For memory safety:
```c
/*@
  requires \valid(ptr);
  ensures \result == \null || \valid(\result);
  ensures \result != \null ==> \fresh(\result);
*/
```

## Quality Requirements

1. **Type Safety**: Use struct wrappers and function pointers to maintain type distinctions
2. **Memory Safety**: All allocations must have corresponding deallocations
3. **Thread Safety**: Document thread safety assumptions in ACSL annotations
4. **Exception Safety**: Translate exception guarantees to error code patterns with cleanup

</requirements>

<implementation>

## Step-by-Step Transpilation Process

1. **Survey the Codebase**
   - Read all files in `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/resource-manager/`
   - Identify all template instantiations used in tests
   - Map C++ features to C equivalents
   - Read project's CLAUDE.md for conventions

2. **Create Output Directory Structure**
   ```
   ./tests/real-world/resource-manager/transpiled/
   ├── resource_manager.h      (header with types, declarations, ACSL predicates)
   ├── resource_manager.c      (implementation)
   ├── CMakeLists.txt          (build configuration)
   └── README.md               (transpilation notes)
   ```

3. **Template Instantiation Strategy**
   - Create concrete types for each resource type (file_handle, memory_handle, etc.)
   - Generate type-specific functions for common operations
   - Use function pointers for custom deleters

4. **Reference Counting Translation**
   ```c
   typedef struct ref_control {
       size_t ref_count;
       void (*deleter)(void*);
       void *resource;
   } ref_control_t;

   /*@
     predicate valid_ref_control(ref_control_t *rc) =
       \valid(rc) && rc->ref_count > 0 &&
       \valid_function(rc->deleter) &&
       (rc->resource == \null || \valid(rc->resource));
   */
   ```

5. **Move Semantics Translation**
   - Use explicit ownership transfer functions
   - Nullify source after move
   - Add ACSL annotations for ownership transfer

6. **RAII Translation**
   - Create scope guard structures
   - Use GCC `__attribute__((cleanup))` for automatic cleanup
   - Manual cleanup paths for portability

7. **Error Handling Translation**
   - C++ exceptions → C error codes (enum)
   - RAII cleanup → explicit cleanup on error paths
   - Document exception safety guarantees in ACSL

8. **Build Integration**
   - Create CMakeLists.txt for transpiled code
   - Ensure it builds with `-std=c11` or `-std=c17`
   - Add ACSL verification targets (using Frama-C if available)

## What to Preserve

- All resource management semantics (acquire/release patterns)
- Reference counting correctness
- Memory safety guarantees
- Custom deleter behavior
- Move-only semantics (no accidental copies)

## What to Avoid (and WHY)

- **Don't use void* for everything**: Maintain type distinctions with wrapper structs to preserve type safety and enable ACSL verification
- **Don't skip ACSL annotations**: Formal verification is the key deliverable - comprehensive annotations are mandatory
- **Don't lose exception safety guarantees**: Document all cleanup paths and invariants in ACSL
- **Don't create memory leaks**: Every allocation must have a corresponding deallocation path verified by ACSL
- **Don't use platform-specific code without guards**: Keep it portable C11/C17

</implementation>

<output>

Create the following files in `./tests/real-world/resource-manager/transpiled/`:

1. **`resource_manager.h`**: Header with all type definitions, function declarations, and ACSL predicate definitions
2. **`resource_manager.c`**: Complete implementation with ACSL function contracts
3. **`CMakeLists.txt`**: Build configuration that compiles the transpiled code
4. **`README.md`**: Documentation covering:
   - Transpilation strategy and design decisions
   - Template instantiations created
   - ACSL annotation approach
   - How to build and verify the code
   - Comparison with original C++ implementation

All file paths should be relative to the project root.

</output>

<verification>

Before declaring complete, verify:

1. **Compilation**: Code compiles successfully with `-std=c11 -Wall -Wextra -Werror`
2. **ACSL Syntax**: All ACSL annotations are syntactically valid
3. **Completeness**: All C++ functionality has been transpiled
4. **Type Safety**: No unsafe casts or untyped void* operations
5. **Memory Safety**: All allocations have corresponding frees
6. **Documentation**: README.md thoroughly explains design decisions

Run these verification steps:
```bash
# Build the transpiled code
cd tests/real-world/resource-manager/transpiled
mkdir -p build && cd build
cmake .. && cmake --build .

# Verify ACSL annotations (if Frama-C is available)
frama-c -wp ../resource_manager.c -wp-prover alt-ergo
```

</verification>

<success_criteria>

✓ All C++ source files transpiled to C
✓ Comprehensive ACSL annotations on all functions
✓ ACSL predicates defined for key invariants (reference counting, resource ownership)
✓ Code compiles without warnings
✓ CMakeLists.txt successfully builds the project
✓ README.md documents transpilation approach
✓ All template instantiations manually resolved
✓ Reference counting semantics preserved
✓ Move semantics translated to ownership transfer
✓ RAII patterns converted to explicit cleanup
✓ Memory safety verified through annotations

</success_criteria>

<research>
Before beginning implementation, research:
- Existing ACSL annotation patterns in the codebase
- C11/C17 features available for implementation
- Any existing transpiler utilities or helper functions
- CMake patterns used in the project
</research>
