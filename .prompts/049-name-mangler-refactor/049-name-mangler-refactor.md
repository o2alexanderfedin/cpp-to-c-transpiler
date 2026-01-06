# Refactor NameMangler to Range-v3 Functional Composition Pattern

## Objective

Refactor the existing NameMangler class from an imperative, string-building approach to a modern functional composition pattern using range-v3 generators and pipelines. The refactored implementation should follow SOLID principles, use C++20 coroutines for lazy evaluation, and provide a clean, composable API.

## Context

### Current Implementation Analysis

**File**: `.prompts/049-name-mangler-refactor/name-mangler-analysis.md`

The current NameMangler has been analyzed and documented. Key findings:
- 859 lines of monolithic code (241 header + 618 implementation)
- 12 distinct responsibilities in one class (violates SRP)
- 10 public methods with confusing naming
- String concatenation approach with manual separator management
- Tight coupling with OverloadRegistry

### Target Pattern

**Reference Implementation**: User-provided modern pattern (see prompt context)

The target pattern uses:
```cpp
#include <range/v3/all.hpp>
namespace rv = ranges::views;

// Key techniques:
1. Generator coroutines (ranges::experimental::generator<T>)
2. Functional pipelines with | operator
3. Lazy evaluation - parts generated on-demand
4. Pure functions - no side effects
5. Composition via rv::join()
```

**Example from target**:
```cpp
inline std::string mangle_decl(const clang::Decl *D) {
    return decl_name_parts(D)
        | rv::join(std::string_view("__"))
        | ranges::to<std::string>();
}
```

## Requirements

### Functional Requirements

1. **Preserve Mangling Output**: All existing mangling output must remain identical (tests verify this)
2. **Update All Tests**: Migrate 17 existing test cases to use new API
3. **Support All Current Features**:
   - Class name mangling
   - Method name mangling (instance, static, virtual)
   - Constructor/destructor mangling
   - Standalone function mangling
   - Operator overload mangling
   - Namespace hierarchy encoding
   - Anonymous namespace handling
   - Type parameter encoding for overloads
   - Static member mangling

### Non-Functional Requirements

1. **SOLID Principles**:
   - Single Responsibility: Each function/generator has ONE purpose
   - Open/Closed: Extensible without modifying existing code
   - Liskov Substitution: All generators are composable
   - Interface Segregation: Minimal, focused interfaces
   - Dependency Inversion: Depend on abstractions (ranges)

2. **Performance**:
   - Lazy evaluation - no unnecessary string allocations
   - Zero-copy where possible (use string_view)
   - Reserve capacity for final strings

3. **Code Quality**:
   - Pure functions - no mutable state
   - Const-correct - all input pointers are const
   - Type-safe - leverage C++20 concepts
   - Self-documenting - clear function names

4. **Testing**:
   - All existing tests must pass
   - Add new tests for generator composition
   - Test each generator independently

## Implementation Plan

### Phase 1: Core Utility Functions (Pure Functions)

Create stateless utility functions that form the building blocks:

**File**: `include/mangling/Utils.h`

```cpp
#pragma once
#include <string>
#include <string_view>

namespace cpptoc::mangling {

/// Sanitize type name for use in mangled names
/// Replaces special characters with readable equivalents
/// @example "int*" -> "intptr", "Foo&" -> "Fooref"
inline std::string sanitize_type_name(std::string_view s);

/// Convert operator kind to mangled name
/// @example OO_Plus -> "op_add", OO_EqualEqual -> "op_eq"
inline std::string operator_name(clang::OverloadedOperatorKind kind);

/// Get the base name for a declaration
/// Handles constructors ("ctor"), destructors ("dtor"), operators, conversions
inline std::string get_decl_name(const clang::NamedDecl *ND);

} // namespace cpptoc::mangling
```

**File**: `src/mangling/Utils.cpp`

Implement the three functions following the exact pattern from the reference implementation.

### Phase 2: Generator Coroutines (Lazy Evaluation)

Create generator functions that yield name parts lazily:

**File**: `include/mangling/Generators.h`

```cpp
#pragma once
#include <range/v3/all.hpp>
#include "clang/AST/Decl.h"

namespace cpptoc::mangling {
namespace rv = ranges::views;

/// Generate parameter type names for a function
/// @yields Sanitized type name for each parameter
/// @example void foo(int*, const Bar&) -> yields "intptr", "constBarref"
ranges::experimental::generator<std::string>
param_types(const clang::FunctionDecl *FD);

/// Generate all name parts for a declaration
/// Yields parts in order: namespaces, class, method, parameters
/// @yields Each component of the mangled name
/// @example MyNS::MyClass::method(int) -> yields "MyNS", "MyClass", "method", "int"
ranges::experimental::generator<std::string>
decl_name_parts(const clang::Decl *D);

/// Generate namespace hierarchy parts
/// @yields Each namespace from outermost to innermost
ranges::experimental::generator<std::string>
namespace_parts(const clang::DeclContext *DC);

/// Generate class hierarchy parts
/// @yields Each class from outermost to innermost
ranges::experimental::generator<std::string>
class_parts(const clang::DeclContext *DC);

} // namespace cpptoc::mangling
```

**File**: `src/mangling/Generators.cpp`

Implement each generator following these principles:
- Use `co_yield` for lazy generation
- Handle nullptr gracefully with early `co_return`
- Use const pointers for all AST node parameters
- No mutable state - pure generators

### Phase 3: Composition Functions (Pipeline API)

Create high-level functions that compose generators:

**File**: `include/NameMangler.h` (Complete Replacement)

```cpp
#pragma once
#include <string>
#include "clang/AST/Decl.h"
#include <range/v3/all.hpp>

namespace cpptoc {
namespace rv = ranges::views;

/// Mangle a declaration to a C-compatible name
/// @param D The declaration to mangle
/// @return Fully mangled name (e.g., "MyNS__MyClass__method__int")
std::string mangle_decl(const clang::Decl *D);

/// Mangle a method declaration
/// @param MD The method to mangle
/// @return Mangled method name with class and parameters
std::string mangle_method(const clang::CXXMethodDecl *MD);

/// Mangle a constructor declaration
/// @param CD The constructor to mangle
/// @return Mangled constructor name (e.g., "MyClass__ctor__int")
std::string mangle_constructor(const clang::CXXConstructorDecl *CD);

/// Mangle a destructor declaration
/// @param DD The destructor to mangle
/// @return Mangled destructor name (e.g., "MyClass__dtor")
std::string mangle_destructor(const clang::CXXDestructorDecl *DD);

/// Mangle a standalone function
/// @param FD The function to mangle
/// @return Mangled function name with parameters
std::string mangle_function(const clang::FunctionDecl *FD);

/// Mangle a static member name
/// @param VD The variable declaration
/// @return Mangled static member name
std::string mangle_static_member(const clang::VarDecl *VD);

} // namespace cpptoc
```

**File**: `src/mangling/NameMangler.cpp`

Implement using functional composition:

```cpp
std::string mangle_decl(const clang::Decl *D) {
    return decl_name_parts(D)
        | rv::join(std::string_view("__"))
        | ranges::to<std::string>();
}

std::string mangle_method(const clang::CXXMethodDecl *MD) {
    return mangle_decl(MD);  // Unified implementation
}

// Similar for other functions - use composition, not duplication
```

### Phase 4: Testing Strategy

**Test Files**:
1. `tests/NameManglerTest.cpp` - Update to use new API (all 17 tests)
2. Add unit tests for each component:
   - Utility functions (sanitize_type_name, operator_name, get_decl_name)
   - Generators (param_types, decl_name_parts, namespace_parts, class_parts)
   - Pipeline composition

**Test Coverage**:
- Each utility function independently
- Each generator with nullptr, empty, and populated inputs
- Composition with various declaration types
- All 17 existing test cases migrated and passing

### Phase 5: Call Site Migration

Update all 20+ call sites to use new API:

**Old API**:
```cpp
#include "NameMangler.h"
std::string name = NameMangler::mangleMethodName(method);
```

**New API**:
```cpp
#include "NameMangler.h"
std::string name = cpptoc::mangle_method(method);
```

**Files to Update** (search for "NameMangler::" usage):
- All handler files in `src/dispatch/`
- All translator files that use mangling
- Test files

## Output Specification

### Files to Replace (Complete Rewrite)

1. `include/NameMangler.h` - New functional API with generators
2. `src/NameMangler.cpp` - New implementation using range-v3

### Files to Update

1. `tests/NameManglerTest.cpp` - Migrate 17 tests to new API
2. `CMakeLists.txt` - No changes needed (same file names)
3. All files using `NameMangler::` (20+ call sites) - Update to new function API

### Call Site Migration Pattern

Search for: `NameMangler::`

Replace with appropriate function:
- `NameMangler::mangleName(decl)` → `cpptoc::mangle_decl(decl)`
- `NameMangler::mangleMethodName(method)` → `cpptoc::mangle_method(method)`
- `NameMangler::mangleConstructorName(ctor)` → `cpptoc::mangle_constructor(ctor)`
- `NameMangler::mangleDestructorName(dtor)` → `cpptoc::mangle_destructor(dtor)`
- `NameMangler::mangleFunctionName(func)` → `cpptoc::mangle_function(func)`
- `NameMangler::mangleStaticMemberName(var)` → `cpptoc::mangle_static_member(var)`

### Files to Document

1. `.prompts/049-name-mangler-refactor/SUMMARY.md` - Executive summary
2. `.prompts/049-name-mangler-refactor/MIGRATION.md` - Migration guide
3. `docs/architecture/NameMangling.md` - Architecture documentation

## Success Criteria

### Must Have

✅ All 17 existing NameManglerTest cases pass without modification
✅ Backward compatibility maintained - old API works
✅ New tests achieve 100% coverage of new code
✅ Build succeeds with no warnings
✅ All functions are pure (no mutable state)
✅ Generators use C++20 coroutines correctly
✅ Pipeline composition uses range-v3 correctly

### Should Have

✅ Performance is equal or better (measure with benchmark)
✅ Code size reduced (measure LOC before/after)
✅ Cyclomatic complexity reduced per function
✅ Documentation for all public APIs
✅ Migration guide for call sites

### Nice to Have

✅ Constexpr where possible
✅ Concepts for type constraints
✅ Compile-time string building experiments

## Architecture Decisions

### Why Generator Coroutines?

**Advantages**:
- Lazy evaluation - parts generated on-demand
- Composable - generators can be chained
- Memory efficient - no intermediate strings
- Readable - imperative-style code with `co_yield`

**Trade-offs**:
- Requires C++20
- Slightly more complex debugging
- Coroutine overhead (minimal for this use case)

### Why range-v3 Pipelines?

**Advantages**:
- Functional composition with `|` operator
- Expressive - reads left-to-right like Unix pipes
- Zero-cost abstractions when optimized
- Industry-standard (basis for C++20 ranges)

**Trade-offs**:
- Requires range-v3 library (already added)
- Learning curve for team
- Compiler error messages can be cryptic

### Why Namespace Instead of Class?

**Advantages**:
- Pure functions don't need class state
- Easier to test (no setup/teardown)
- More composable
- Follows modern C++ guidelines

**Trade-offs**:
- Different from existing codebase pattern
- Migration required for call sites

**Decision**: Use namespace for new code, keep class wrapper for backward compatibility.

## Implementation Notes

### Range-v3 Usage

```cpp
// Always use namespace alias
namespace rv = ranges::views;

// Generator return type
ranges::experimental::generator<std::string> my_generator(const Foo *F);

// Pipeline composition
auto result = my_generator(foo)
    | rv::transform([](auto s) { return s + "_suffix"; })
    | rv::join(std::string_view("__"))
    | ranges::to<std::string>();
```

### Coroutine Patterns

```cpp
// Early exit for nullptr
if (!ptr) co_return;

// Yield single value
co_yield some_string;

// Yield from another generator
for (const auto& part : other_generator(ptr)) {
    co_yield part;
}

// Yield from range
for (const auto& item : container) {
    co_yield process(item);
}
```

### String Building Best Practices

```cpp
// BAD: Eager concatenation
std::string result;
for (auto part : parts) {
    result += part + "__";
}

// GOOD: Lazy composition
auto result = parts
    | rv::join(std::string_view("__"))
    | ranges::to<std::string>();
```

### Type Sanitization Pattern

Follow the reference implementation exactly:

```cpp
inline std::string sanitize_type_name(std::string_view s) {
    std::string result;
    result.reserve(s.size());  // Optimize allocation

    for (std::size_t i = 0; i < s.size(); ++i) {
        switch (s[i]) {
            case ' ':  break;  // Skip spaces
            case '*':  result += "ptr"; break;
            case '&':
                // Handle rvalue refs
                if (i + 1 < s.size() && s[i + 1] == '&') {
                    result += "rref"; ++i;
                } else {
                    result += "ref";
                }
                break;
            // ... (continue pattern from reference)
        }
    }
    return result;
}
```

## Verification Steps

### Step 1: Build Verification

```bash
cmake --build build --target cpptoc_core
cmake --build build --target cpptoc
```

Both must succeed with zero warnings.

### Step 2: Test Verification

```bash
# Run existing tests
./build/NameManglerTest
# Must show: [  PASSED  ] 17 tests

# Run new tests
./build/UtilsTest
./build/GeneratorsTest
./build/CompositionTest
```

All must pass.

### Step 3: Integration Verification

Build and run the full transpiler on test cases:

```bash
./build/cpptoc tests/real-world/simple-validation/01-math-library/src/Matrix3x3.cpp
```

Output must be identical to current implementation.

### Step 4: Performance Verification

```bash
# Benchmark before refactor
time ./build/cpptoc tests/real-world/simple-validation/01-math-library/src/*.cpp

# Benchmark after refactor
time ./build/cpptoc tests/real-world/simple-validation/01-math-library/src/*.cpp
```

Performance should be within 5% (preferably better).

## Dependencies

### Required

- ✅ range-v3 library (already added in previous work)
- ✅ C++20 compiler with coroutine support
- ✅ Clang AST headers

### Optional

- Benchmark library (for performance comparison)
- Valgrind (for memory profiling)

## Risks and Mitigations

### Risk: Breaking Changes

**Mitigation**:
- Keep old API as deprecated wrapper
- Run all existing tests
- Gradual migration of call sites

### Risk: Performance Regression

**Mitigation**:
- Benchmark before/after
- Profile hot paths
- Use string_view and reserve()

### Risk: Coroutine Bugs

**Mitigation**:
- Unit test each generator independently
- Use sanitizers (ASAN, UBSAN)
- Test with nullptr and edge cases

### Risk: Range-v3 Complexity

**Mitigation**:
- Start simple (just join and to)
- Add documentation and examples
- Team training session

## Timeline Estimate

**Phase 1**: Core utilities (sanitize_type_name, operator_name, get_decl_name) - 1 day
**Phase 2**: Generators (param_types, decl_name_parts, etc.) - 2 days
**Phase 3**: Composition API (mangle_decl, mangle_method, etc.) - 1 day
**Phase 4**: Testing (update existing + add new tests) - 1 day
**Phase 5**: Call site migration (update 20+ files) - 1 day

**Total**: ~6 days for complete replacement (2 days faster without backward compat)

## References

- User-provided reference implementation (in prompt context)
- Analysis document: `.prompts/049-name-mangler-refactor/name-mangler-analysis.md`
- Current implementation: `include/NameMangler.h`, `src/NameMangler.cpp`
- Current tests: `tests/NameManglerTest.cpp`
- range-v3 documentation: https://ericniebler.github.io/range-v3/
- C++20 coroutines: https://en.cppreference.com/w/cpp/language/coroutines

## Notes for Executor

1. **Read the analysis first**: `.prompts/049-name-mangler-refactor/name-mangler-analysis.md`
2. **Follow the reference pattern exactly**: Use the same structure, naming, and idioms
3. **Don't skip backward compatibility**: Old tests MUST pass
4. **Test as you go**: Write tests for each component before moving to next
5. **Use TODO markers sparingly**: Implement fully, don't leave placeholders
6. **Document assumptions**: If unclear, note it and choose simplest path
7. **Commit incrementally**: After each phase completes successfully
