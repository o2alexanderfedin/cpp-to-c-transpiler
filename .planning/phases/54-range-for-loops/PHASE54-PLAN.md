# Phase 54 Plan: Range-Based For Loops

**Phase**: 54 (Range-For Loops)
**Prerequisite**: Iterators, auto type deduction, Phase 48 (Namespaces)
**Status**: PLANNING
**Target**: Implement C++ range-based for loops with iterator protocol translation

## Phase Goal

Implement complete support for C++ range-based for loops (`for (auto x : container)`), translating them to traditional C for loops using begin/end iterators or array indexing. Handle STL containers, C arrays, custom iterators, and structured bindings. Generate idiomatic C code that mirrors the iteration semantics.

## Range-Based For Loop Pattern Overview

C++ range-based for loops provide syntactic sugar for iterating over sequences:
1. **Array iteration** - `for (auto x : array)` => index-based loop
2. **Container iteration** - `for (auto x : vec)` => iterator-based loop
3. **Const/reference variants** - `for (const auto& x : vec)` => efficient iteration
4. **Structured bindings** - `for (auto [k, v] : map)` => destructuring (C++17)

### Pattern Example

**C++ Source:**
```cpp
#include <vector>
#include <array>
#include <map>

void example() {
    // Array iteration
    int arr[5] = {1, 2, 3, 4, 5};
    for (int x : arr) {
        printf("%d\n", x);
    }

    // Vector iteration (by value)
    std::vector<int> vec = {10, 20, 30};
    for (int x : vec) {
        printf("%d\n", x);
    }

    // Vector iteration (by const reference - efficient)
    for (const int& x : vec) {
        printf("%d\n", x);
    }

    // Auto type deduction
    for (auto x : vec) {
        printf("%d\n", x);
    }

    // Structured bindings with map (C++17)
    std::map<int, std::string> m = {{1, "one"}, {2, "two"}};
    for (auto [key, value] : m) {
        printf("%d: %s\n", key, value.c_str());
    }
}
```

**Generated C (Range-For Translation):**
```c
#include <stdio.h>

/* Forward declarations for vector */
struct vector_int;
struct vector_int_iterator;

/* Vector iterator structure */
struct vector_int_iterator {
    int *ptr;
};

/* Vector begin/end functions */
struct vector_int_iterator vector_int__begin(struct vector_int *this);
struct vector_int_iterator vector_int__end(struct vector_int *this);
int vector_int_iterator__deref(struct vector_int_iterator *this);
void vector_int_iterator__increment(struct vector_int_iterator *this);
int vector_int_iterator__not_equal(struct vector_int_iterator *a,
                                     struct vector_int_iterator *b);

void example() {
    /* Array iteration => index-based loop */
    int arr[5] = {1, 2, 3, 4, 5};
    for (size_t __i = 0; __i < 5; ++__i) {
        int x = arr[__i];
        printf("%d\n", x);
    }

    /* Vector iteration (by value) => iterator loop */
    struct vector_int vec;
    /* ... vec initialization ... */

    {
        struct vector_int_iterator __begin = vector_int__begin(&vec);
        struct vector_int_iterator __end = vector_int__end(&vec);
        for (; vector_int_iterator__not_equal(&__begin, &__end);
             vector_int_iterator__increment(&__begin)) {
            int x = vector_int_iterator__deref(&__begin);
            printf("%d\n", x);
        }
    }

    /* Vector iteration (by const reference) => iterator loop with pointer */
    {
        struct vector_int_iterator __begin = vector_int__begin(&vec);
        struct vector_int_iterator __end = vector_int__end(&vec);
        for (; vector_int_iterator__not_equal(&__begin, &__end);
             vector_int_iterator__increment(&__begin)) {
            const int* x = &vector_int_iterator__deref(&__begin);
            printf("%d\n", *x);
        }
    }

    /* Auto type deduction => same as by-value */
    {
        struct vector_int_iterator __begin = vector_int__begin(&vec);
        struct vector_int_iterator __end = vector_int__end(&vec);
        for (; vector_int_iterator__not_equal(&__begin, &__end);
             vector_int_iterator__increment(&__begin)) {
            int x = vector_int_iterator__deref(&__begin);
            printf("%d\n", x);
        }
    }

    /* Structured bindings => destructuring assignment */
    struct map_int_string m;
    /* ... map initialization ... */

    {
        struct map_int_string_iterator __begin = map_int_string__begin(&m);
        struct map_int_string_iterator __end = map_int_string__end(&m);
        for (; map_int_string_iterator__not_equal(&__begin, &__end);
             map_int_string_iterator__increment(&__begin)) {
            struct pair_int_string __pair = map_int_string_iterator__deref(&__begin);
            int key = __pair.first;
            struct string value = __pair.second;
            printf("%d: %s\n", key, string__c_str(&value));
        }
    }
}
```

## Key Concepts

### Iterator Protocol Requirements
For a type to be range-compatible in C++:
1. **begin()/end() methods** or free functions
2. **Iterator dereference** (`operator*`)
3. **Iterator increment** (`operator++`)
4. **Iterator comparison** (`operator!=`)

### Array vs Container Detection
- **C arrays**: Compile-time known size, use index loop
- **Containers**: Runtime size, use begin/end iterators
- **Range detection**: Check for begin/end methods or array type

### Value Categories
- **By value** (`auto x`): Copy element each iteration
- **By const reference** (`const auto& x`): Efficient, read-only
- **By mutable reference** (`auto& x`): Modify elements in place
- **Rvalue reference** (`auto&& x`): Universal reference (defer to Phase 57)

## Implementation Tasks

### Group 1: Range Detection & Classification (3 tasks - parallel)

**Task 1: Range Type Analyzer** (Est. 3-4 hours)
- Create `RangeTypeAnalyzer` helper class
- Detect range-for loops in Clang AST (`CXXForRangeStmt`)
- Classify range type (C array, STL container, custom type)
- Determine if begin/end are methods or free functions
- **Tests** (12-15 tests):
  - Detect range-for loop statement
  - Classify C array range
  - Classify std::vector range
  - Classify std::array range
  - Classify std::map range
  - Classify custom container range
  - Detect begin() method
  - Detect end() method
  - Detect free-function begin()
  - Detect free-function end()
  - Handle const container
  - Extract range expression
  - Determine array size (constant)
  - Error on non-iterable type

**Task 2: Iterator Type Deducer** (Est. 3-4 hours) - PARALLEL with Task 1
- Create `IteratorTypeDeducer` helper class
- Deduce iterator type from range
- Extract value type from iterator dereference
- Handle const iterators vs mutable iterators
- **Tests** (10-12 tests):
  - Deduce iterator type for vector
  - Deduce iterator type for array
  - Deduce iterator type for map
  - Deduce value type from iterator
  - Handle const_iterator
  - Handle reverse_iterator
  - Extract pointer type for arrays
  - Deduce pair type for map
  - Handle auto type deduction
  - Handle const auto& deduction
  - Handle auto& deduction

**Task 3: Loop Variable Analyzer** (Est. 2-3 hours) - PARALLEL with Tasks 1,2
- Analyze loop variable declaration
- Determine value category (value, const ref, mutable ref)
- Extract variable name and type
- Handle structured bindings (defer complex cases)
- **Tests** (8-10 tests):
  - Extract loop variable name
  - Determine by-value semantics
  - Determine by-const-ref semantics
  - Determine by-mutable-ref semantics
  - Handle auto type
  - Handle explicit type
  - Handle const qualifier
  - Detect structured binding (error or simple support)
  - Multiple loop variables (error)

### Group 2: Array-Based Loop Translation (2 tasks - parallel)

**Task 4: Array Loop Generator** (Est. 2-3 hours)
- Create `ArrayLoopGenerator` helper class
- Generate index-based for loop for C arrays
- Pattern: `for (size_t i = 0; i < N; ++i)`
- Handle array element access
- **Tests** (10-12 tests):
  - Generate loop for int array
  - Generate loop for struct array
  - Generate loop for pointer array
  - Use correct array size
  - Generate unique index variable name
  - Handle nested array loops (avoid name collision)
  - By-value array element access
  - By-reference array element access
  - Const array iteration
  - Multi-dimensional array (defer or error)
  - Array of unknown size (error)

**Task 5: Array Element Access** (Est. 2 hours) - PARALLEL with Task 4
- Generate element access expression
- Pattern: `T x = arr[i]` or `T* x = &arr[i]`
- Handle value vs reference semantics
- **Tests** (6-8 tests):
  - Generate by-value access (arr[i])
  - Generate by-reference access (&arr[i])
  - Generate const reference access
  - Correct type for element
  - Pointer vs value distinction
  - Array element with complex type

### Group 3: Iterator-Based Loop Translation (4 tasks - 2 parallel + 2)

**Task 6: Iterator Variable Generator** (Est. 3-4 hours)
- Create `IteratorLoopGenerator` helper class
- Generate begin/end iterator variables
- Pattern: `Iterator __begin = container.begin(); Iterator __end = container.end();`
- Unique variable names to avoid collision
- **Tests** (12-15 tests):
  - Generate begin iterator variable
  - Generate end iterator variable
  - Correct iterator type
  - Unique variable names
  - Call begin() method
  - Call end() method
  - Call free-function begin()
  - Call free-function end()
  - Const container uses const_iterator
  - Mutable container uses iterator
  - Handle namespace-qualified iterator
  - Iterator struct generation
  - Temporary container handling

**Task 7: Iterator Loop Structure** (Est. 3-4 hours) - PARALLEL with Task 6
- Generate for loop with iterator protocol
- Pattern: `for (; it != end; ++it)`
- Call iterator increment and comparison
- Handle iterator method calls
- **Tests** (12-15 tests):
  - Generate for loop init (empty)
  - Generate for loop condition (it != end)
  - Generate for loop increment (++it)
  - Call iterator increment method
  - Call iterator comparison method
  - Use prefix increment
  - Correct comparison function
  - Handle custom iterator
  - Handle STL iterator
  - Iterator in namespace
  - Nested iterator loops
  - Iterator with const

**Task 8: Iterator Dereference** (Est. 2-3 hours) - DEPENDS on Tasks 6, 7
- Generate loop variable initialization from iterator
- Pattern: `T x = *it` or `const T& x = *it`
- Call iterator dereference operator
- Handle value vs reference semantics
- **Tests** (10-12 tests):
  - Generate dereference call
  - By-value dereference
  - By-const-ref dereference (pointer)
  - By-mutable-ref dereference (pointer)
  - Correct dereference function name
  - Handle struct return from deref
  - Handle pointer return from deref
  - Complex type dereference
  - Map pair dereference
  - Custom iterator dereference

**Task 9: Begin/End Function Translation** (Est. 3-4 hours) - DEPENDS on Task 6
- Translate begin()/end() calls to C functions
- Pattern: `container__begin(&container)`
- Handle member methods vs free functions
- Generate function declarations if needed
- **Tests** (10-12 tests):
  - Translate begin() member call
  - Translate end() member call
  - Translate begin() free function
  - Translate end() free function
  - Generate begin() declaration
  - Generate end() declaration
  - Correct function signature
  - Const begin/end functions
  - Namespace-qualified begin/end
  - Template container begin/end
  - Custom container begin/end

### Group 4: Structured Binding Support (2 tasks - sequential)

**Task 10: Simple Structured Binding** (Est. 3-4 hours)
- Handle simple structured bindings for pairs
- Pattern: `auto [a, b] = pair` => `T a = pair.first; U b = pair.second;`
- Support std::pair decomposition
- **Tests** (10-12 tests):
  - Detect structured binding
  - Extract binding variable names
  - Decompose std::pair
  - Generate first access
  - Generate second access
  - Correct types for bindings
  - Const structured binding
  - Mutable structured binding
  - Nested pair (defer or error)
  - Tuple decomposition (defer)
  - Custom struct decomposition (defer)

**Task 11: Map Iteration with Structured Binding** (Est. 2-3 hours) - DEPENDS on Task 10
- Combine iterator loop with pair decomposition
- Pattern: `for (auto [k, v] : map)` => loop + decomposition
- **Tests** (8-10 tests):
  - Iterate map with structured binding
  - Decompose key and value
  - Correct key type
  - Correct value type
  - Const key/value
  - Mutable value binding
  - Map with complex types
  - Integration with iterator loop

### Group 5: Integration & Optimization (3 tasks - 2 parallel + 1)

**Task 12: Statement Handler Integration** (Est. 3-4 hours)
- Extend `StatementHandler` to handle `CXXForRangeStmt`
- Dispatch to array or iterator generator
- Generate complete loop translation
- **Tests** (15-18 tests):
  - Detect CXXForRangeStmt
  - Dispatch to array generator
  - Dispatch to iterator generator
  - Generate complete array loop
  - Generate complete iterator loop
  - Handle nested range-for loops
  - Range-for with break
  - Range-for with continue
  - Range-for with return
  - Range-for body translation
  - Empty range-for body
  - Complex range-for body
  - Range-for in function
  - Range-for in method
  - Range-for with structured binding
  - Integration with existing statement handling

**Task 13: Optimization Pass** (Est. 2-3 hours) - PARALLEL with Task 12
- Optimize generated loop code
- Hoist begin/end calls if container is const
- Eliminate redundant iterator copies
- Generate readable C code
- **Tests** (6-8 tests):
  - Hoist end() for const container
  - Avoid redundant begin() calls
  - Minimize temporary variables
  - Generate clean loop structure
  - Readable variable names
  - Optimize trivial loops

**Task 14: Integration with Auto Type Deduction** (Est. 3-4 hours) - DEPENDS on Task 12
- Ensure auto type deduction works in loop variables
- Deduce type from range element type
- Handle cv-qualifiers (const/volatile)
- **Tests** (10-12 tests):
  - Deduce auto type from vector
  - Deduce auto type from array
  - Deduce const auto& type
  - Deduce auto& type
  - Deduce auto&& type (defer rvalue)
  - Correct type for auto
  - Auto with complex type
  - Auto with template type
  - Auto with namespace type
  - Integration with existing auto support

### Group 6: End-to-End Testing (1 task)

**Task 15: E2E Tests** (Est. 4-5 hours)
- Create `tests/e2e/phase54/RangeForLoopsE2ETest.cpp`
- Compile and execute generated C code
- **Tests** (20-25 tests):
  - 3 active sanity tests
  - 4-5 active tests (realistic algorithms)
  - 15-17 disabled complex algorithm tests:
    - Sum array elements
    - Find max in vector
    - Filter vector elements
    - Transform vector (map operation)
    - Count occurrences
    - Iterate map and print
    - Nested loops (2D array)
    - Range-for with early exit (break)
    - Range-for with skip (continue)
    - Custom container iteration
    - Const container iteration
    - Modify elements via reference
    - Structured binding with map
    - String iteration (char array)
    - Mixed array and container loops
    - Integration with Phase 48 namespaces
    - Integration with Phase 53 type aliases

## Execution Strategy

### Parallel Execution Groups

**Group 1 (Tasks 1-3)**: Range Detection & Classification
- All 3 tasks in parallel - ~3-4 hours
- **Total: ~3-4 hours**

**Group 2 (Tasks 4-5)**: Array-Based Loop Translation
- Both tasks in parallel - ~2-3 hours
- **Total: ~2-3 hours**

**Group 3 (Tasks 6-9)**: Iterator-Based Loop Translation
- Task 6 + Task 7 in parallel - ~3-4 hours
- Task 8 + Task 9 sequential after 6,7 - ~5-7 hours
- **Total: ~8-11 hours**

**Group 4 (Tasks 10-11)**: Structured Binding Support
- Task 10 then Task 11 sequential - ~5-7 hours
- **Total: ~5-7 hours**

**Group 5 (Tasks 12-14)**: Integration & Optimization
- Task 12 + Task 13 in parallel - ~3-4 hours
- Task 14 sequential after 12 - ~3-4 hours
- **Total: ~6-8 hours**

**Group 6 (Task 15)**: E2E Testing
- Task 15 - ~4-5 hours
- **Total: ~4-5 hours**

**Overall Estimated Time:**
- Parallel: ~28-38 hours
- Sequential: ~45-60 hours
- **Time Savings: ~35-40%**

## Files to Create

1. `include/handlers/RangeTypeAnalyzer.h` - Analyze range types
2. `src/handlers/RangeTypeAnalyzer.cpp` - Implementation
3. `tests/unit/handlers/RangeTypeAnalyzerTest.cpp` - Unit tests
4. `include/handlers/IteratorTypeDeducer.h` - Deduce iterator types
5. `src/handlers/IteratorTypeDeducer.cpp` - Implementation
6. `tests/unit/handlers/IteratorTypeDeducerTest.cpp` - Unit tests
7. `include/handlers/ArrayLoopGenerator.h` - Generate array loops
8. `src/handlers/ArrayLoopGenerator.cpp` - Implementation
9. `tests/unit/handlers/ArrayLoopGeneratorTest.cpp` - Unit tests
10. `include/handlers/IteratorLoopGenerator.h` - Generate iterator loops
11. `src/handlers/IteratorLoopGenerator.cpp` - Implementation
12. `tests/unit/handlers/IteratorLoopGeneratorTest.cpp` - Unit tests
13. `include/handlers/StructuredBindingHandler.h` - Handle structured bindings
14. `src/handlers/StructuredBindingHandler.cpp` - Implementation
15. `tests/unit/handlers/StructuredBindingHandlerTest.cpp` - Unit tests
16. `tests/e2e/phase54/RangeForLoopsE2ETest.cpp` - E2E tests
17. `.planning/phases/54-range-for-loops/PHASE54-USAGE-GUIDE.md` - User guide
18. `.planning/phases/54-range-for-loops/PHASE54-COMPLETE.md` - Summary doc

## Files to Modify

1. `include/handlers/StatementHandler.h` - Add range-for handling
2. `src/handlers/StatementHandler.cpp` - Implement CXXForRangeStmt
3. `include/handlers/ExpressionHandler.h` - Add iterator operations
4. `src/handlers/ExpressionHandler.cpp` - Implement iterator calls
5. `include/handlers/TypeHandler.h` - Add auto type deduction
6. `src/handlers/TypeHandler.cpp` - Implement auto for loop vars
7. `include/CppToCVisitor.h` - Add range-for visitor
8. `src/CppToCVisitor.cpp` - Integrate range-for handling
9. `CMakeLists.txt` - Add new test targets

## Success Criteria

- [ ] All 100-120 unit tests pass (100%)
- [ ] All 15-18 integration tests pass (100%)
- [ ] 3-5 E2E active tests pass (100%)
- [ ] Array-based loops generate index iteration
- [ ] Container-based loops generate iterator protocol
- [ ] Auto type deduction works for loop variables
- [ ] Const/mutable reference semantics preserved
- [ ] Structured bindings decompose pairs correctly
- [ ] Begin/end functions called correctly
- [ ] Iterator increment/dereference/comparison work
- [ ] Nested range-for loops supported
- [ ] Generated C code compiles without warnings
- [ ] Code follows SOLID principles
- [ ] TDD followed throughout

## Test Count Targets

- **Group 1 Tests**: 30-37 tests (Range Analyzer 12-15, Iterator Deducer 10-12, Loop Var 8-10)
- **Group 2 Tests**: 16-20 tests (Array Loop Gen 10-12, Element Access 6-8)
- **Group 3 Tests**: 44-53 tests (Iterator Vars 12-15, Loop Structure 12-15, Deref 10-12, Begin/End 10-12)
- **Group 4 Tests**: 18-22 tests (Structured Binding 10-12, Map Iteration 8-10)
- **Group 5 Tests**: 31-38 tests (Statement Handler 15-18, Optimization 6-8, Auto Integration 10-12)
- **Group 6 Tests**: 20-25 tests (E2E)
- **Total: 159-195 tests** (target 80-100 active, rest disabled for complex scenarios)

## Dependencies

**Requires:**
- Phase 48 (Namespaces) - For namespaced containers
- Iterator infrastructure (may need to be created)
- Auto type deduction (partial support exists)
- begin()/end() function generation
- Clang AST traversal infrastructure

**External:**
- Clang AST API for range-for loops
- Clang CXXForRangeStmt
- Clang auto type deduction
- Google Test framework
- CMake build system

## Risk Mitigation

**Risk 1: Iterator Infrastructure Missing**
- Mitigation: Create minimal iterator support for common containers
- Fallback: Support only arrays and std::vector initially
- Test: Comprehensive iterator protocol tests

**Risk 2: Auto Type Deduction Complexity**
- Mitigation: Leverage Clang's type deduction
- Fallback: Require explicit types if auto fails
- Test: Auto deduction integration tests

**Risk 3: Structured Binding Complexity**
- Mitigation: Support only simple cases (pairs) initially
- Defer: Complex bindings (tuples, custom structs) to later
- Test: Error handling for unsupported cases

**Risk 4: Custom Container Support**
- Mitigation: Design extensible system for begin/end
- Fallback: Focus on STL containers and arrays first
- Document: How to add custom container support

**Risk 5: Performance of Generated Code**
- Mitigation: Optimize common patterns
- Test: Benchmark against hand-written C loops
- Document: Performance characteristics

## Translation Patterns

### Array Loop Translation

```cpp
// C++ Input
int arr[5] = {1, 2, 3, 4, 5};
for (int x : arr) {
    printf("%d\n", x);
}

// C Output
int arr[5] = {1, 2, 3, 4, 5};
for (size_t __i = 0; __i < 5; ++__i) {
    int x = arr[__i];
    printf("%d\n", x);
}
```

### Vector Loop Translation

```cpp
// C++ Input
std::vector<int> vec = {10, 20, 30};
for (const int& x : vec) {
    printf("%d\n", x);
}

// C Output
struct vector_int vec;
/* ... initialization ... */

{
    struct vector_int_iterator __begin = vector_int__begin(&vec);
    struct vector_int_iterator __end = vector_int__end(&vec);
    for (; vector_int_iterator__not_equal(&__begin, &__end);
         vector_int_iterator__increment(&__begin)) {
        const int* x = &vector_int_iterator__deref(&__begin);
        printf("%d\n", *x);
    }
}
```

### Map with Structured Binding

```cpp
// C++ Input
std::map<int, std::string> m = {{1, "one"}};
for (auto [key, value] : m) {
    printf("%d: %s\n", key, value.c_str());
}

// C Output
struct map_int_string m;
/* ... initialization ... */

{
    struct map_int_string_iterator __begin = map_int_string__begin(&m);
    struct map_int_string_iterator __end = map_int_string__end(&m);
    for (; map_int_string_iterator__not_equal(&__begin, &__end);
         map_int_string_iterator__increment(&__begin)) {
        struct pair_int_string __pair = map_int_string_iterator__deref(&__begin);
        int key = __pair.first;
        struct string value = __pair.second;
        printf("%d: %s\n", key, string__c_str(&value));
    }
}
```

## Known Limitations

1. **Rvalue References** - `auto&&` deferred to Phase 57 (Move Semantics)
2. **Complex Structured Bindings** - Only pairs supported, tuples deferred
3. **Custom Iterators** - May need manual begin/end implementations
4. **Range Adaptors** - C++20 ranges library not supported
5. **Reverse Iteration** - Reverse iterators deferred
6. **Initializer List Ranges** - Temporary ranges may not work

## Next Steps After Completion

**Phase 55: Friend Declarations** - Est. 8-12 hours
- Friend classes and functions
- Access control bypass
- Low priority

**Phase 56: Virtual Inheritance** - Est. 40-60 hours
- Diamond problem solution
- Virtual base tables
- Depends on Phase 46

## References

### Range-Based For Loops
- [C++ Reference: Range-For Loop](https://en.cppreference.com/w/cpp/language/range-for)
- [C++ Reference: Iterator Library](https://en.cppreference.com/w/cpp/iterator)
- [C++ Reference: Structured Binding](https://en.cppreference.com/w/cpp/language/structured_binding)

### Technical Resources
- [Clang CXXForRangeStmt Documentation](https://clang.llvm.org/doxygen/classclang_1_1CXXForRangeStmt.html)
- [Iterator Protocol in C++ - Stack Overflow](https://stackoverflow.com/questions/7758580/writing-your-own-stl-container)
- [Understanding Range-For - Fluent C++](https://www.fluentcpp.com/2018/03/30/is-stdfor_each-obsolete/)

---

**Created**: 2025-12-26
**Status**: READY FOR IMPLEMENTATION
**Dependencies**: Iterators, auto type deduction, Phase 48 (Namespaces)
**Estimated Effort**: 20-30 hours (parallel execution)
**Priority**: HIGH (common modern C++ idiom)
