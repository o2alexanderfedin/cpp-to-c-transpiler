# Phase 59: Variadic Templates - Translation Examples and Patterns

**Status**: DOCUMENTATION-ONLY (Deferred Implementation)
**Date**: 2025-12-27
**Approach**: Comprehensive documentation following Phase 55 pattern

## Overview

This document provides comprehensive examples of how C++ variadic templates WOULD be translated to C if/when implemented. Currently, variadic templates are **deferred** (VERY LOW priority, see PHASE59-EVALUATION.md), but this documentation serves as:

1. Reference for users attempting to transpile variadic template code
2. Design specification for future implementation
3. Guide for alternative patterns in transpilable C++ code

## Key Concepts

### What Are Variadic Templates?

**C++ Feature:**
```cpp
// Variadic function template - arbitrary number of type parameters
template<typename... Args>
void print(Args... args);

// Variadic class template - arbitrary number of types
template<typename... Types>
struct Tuple { /* ... */ };

// Usage
print(1, "hello", 3.14);           // 3 arguments, 3 types
Tuple<int, float, char> t;         // 3 types
```

**Key Components:**
- **Parameter Pack** (`typename... Args`): Template parameter that accepts 0+ types
- **Pack Expansion** (`Args... args`): Expands pack into argument list
- **Fold Expression** (`(args + ...)`): C++17 feature to reduce pack
- **sizeof...()** (`sizeof...(Args)`): Returns pack size at compile time

### Translation Strategy: Monomorphization

**Approach:** Generate separate C code for each instantiation.

**Why:** C has no template concept. Each unique instantiation becomes a separate function/struct with concrete types.

**Existing Infrastructure:** TemplateMonomorphizer (Phase 11) handles this for basic templates.

**What's Missing:** Pack expansion logic, fold expression translation, sizeof...() evaluation.

## Example 1: Simple Variadic Function

### C++ Code

```cpp
#include <iostream>

// Variadic function template
template<typename T>
void print_impl(T value) {
    std::cout << value << " ";
}

template<typename First, typename... Rest>
void print_impl(First first, Rest... rest) {
    std::cout << first << " ";
    print_impl(rest...);  // Recursive pack expansion
}

template<typename... Args>
void print(Args... args) {
    print_impl(args...);
    std::cout << std::endl;
}

int main() {
    print(1, 2.5, "hello");
    print(42);
    print();  // Empty pack
    return 0;
}
```

### Conceptual C Translation

```c
#include <stdio.h>

// ============================================================================
// Monomorphized Versions for print(1, 2.5, "hello")
// ============================================================================

// Base case: print_impl(const char*)
void print_impl__cstr(const char* value) {
    printf("%s ", value);
}

// Intermediate: print_impl(double, const char*)
void print_impl__double_cstr(double first, const char* rest_0) {
    printf("%f ", first);
    print_impl__cstr(rest_0);
}

// Full expansion: print_impl(int, double, const char*)
void print_impl__int_double_cstr(int first, double rest_0, const char* rest_1) {
    printf("%d ", first);
    print_impl__double_cstr(rest_0, rest_1);
}

// Top-level print(int, double, const char*)
void print__int_double_cstr(int arg0, double arg1, const char* arg2) {
    print_impl__int_double_cstr(arg0, arg1, arg2);
    printf("\n");
}

// ============================================================================
// Monomorphized Versions for print(42)
// ============================================================================

// Base case: print_impl(int)
void print_impl__int(int value) {
    printf("%d ", value);
}

// Top-level print(int)
void print__int(int arg0) {
    print_impl__int(arg0);
    printf("\n");
}

// ============================================================================
// Monomorphized Versions for print()
// ============================================================================

// Empty pack: print()
void print__void(void) {
    // No arguments, just newline
    printf("\n");
}

// ============================================================================
// Main
// ============================================================================

int main(void) {
    print__int_double_cstr(1, 2.5, "hello");
    print__int(42);
    print__void();
    return 0;
}
```

### Translation Notes

**Pack Expansion:**
- `Args... args` becomes individual parameters: `arg0, arg1, arg2`
- Parameter names are mangled: `args...` → `rest_0, rest_1`

**Recursive Expansion:**
- Each recursion level gets its own function
- Base case must be explicitly handled
- Full call chain is generated

**Name Mangling:**
- Function names encode all type parameters
- `print<int, double, const char*>` → `print__int_double_cstr`
- Consistent with existing TemplateMonomorphizer

**Empty Pack:**
- Zero-argument version is valid
- Generates `_void` suffix (no parameters)

## Example 2: Variadic Class Template (Tuple)

### C++ Code

```cpp
// Simple tuple implementation with variadic templates
template<typename... Types>
struct Tuple;

// Base case: empty tuple
template<>
struct Tuple<> {
    Tuple() {}
};

// Recursive case
template<typename Head, typename... Tail>
struct Tuple<Head, Tail...> {
    Head head;
    Tuple<Tail...> tail;

    Tuple(Head h, Tail... t) : head(h), tail(t...) {}
};

int main() {
    Tuple<int, float, const char*> t(42, 3.14f, "hello");
    return 0;
}
```

### Conceptual C Translation

```c
// ============================================================================
// Monomorphized Tuple Structs
// ============================================================================

// Base case: Tuple<> (empty)
typedef struct Tuple__empty {
    // No fields
    char dummy;  // C doesn't allow empty structs
} Tuple__empty;

void Tuple__empty__init(Tuple__empty* this) {
    // No initialization needed
}

// Tuple<const char*>
typedef struct Tuple__cstr {
    const char* head;
    Tuple__empty tail;
} Tuple__cstr;

void Tuple__cstr__init(Tuple__cstr* this, const char* h) {
    this->head = h;
    Tuple__empty__init(&this->tail);
}

// Tuple<float, const char*>
typedef struct Tuple__float_cstr {
    float head;
    Tuple__cstr tail;
} Tuple__float_cstr;

void Tuple__float_cstr__init(Tuple__float_cstr* this, float h, const char* t0) {
    this->head = h;
    Tuple__cstr__init(&this->tail, t0);
}

// Tuple<int, float, const char*>
typedef struct Tuple__int_float_cstr {
    int head;
    Tuple__float_cstr tail;
} Tuple__int_float_cstr;

void Tuple__int_float_cstr__init(Tuple__int_float_cstr* this,
                                  int h, float t0, const char* t1) {
    this->head = h;
    Tuple__float_cstr__init(&this->tail, t0, t1);
}

// ============================================================================
// Main
// ============================================================================

int main(void) {
    Tuple__int_float_cstr t;
    Tuple__int_float_cstr__init(&t, 42, 3.14f, "hello");
    return 0;
}
```

### Translation Notes

**Recursive Structure:**
- Each tuple size gets its own struct
- Nested tail pattern preserved in C
- Base case (empty tuple) needs dummy field

**Constructor Translation:**
- Variadic constructor → init function with all parameters
- Pack expansion in constructor call → separate parameter passing
- Initialization propagates through tail recursively

**Memory Layout:**
- All fields embedded in struct (no pointers)
- Same memory layout as C++ (tail is value, not pointer)
- Can be stack-allocated

## Example 3: Fold Expressions (C++17)

### C++ Code

```cpp
// Sum using fold expression
template<typename... Args>
auto sum(Args... args) {
    return (args + ...);  // Unary right fold
}

// Logical AND using fold expression
template<typename... Args>
bool all_true(Args... args) {
    return (args && ...);
}

// Variadic max using fold expression
template<typename... Args>
auto max_value(Args... args) {
    return (args > ... > args);  // Binary fold (doesn't work, just example)
}

int main() {
    int total = sum(1, 2, 3, 4, 5);  // 15
    bool result = all_true(true, true, false);  // false
    return 0;
}
```

### Conceptual C Translation

```c
// ============================================================================
// sum(1, 2, 3, 4, 5) - Unary right fold
// ============================================================================

// Fold expression: (args + ...) expands to: arg0 + (arg1 + (arg2 + (arg3 + arg4)))
int sum__int_int_int_int_int(int arg0, int arg1, int arg2, int arg3, int arg4) {
    return arg0 + arg1 + arg2 + arg3 + arg4;  // Left-associative in C
}

// Alternative: Preserve right-associativity (unnecessary for +)
int sum__int_int_int_int_int_right_assoc(int arg0, int arg1, int arg2, int arg3, int arg4) {
    return arg0 + (arg1 + (arg2 + (arg3 + arg4)));
}

// ============================================================================
// all_true(true, true, false) - Logical AND fold
// ============================================================================

// Fold expression: (args && ...) expands to: arg0 && arg1 && arg2
int all_true__bool_bool_bool(int arg0, int arg1, int arg2) {
    return arg0 && arg1 && arg2;
}

// ============================================================================
// Main
// ============================================================================

int main(void) {
    int total = sum__int_int_int_int_int(1, 2, 3, 4, 5);
    int result = all_true__bool_bool_bool(1, 1, 0);  // true=1, false=0
    return 0;
}
```

### Translation Notes

**Fold Operators:**
- Arithmetic: `+, -, *, /, %`
- Bitwise: `&, |, ^, <<, >>`
- Logical: `&&, ||`
- Comparison: `==, !=, <, >, <=, >=`
- Comma: `,`

**Fold Types:**
- **Unary right fold**: `(args op ...)` → `arg0 op (arg1 op arg2)`
- **Unary left fold**: `(... op args)` → `(arg0 op arg1) op arg2`
- **Binary fold**: Includes init value (more complex)

**C Translation:**
- Most folds can use C's left-associative operators
- Right-associativity can be preserved with parentheses if needed
- Short-circuit evaluation preserved for `&&` and `||`

**Limitations:**
- Can't fold arbitrary expressions (only operators)
- Custom operators not supported (C has no operator overloading)

## Example 4: sizeof...() Operator

### C++ Code

```cpp
// Count arguments using sizeof...()
template<typename... Args>
constexpr size_t count_args(Args... args) {
    return sizeof...(Args);
}

// Create array with pack size
template<typename... Args>
void print_count(Args... args) {
    constexpr size_t N = sizeof...(Args);
    const char* types[N] = { typeid(args).name()... };
    printf("Received %zu arguments\n", N);
}

int main() {
    size_t n1 = count_args(1, 2, 3);      // 3
    size_t n2 = count_args();              // 0
    print_count(1, "hello", 3.14);        // 3
    return 0;
}
```

### Conceptual C Translation

```c
#include <stddef.h>
#include <stdio.h>

// ============================================================================
// count_args Monomorphizations
// ============================================================================

// count_args(1, 2, 3) - sizeof...(Args) = 3
size_t count_args__int_int_int(int arg0, int arg1, int arg2) {
    return 3;  // sizeof...(Args) evaluated at compile time
}

// count_args() - sizeof...(Args) = 0
size_t count_args__void(void) {
    return 0;  // Empty pack
}

// ============================================================================
// print_count Monomorphizations
// ============================================================================

// print_count(1, "hello", 3.14) - sizeof...(Args) = 3
void print_count__int_cstr_double(int arg0, const char* arg1, double arg2) {
    const size_t N = 3;  // sizeof...(Args) = 3

    // Note: typeid().name() not available in C, would need alternative
    const char* types[3] = { "int", "const char*", "double" };

    printf("Received %zu arguments\n", N);
}

// ============================================================================
// Main
// ============================================================================

int main(void) {
    size_t n1 = count_args__int_int_int(1, 2, 3);
    size_t n2 = count_args__void();
    print_count__int_cstr_double(1, "hello", 3.14);
    return 0;
}
```

### Translation Notes

**sizeof...() Evaluation:**
- Compile-time constant in C++
- Becomes literal integer in C
- Known at monomorphization time

**Array Sizing:**
- `const size_t N = sizeof...(Args)` → `const size_t N = 3`
- Arrays can be sized with compile-time constant

**Type Information:**
- `typeid(args).name()` has no C equivalent
- Would need preprocessing or alternative approach
- Could generate type name strings at monomorphization time

## Example 5: Perfect Forwarding with Variadic Templates

### C++ Code

```cpp
// Factory function using perfect forwarding
template<typename T, typename... Args>
T* make(Args&&... args) {
    return new T(std::forward<Args>(args)...);
}

struct Point {
    int x, y;
    Point(int x, int y) : x(x), y(y) {}
};

int main() {
    Point* p = make<Point>(10, 20);
    delete p;
    return 0;
}
```

### Conceptual C Translation

```c
#include <stdlib.h>

// ============================================================================
// Point Struct
// ============================================================================

typedef struct Point {
    int x;
    int y;
} Point;

void Point__init(Point* this, int x, int y) {
    this->x = x;
    this->y = y;
}

// ============================================================================
// make<Point>(int, int) - No forwarding in C
// ============================================================================

// Perfect forwarding disappears in C (no rvalue references)
// Args&&... becomes Args... (all by value)
Point* make__Point__int_int(int arg0, int arg1) {
    Point* obj = (Point*)malloc(sizeof(Point));
    if (obj) {
        Point__init(obj, arg0, arg1);
    }
    return obj;
}

// ============================================================================
// Main
// ============================================================================

int main(void) {
    Point* p = make__Point__int_int(10, 20);
    free(p);
    return 0;
}
```

### Translation Notes

**Rvalue References:**
- `Args&&... args` → `Args... args` (by value)
- C has no rvalue references
- Perfect forwarding becomes simple parameter passing

**std::forward:**
- Disappears entirely in C
- No move semantics in C
- May lose some C++ optimizations

**Trade-offs:**
- Correctness preserved (code works)
- Performance may be slightly worse (copies instead of moves)
- For POD types, no difference in practice

## Example 6: Variadic Constructor

### C++ Code

```cpp
struct Logger {
    std::vector<std::string> messages;

    template<typename... Args>
    Logger(Args... args) {
        // Fold expression to push all arguments
        (messages.push_back(args), ...);
    }
};

int main() {
    Logger log("Starting", "Processing", "Done");
    return 0;
}
```

### Conceptual C Translation

```c
#include <string.h>
#include <stdlib.h>

// ============================================================================
// Logger Struct (simplified - no std::vector in C)
// ============================================================================

typedef struct Logger {
    char** messages;
    size_t count;
    size_t capacity;
} Logger;

// Helper to add message
void Logger__add_message(Logger* this, const char* msg) {
    if (this->count >= this->capacity) {
        this->capacity = this->capacity ? this->capacity * 2 : 4;
        this->messages = (char**)realloc(this->messages,
                                         this->capacity * sizeof(char*));
    }
    this->messages[this->count++] = strdup(msg);
}

// ============================================================================
// Logger Constructor: Logger(const char*, const char*, const char*)
// ============================================================================

void Logger__init__cstr_cstr_cstr(Logger* this,
                                   const char* arg0,
                                   const char* arg1,
                                   const char* arg2) {
    this->messages = NULL;
    this->count = 0;
    this->capacity = 0;

    // Fold expression: (messages.push_back(args), ...)
    // Expands to: push(arg0), push(arg1), push(arg2)
    Logger__add_message(this, arg0);
    Logger__add_message(this, arg1);
    Logger__add_message(this, arg2);
}

void Logger__destroy(Logger* this) {
    for (size_t i = 0; i < this->count; i++) {
        free(this->messages[i]);
    }
    free(this->messages);
}

// ============================================================================
// Main
// ============================================================================

int main(void) {
    Logger log;
    Logger__init__cstr_cstr_cstr(&log, "Starting", "Processing", "Done");
    Logger__destroy(&log);
    return 0;
}
```

### Translation Notes

**Comma Fold Expression:**
- `(messages.push_back(args), ...)` → sequence of calls
- Expands to statement sequence
- Execution order preserved

**Container Translation:**
- `std::vector<std::string>` → C array with manual memory management
- Push_back → manual resize and append logic
- String ownership managed explicitly

## Example 7: Variadic Min/Max

### C++ Code

```cpp
// Variadic minimum using fold expression
template<typename... Args>
auto min_value(Args... args) {
    return (args < ... < args);  // Won't compile - invalid fold
}

// Correct version using initializer_list
template<typename T>
T min_value(std::initializer_list<T> values) {
    return *std::min_element(values.begin(), values.end());
}

// Alternative: Recursive version
template<typename T>
T min_recursive(T value) {
    return value;
}

template<typename T, typename... Rest>
T min_recursive(T first, Rest... rest) {
    T rest_min = min_recursive(rest...);
    return first < rest_min ? first : rest_min;
}

int main() {
    int m = min_recursive(5, 3, 8, 1, 9);  // 1
    return 0;
}
```

### Conceptual C Translation

```c
// ============================================================================
// Recursive min_recursive Monomorphizations
// ============================================================================

// Base case: min_recursive(int)
int min_recursive__int(int value) {
    return value;
}

// min_recursive(int, int)
int min_recursive__int_int(int first, int rest_0) {
    int rest_min = min_recursive__int(rest_0);
    return first < rest_min ? first : rest_min;
}

// min_recursive(int, int, int)
int min_recursive__int_int_int(int first, int rest_0, int rest_1) {
    int rest_min = min_recursive__int_int(rest_0, rest_1);
    return first < rest_min ? first : rest_min;
}

// min_recursive(int, int, int, int)
int min_recursive__int_int_int_int(int first, int rest_0, int rest_1, int rest_2) {
    int rest_min = min_recursive__int_int_int(rest_0, rest_1, rest_2);
    return first < rest_min ? first : rest_min;
}

// min_recursive(int, int, int, int, int)
int min_recursive__int_int_int_int_int(int first, int rest_0, int rest_1,
                                        int rest_2, int rest_3) {
    int rest_min = min_recursive__int_int_int_int(rest_0, rest_1, rest_2, rest_3);
    return first < rest_min ? first : rest_min;
}

// ============================================================================
// Main
// ============================================================================

int main(void) {
    int m = min_recursive__int_int_int_int_int(5, 3, 8, 1, 9);
    return 0;
}
```

### Translation Notes

**Recursive Pattern:**
- Each pack size generates separate function
- Full recursion chain monomorphized
- All intermediate functions generated

**Optimization:**
- C compiler can inline these calls
- Final code may be optimized to simple comparisons
- No runtime recursion overhead if inlined

**Alternative:**
- Could generate iterative version instead
- Could use C99 variadic functions (different approach)

## Example 8: Pack Expansion in Multiple Contexts

### C++ Code

```cpp
// Pack expansion in different contexts
template<typename... Args>
void multi_context(Args... args) {
    // 1. Function call pack expansion
    process(args...);

    // 2. Initializer list pack expansion
    int values[] = { args... };

    // 3. sizeof... operator
    constexpr size_t count = sizeof...(Args);

    // 4. Fold expression
    int sum = (args + ...);

    // 5. Multiple pack expansions in same expression
    call_pair(args..., args...);
}
```

### Conceptual C Translation

```c
// Assume: multi_context<int, int, int>(1, 2, 3)

void multi_context__int_int_int(int arg0, int arg1, int arg2) {
    // 1. Function call pack expansion: process(args...)
    process__int_int_int(arg0, arg1, arg2);

    // 2. Initializer list pack expansion: int values[] = { args... }
    int values[] = { arg0, arg1, arg2 };

    // 3. sizeof... operator: sizeof...(Args)
    const size_t count = 3;

    // 4. Fold expression: (args + ...)
    int sum = arg0 + arg1 + arg2;

    // 5. Multiple pack expansions: call_pair(args..., args...)
    call_pair__int_int_int__int_int_int(arg0, arg1, arg2, arg0, arg1, arg2);
}
```

### Translation Notes

**Pack Expansion Contexts:**
- Function calls: `f(args...)` → `f(arg0, arg1, arg2)`
- Initializers: `{ args... }` → `{ arg0, arg1, arg2 }`
- sizeof...: `sizeof...(Args)` → `3`
- Fold expressions: `(args + ...)` → `arg0 + arg1 + arg2`
- Multiple packs: Each expansion is independent

**Name Mangling:**
- Multiple pack expansions create longer names
- `call_pair<int, int, int, int, int, int>` → `call_pair__int_int_int__int_int_int`

## Current Transpiler Support

### What Works Today (via TemplateMonomorphizer)

✅ **Basic Class Templates:**
```cpp
template<typename T>
struct Container { T value; };

Container<int> c;  // Works - monomorphizes to Container__int
```

✅ **Basic Function Templates:**
```cpp
template<typename T>
T add(T a, T b) { return a + b; }

int x = add(1, 2);  // Works - monomorphizes to add__int
```

✅ **Template Specialization Detection:**
```cpp
template<typename T> struct Traits;
template<> struct Traits<int> { /* ... */ };  // Works - detected
```

✅ **Name Mangling:**
- Type-based name encoding
- Deduplication of identical instantiations
- Instantiation limit enforcement

### What Doesn't Work Today (Variadic-Specific)

❌ **Parameter Packs:**
```cpp
template<typename... Args>
void func(Args... args);  // Not supported - pack expansion needed
```

❌ **Fold Expressions:**
```cpp
template<typename... Args>
auto sum(Args... args) { return (args + ...); }  // Not supported
```

❌ **sizeof...() Operator:**
```cpp
template<typename... Args>
constexpr size_t count(Args...) { return sizeof...(Args); }  // Not supported
```

❌ **Variadic Class Templates:**
```cpp
template<typename... Types>
struct Tuple;  // Not supported - recursive structure needed
```

### Workarounds for Users

**Instead of Variadic Templates, Use:**

1. **Fixed-Arity Overloads:**
   ```cpp
   // Instead of: template<typename... Args> void print(Args... args)
   void print(int a);
   void print(int a, int b);
   void print(int a, int b, int c);
   ```

2. **Initializer Lists:**
   ```cpp
   // Instead of: template<typename... Args> T min(Args... args)
   template<typename T>
   T min(std::initializer_list<T> values);
   ```

3. **C-Style Variadic Functions:**
   ```cpp
   // Instead of: template<typename... Args> void log(Args... args)
   #include <cstdarg>
   void log(const char* fmt, ...);
   ```

4. **Container-Based Approaches:**
   ```cpp
   // Instead of: template<typename... Types> struct Tuple
   template<typename T>
   struct Vector { T* data; size_t size; };
   ```

## Future Implementation Notes

### If Variadic Templates Are Implemented

**Required Components:**

1. **PackExpansionAnalyzer** (Phase 59.1)
   - Detect `typename... Args` and `Args... args`
   - Analyze pack expansion contexts
   - Build pack expansion AST nodes

2. **FoldExpressionTranslator** (Phase 59.3)
   - Identify fold operators
   - Generate equivalent C expressions
   - Handle left/right fold variants

3. **VariadicMonomorphizer** (Phase 59.2)
   - Extend TemplateMonomorphizer
   - Handle pack expansion in monomorphization
   - Generate functions for each pack size

4. **sizeof...() Evaluator**
   - Evaluate pack size at monomorphization time
   - Substitute with integer literal

### Implementation Strategy

**Phase 1:** Simple parameter packs (no folds)
- `template<typename... Args> void f(Args... args)`
- Function call expansion: `g(args...)`
- Initializer expansion: `{ args... }`

**Phase 2:** Fold expressions
- Arithmetic folds: `(args + ...)`
- Logical folds: `(args && ...)`
- All fold operators

**Phase 3:** Advanced patterns
- Recursive pack expansion
- sizeof...() operator
- Perfect forwarding

**Estimated Effort:** 60-90 hours (per plan)

## Limitations and Best Practices

### Current Limitations

1. **No Variadic Template Support**
   - Parameter packs not recognized
   - Pack expansion not implemented
   - Fold expressions not translated
   - sizeof...() not evaluated

2. **No Runtime Variadic Behavior**
   - C variadic functions (stdarg.h) are separate feature
   - Template variadic is compile-time only
   - All instantiations must be known at compile time

3. **Code Bloat Concerns**
   - Each pack size generates separate function
   - Large packs → many functions
   - Deduplication helps but not eliminates

### Best Practices for Transpilable C++ Code

**DO:**
- ✅ Use fixed-arity templates when possible
- ✅ Use std::initializer_list for homogeneous types
- ✅ Limit pack sizes to reasonable numbers (<10)
- ✅ Use C-style varargs for truly runtime-variadic functions

**DON'T:**
- ❌ Use variadic templates extensively (not supported)
- ❌ Rely on fold expressions (C++17 not supported)
- ❌ Use recursive pack patterns (complex to transpile)
- ❌ Use variadic templates in library interfaces

### Alternative Patterns

**Pattern 1: Fixed Arity with Default Arguments**
```cpp
// Instead of variadic template
template<typename T>
void set_values(T* arr, T v1, T v2 = T(), T v3 = T(), T v4 = T());
```

**Pattern 2: Array or Vector**
```cpp
// Instead of variadic pack
template<typename T>
void process_all(const std::vector<T>& values);
```

**Pattern 3: Overload Set**
```cpp
// Instead of one variadic template
template<typename T> void func(T a);
template<typename T> void func(T a, T b);
template<typename T> void func(T a, T b, T c);
```

## Summary

| Feature | C++ Syntax | C Translation | Support Status |
|---------|------------|---------------|----------------|
| **Parameter Pack** | `typename... Args` | Separate parameters | ❌ Not Supported |
| **Pack Expansion** | `args...` | Individual args | ❌ Not Supported |
| **Fold Expression** | `(args + ...)` | Expanded operators | ❌ Not Supported |
| **sizeof...()** | `sizeof...(Args)` | Integer literal | ❌ Not Supported |
| **Variadic Constructor** | `Ctor(Args... args)` | Init function | ❌ Not Supported |
| **Perfect Forwarding** | `Args&&... args` | By-value params | ❌ Not Supported |
| **Recursive Pack** | `f(rest...)` | Function chain | ❌ Not Supported |
| **Basic Template** | `template<T>` | Monomorphization | ✅ Supported (Phase 11) |

**Key Takeaway:** Variadic templates are complex C++ feature with limited transpiler support. Use alternatives when possible. Future implementation will extend existing TemplateMonomorphizer with pack expansion logic.

---

**Documentation Status:** COMPLETE (Documentation-Only Phase)
**Last Updated:** 2025-12-27
**Related:** PHASE59-EVALUATION.md, PHASE59-SUMMARY.md, Phase 11 (Template Infrastructure)
