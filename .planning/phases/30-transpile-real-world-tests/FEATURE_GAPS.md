# Feature Gaps Identified During Real-World Transpilation Attempt

**Phase**: 30-01
**Date**: 2025-12-24

## Summary

Attempting to transpile 5 real-world C++ test projects revealed significant gaps between the transpiler's current capabilities and the features required by production C++ code.

## Feature Support Matrix

| Feature Category | Feature | Status | Priority | Effort | Blocker |
|-----------------|---------|--------|----------|--------|---------|
| **STL Support** | | | | | |
| | std::string | ❌ Not Supported | CRITICAL | HIGH | YES |
| | std::vector<T> | ❌ Not Supported | CRITICAL | HIGH | YES |
| | std::map<K,V> | ❌ Not Supported | CRITICAL | HIGH | YES |
| | std::unique_ptr<T> | ❌ Not Supported | CRITICAL | MEDIUM | YES |
| | std::shared_ptr<T> | ❌ Not Supported | CRITICAL | MEDIUM | YES |
| | std::function<> | ❌ Not Supported | HIGH | MEDIUM | NO |
| | std::optional<T> | ❌ Not Supported | MEDIUM | LOW | NO |
| | std::variant<Ts...> | ❌ Not Supported | MEDIUM | MEDIUM | NO |
| | std::array<T,N> | ❌ Not Supported | LOW | LOW | NO |
| | STL algorithms | ❌ Not Supported | HIGH | HIGH | NO |
| **Language Features** | | | | | |
| | Basic classes | ✅ Supported | - | - | - |
| | Single inheritance | ✅ Supported | - | - | - |
| | Multiple inheritance | ⚠️  Partial | MEDIUM | MEDIUM | NO |
| | Virtual inheritance | ❌ Not Supported | LOW | HIGH | NO |
| | Virtual methods | ✅ Supported | - | - | - |
| | Pure virtual methods | ✅ Supported | - | - | - |
| | Operator overloading | ⚠️  Partial | MEDIUM | MEDIUM | NO |
| | Move semantics | ❌ Not Supported | HIGH | HIGH | YES |
| | Rvalue references | ❌ Not Supported | HIGH | HIGH | YES |
| | Perfect forwarding | ❌ Not Supported | MEDIUM | HIGH | NO |
| | RAII (basic) | ⚠️  Partial | HIGH | MEDIUM | NO |
| | RAII (complex) | ❌ Not Supported | HIGH | HIGH | YES |
| **Templates** | | | | | |
| | Class templates (simple) | ⚠️  Partial | HIGH | MEDIUM | NO |
| | Function templates | ⚠️  Partial | HIGH | MEDIUM | NO |
| | Variadic templates | ❌ Not Supported | HIGH | HIGH | YES |
| | Template specialization | ❌ Not Supported | MEDIUM | HIGH | NO |
| | SFINAE | ❌ Not Supported | LOW | HIGH | NO |
| | Concepts (C++20) | ❌ Not Supported | LOW | HIGH | NO |
| | Template template params | ❌ Not Supported | LOW | HIGH | NO |
| **Exception Handling** | | | | | |
| | try/catch (basic) | ⚠️  Partial | HIGH | MEDIUM | NO |
| | try/catch (complex) | ❌ Not Supported | HIGH | HIGH | YES |
| | Exception propagation | ⚠️  Partial | HIGH | MEDIUM | NO |
| | std::exception hierarchy | ❌ Not Supported | HIGH | MEDIUM | NO |
| | RAII + exceptions | ❌ Not Supported | CRITICAL | HIGH | YES |
| | noexcept specifier | ❌ Not Supported | MEDIUM | LOW | NO |
| **Modern C++ (C++11+)** | | | | | |
| | auto type deduction | ⚠️  Partial | HIGH | LOW | NO |
| | Range-based for loops | ❌ Not Supported | HIGH | MEDIUM | YES |
| | Lambda expressions | ❌ Not Supported | HIGH | HIGH | YES |
| | constexpr | ⚠️  Partial | MEDIUM | MEDIUM | NO |
| | nullptr | ✅ Supported | - | - | - |
| | enum class | ⚠️  Partial | MEDIUM | LOW | NO |
| | Delegating constructors | ⚠️  Partial | LOW | LOW | NO |
| | Uniform initialization | ❌ Not Supported | MEDIUM | MEDIUM | NO |
| **Multi-File Support** | | | | | |
| | Include path resolution | ❌ Not Supported | CRITICAL | LOW | YES |
| | Multi-file transpilation | ❌ Not Supported | CRITICAL | HIGH | YES |
| | Shared type definitions | ❌ Not Supported | CRITICAL | MEDIUM | YES |
| | Header generation | ⚠️  Partial | HIGH | MEDIUM | NO |
| | Forward declarations | ⚠️  Partial | MEDIUM | LOW | NO |
| **Tooling** | | | | | |
| | Error diagnostics | ⚠️  Poor | CRITICAL | MEDIUM | YES |
| | Include path flags (-I) | ❌ Not Supported | CRITICAL | LOW | YES |
| | Warning suppression | ❌ Not Supported | LOW | LOW | NO |
| | Verbose mode | ❌ Not Supported | MEDIUM | LOW | NO |
| | Feature detection | ❌ Not Supported | HIGH | LOW | NO |

## Legend

- ✅ **Supported**: Feature works reliably
- ⚠️  **Partial**: Feature works in simple cases but fails in complex scenarios
- ❌ **Not Supported**: Feature does not work or is not implemented

**Priority Levels**:
- **CRITICAL**: Blocks real-world usage
- **HIGH**: Severely limits usability
- **MEDIUM**: Limits usability for some use cases
- **LOW**: Nice to have

**Effort Levels**:
- **LOW**: Days to 1 week
- **MEDIUM**: 1-4 weeks
- **HIGH**: 1-6 months

**Blocker**: Whether this feature prevents transpiling any real-world code

## Critical Blockers (Must Fix)

### 1. STL Support (std::string, std::vector, std::map)
**Impact**: Blocks 100% of modern C++ code
**Effort**: HIGH (3-6 months for comprehensive support)

**Why it's blocking**:
- Every real-world project uses `std::string`
- Most projects use `std::vector<T>`
- Many projects use `std::map<K,V>` or `std::unordered_map<K,V>`
- No practical workaround exists

**Possible Solutions**:
1. **Full C Implementation** (recommended but massive effort)
   - Implement C versions of STL containers
   - `struct String { char* data; size_t len; size_t cap; }`
   - `struct Vector_T { T* data; size_t len; size_t cap; }`
   - Provide all standard methods (push_back, insert, erase, etc.)
   - Estimated: 5000-10000 LOC, 3-6 months

2. **Mapping to Existing C Libraries**
   - Use glib (GString, GArray, GHashTable)
   - Requires glib dependency
   - Licensing concerns
   - Translation more complex

3. **Scope Reduction**
   - Define "No-STL C++" subset
   - Require users to replace STL with custom types
   - Document migration guide
   - Least effort but limits usefulness

### 2. Include Path Resolution
**Impact**: Blocks multi-file projects
**Effort**: LOW (1-3 days)

**Why it's blocking**:
- Test files include project headers: `#include "JsonParser.h"`
- Transpiler can't find these headers
- Results in compilation errors

**Solution**:
```bash
# Add -I flag support to transpiler-api-cli
transpiler-api-cli input.cpp --json -I./include -I../common
```

**Implementation**:
- Modify CLI argument parsing
- Pass include paths to Clang frontend
- Already supported by Clang, just need to expose in CLI

### 3. Move Semantics and Rvalue References
**Impact**: Blocks modern C++ codebases
**Effort**: HIGH (1-2 months)

**Why it's blocking**:
- Resource manager project uses `std::move()`
- Smart pointers require move semantics
- Copy elision depends on rvalue references

**Solution**:
- Detect move constructors and move assignment operators
- Generate C code that transfers ownership
- Implement shallow copy + clear for move operations
- Add runtime flags to track ownership

### 4. Range-Based For Loops
**Impact**: Blocks idiomatic modern C++
**Effort**: MEDIUM (1-2 weeks)

**Why it's blocking**:
```cpp
// C++
for (const auto& item : items) {
    process(item);
}

// Needs to become C
for (size_t i = 0; i < items.size; i++) {
    const Item* item = &items.data[i];
    process(item);
}
```

**Solution**:
- Detect range-based for loops in AST
- Extract container and element type
- Generate traditional for loop with index
- Handle different container types (vector, map, etc.)

### 5. Lambda Expressions
**Impact**: Blocks functional programming patterns
**Effort**: HIGH (2-3 months)

**Why it's blocking**:
```cpp
// C++
auto pred = [threshold](int x) { return x > threshold; };
std::remove_if(vec.begin(), vec.end(), pred);

// Needs to become C (complex)
struct lambda_capture_1 {
    int threshold;
};

int lambda_func_1(struct lambda_capture_1* capture, int x) {
    return x > capture->threshold;
}

// ... generate closure and pass to C equivalent of remove_if
```

**Solution**:
- Generate struct for captured variables
- Generate function pointer for lambda body
- Create closure initialization code
- Handle different capture modes (=, &, specific vars)

### 6. RAII + Exceptions
**Impact**: Blocks exception-safe code
**Effort**: HIGH (1-2 months)

**Why it's blocking**:
```cpp
// C++
void processFile(const std::string& path) {
    std::ifstream file(path);  // RAII opens file
    if (!file) throw FileError();
    // ...
} // RAII closes file even if exception thrown
```

**Current Issue**:
- RAII works (constructor/destructor)
- Exceptions work (SJLJ)
- But cleanup during stack unwinding is incomplete

**Solution**:
- Enhance exception frame tracking
- Register destructors for each stack object
- Call destructors during unwinding
- Test with complex scenarios

## High-Priority Non-Blockers

### 7. Variadic Templates
**Impact**: Limits template metaprogramming
**Effort**: HIGH (1-2 months)

**Example**:
```cpp
// C++ (string-formatter project)
template<typename... Args>
std::string format(const std::string& fmt, Args&&... args);

// Needs monomorphization for each call site
format("Name: {}, Age: {}", name, age);
// -> generate format_string_int(...)

format("X: {}, Y: {}, Z: {}", x, y, z);
// -> generate format_string_int_int(...)
```

### 8. Lambda Expressions
(See Critical Blockers #5)

### 9. Complex Template Scenarios
**Impact**: Limits advanced C++ usage
**Effort**: HIGH (2-4 months)

**Examples**:
- Template specialization
- SFINAE
- Template template parameters
- Dependent types

### 10. std::function and Type Erasure
**Impact**: Limits callback patterns
**Effort**: MEDIUM (2-3 weeks)

**Example**:
```cpp
std::function<int(int, int)> operation = std::plus<int>();
```

**Solution**:
- Generate struct with function pointer and context
- Similar to lambda but standardized interface

## Medium-Priority Items

- `std::optional<T>` - Useful but can work around with pointers
- `std::variant<Ts...>` - Can use union + tag
- Uniform initialization `{}` - Can use explicit constructors
- constexpr (full support) - Can evaluate at runtime
- Template specialization - Limits generic programming but not critical

## Low-Priority Items

- Virtual inheritance - Rare in practice
- Concepts (C++20) - Can use SFINAE
- Template template parameters - Advanced feature
- SFINAE - Can simplify templates
- `std::array<T,N>` - Can use C arrays

## Recommended Implementation Order

### Phase 1: Unblock Basic Usage (1-2 weeks)
1. Include path resolution (-I flag) - 2 days
2. Error diagnostics improvement - 3 days
3. Fix assertion failures - 2 days
4. Add --verbose flag - 1 day
5. Create simple validation tests - 2 days

### Phase 2: Core Language Features (1-2 months)
6. Range-based for loops - 1 week
7. Auto type deduction (full) - 1 week
8. Move semantics (basic) - 2 weeks
9. RAII + exceptions (robust) - 2 weeks
10. Operator overloading (complete) - 1 week

### Phase 3: STL Foundation (3-4 months)
11. std::string C implementation - 1 month
12. std::vector<T> C implementation - 1 month
13. std::unique_ptr<T> C implementation - 2 weeks
14. std::shared_ptr<T> C implementation - 3 weeks
15. std::map<K,V> C implementation - 1 month

### Phase 4: Advanced Features (2-3 months)
16. Lambda expressions - 1 month
17. Variadic templates - 1 month
18. std::function<> - 2 weeks
19. Template specialization - 3 weeks

### Phase 5: Multi-File Support (1 month)
20. Multi-file transpilation - 2 weeks
21. Shared type definitions - 1 week
22. Header dependency analysis - 1 week

## Total Estimated Effort

**Minimum Viable** (Phase 1-2): 2-3 months
**Production Ready** (Phase 1-3): 5-7 months
**Feature Complete** (Phase 1-5): 10-14 months

**Note**: These are engineering estimates assuming 1 full-time developer. Multiply by 1.5-2x for realistic project timelines.

## Alternative Approaches

### Option A: Scope Reduction
Define "Transpilable C++" as a strict subset:
- No STL (provide custom containers)
- No lambdas (use function pointers)
- No move semantics (copy-only)
- No variadic templates (fixed arity)

**Pros**: Achievable in 1-2 months
**Cons**: Very limited usefulness, users must rewrite code

### Option B: Hybrid Approach
- Transpile C++ to C++11/C++14 (simpler target)
- Use existing C++ to C transpilers (Cfront model)
- Focus on specific domains (embedded, real-time)

**Pros**: Leverage existing tools
**Cons**: Not pure C output

### Option C: C Wrapper Generation
Instead of full transpilation, generate C wrapper APIs:
- Keep C++ code as-is
- Generate extern "C" wrappers
- Provide C-compatible interface layer

**Pros**: Much easier (weeks not months)
**Cons**: Not true transpilation, still requires C++ compiler

## Conclusion

Real-world C++ transpilation requires:
1. **STL Support** (critical, 3-6 months)
2. **Modern Language Features** (move, lambdas, etc., 2-3 months)
3. **Multi-File Coordination** (1 month)
4. **Robust Error Handling** (2 weeks)

**Total realistic timeline**: 10-14 months of dedicated development

**Recommended strategy**: Start with Phase 1 (unblock basic usage), then re-evaluate whether full STL implementation is worth the investment vs. alternative approaches.
