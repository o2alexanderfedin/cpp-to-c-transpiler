# Phase 59: Variadic Templates

**Status**: DEFERRED (VERY LOW Priority)
**Estimated Effort**: 60-90 hours
**Current Progress**: 0%
**Dependencies**: Phase 11 (Template Infrastructure)
**Target Completion**: Deferred until 80%+ C++ feature coverage

## Objective

Implement support for C++ variadic templates, enabling:
- Parameter packs (`template<typename... Args>`)
- Pack expansion (`Args...`, `args...`)
- Fold expressions (C++17): `(args + ...)`, `(... + args)`
- `sizeof...()` operator
- Perfect forwarding with variadic templates

## Context: Why This Is Deferred

### Complexity Factors

1. **Template Infrastructure Dependency**
   - Requires fully functional template system (Phase 11)
   - Phase 11 itself is complex and not yet implemented
   - Must handle template instantiation, type deduction, specialization

2. **Advanced Metaprogramming**
   - Variadic templates are primarily used for advanced metaprogramming
   - Not commonly needed in typical application code
   - Most use cases can be replaced with simpler alternatives

3. **Translation Complexity**
   - Parameter packs don't have direct C equivalents
   - Must generate multiple monomorphized versions
   - Fold expressions require complex code generation
   - Recursive expansion patterns are non-trivial

4. **Limited Real-World Need**
   - Most C++ code doesn't use variadic templates heavily
   - Can transpile 80%+ of C++ codebases without this feature
   - Libraries using variadic templates can often be replaced with C-compatible alternatives

### Strategic Decision

**Defer indefinitely** until:
- Phase 11 (templates) is fully complete and stable
- 80%+ of common C++ features are supported
- Real user demand emerges for this specific feature
- Template monomorphization infrastructure is proven

## Conceptual Translation Approach

IF implemented, variadic templates would be translated through **monomorphization** - generating separate code for each instantiation.

### Example 1: Simple Variadic Function

**C++ Input**:
```cpp
template<typename... Args>
void print(Args... args) {
    (std::cout << ... << args);  // Fold expression
}

// Usage
print(1, "hello", 3.14);
```

**Conceptual C Translation**:
```c
// Monomorphized for (int, const char*, double)
void print__int_cstr_double(int arg0, const char* arg1, double arg2) {
    printf("%d", arg0);
    printf("%s", arg1);
    printf("%f", arg2);
}

// Usage
print__int_cstr_double(1, "hello", 3.14);
```

### Example 2: Variadic Class Template

**C++ Input**:
```cpp
template<typename... Types>
struct Tuple {
    // Store types somehow
};

Tuple<int, float, char> t;
```

**Conceptual C Translation**:
```c
// Monomorphized for (int, float, char)
typedef struct {
    int field_0;
    float field_1;
    char field_2;
} Tuple__int_float_char;

Tuple__int_float_char t;
```

### Example 3: Recursive Parameter Pack

**C++ Input**:
```cpp
template<typename T>
T sum(T value) {
    return value;
}

template<typename T, typename... Args>
T sum(T first, Args... rest) {
    return first + sum(rest...);
}

int result = sum(1, 2, 3, 4);
```

**Conceptual C Translation**:
```c
// Base case
int sum__int(int value) {
    return value;
}

// Recursive cases - fully expanded
int sum__int_int_int_int(int first, int arg1, int arg2, int arg3) {
    return first + sum__int_int_int(arg1, arg2, arg3);
}

int sum__int_int_int(int first, int arg1, int arg2) {
    return first + sum__int_int(arg1, arg2);
}

int sum__int_int(int first, int arg1) {
    return first + sum__int(arg1);
}

// Usage
int result = sum__int_int_int_int(1, 2, 3, 4);
```

## Technical Challenges

### 1. Pack Expansion Analysis

**Challenge**: Determining all instantiations needed
- Must analyze all call sites across entire codebase
- Track which type combinations are actually used
- Generate only necessary monomorphizations

**Approach** (if implemented):
- Two-pass compilation:
  1. Collect all template instantiations
  2. Generate monomorphized versions
- Store instantiation registry in TranslationContext
- Deduplicate identical instantiations

### 2. Fold Expression Translation

**Challenge**: `(args + ...)` has no C equivalent

**Patterns**:
- Left fold: `(... op args)` → `((arg0 op arg1) op arg2) op arg3`
- Right fold: `(args op ...)` → `arg0 op (arg1 op (arg2 op arg3))`
- Unary/binary folds with init values

**Approach** (if implemented):
```cpp
// C++ fold expression
template<typename... Args>
auto sum(Args... args) {
    return (args + ...);
}

// Generated C code
int sum__int_int_int(int arg0, int arg1, int arg2) {
    return arg0 + arg1 + arg2;
}
```

### 3. Perfect Forwarding

**Challenge**: `std::forward<Args>(args)...` preserves value categories

**C Translation**:
- C doesn't have rvalue references
- Forwarding becomes simple parameter passing
- May lose some optimization opportunities

### 4. sizeof...() Operator

**Challenge**: `sizeof...(Args)` returns pack size at compile time

**Approach** (if implemented):
```cpp
// C++
template<typename... Args>
constexpr size_t count(Args... args) {
    return sizeof...(Args);
}

// C - directly substitute the number
size_t count__int_float_char(int arg0, float arg1, char arg2) {
    return 3;  // sizeof... evaluated at monomorphization time
}
```

## Implementation Strategy (IF Pursued)

### Phase 59.1: Analysis Infrastructure (20-30 hrs)

**Objective**: Detect and analyze variadic templates

**Tasks**:
1. Extend template analyzer to detect parameter packs
2. Identify pack expansion patterns
3. Analyze fold expressions
4. Track sizeof...() operators

**Deliverables**:
- PackExpansionAnalyzer class
- FoldExpressionAnalyzer class
- Test suite for detection

### Phase 59.2: Monomorphization Engine (25-35 hrs)

**Objective**: Generate monomorphized versions

**Tasks**:
1. Implement pack expansion logic
2. Generate function/struct for each instantiation
3. Handle recursive pack patterns
4. Manage name mangling for variadic instantiations

**Deliverables**:
- VariadicMonomorphizer class
- Instantiation registry
- Name mangling for packs
- Test suite for monomorphization

### Phase 59.3: Fold Expression Translation (15-25 hrs)

**Objective**: Translate fold expressions to C

**Tasks**:
1. Identify fold expression patterns
2. Generate equivalent C expressions
3. Handle unary/binary folds
4. Support all fold operators

**Deliverables**:
- FoldExpressionTranslator class
- Operator-specific fold handlers
- Test suite for all fold patterns

## Dependencies

### Hard Dependencies

1. **Phase 11: Template Infrastructure** (REQUIRED)
   - Template instantiation mechanism
   - Type deduction
   - Template specialization
   - Template monomorphization

2. **Robust Type System** (REQUIRED)
   - Type inference
   - Type compatibility checking
   - Type substitution

### Soft Dependencies

1. **Phase 13: Lambdas**
   - Variadic lambdas: `[](auto... args) {}`
   - Generic lambda support

2. **Phase 35: std::tuple**
   - Tuple is implemented with variadic templates
   - May need special handling

## Success Criteria (IF Implemented)

### Functional Requirements

- [ ] **Parameter Packs**
  - Detect variadic template declarations
  - Analyze parameter pack usage
  - Generate monomorphized versions

- [ ] **Pack Expansion**
  - Function parameter expansion: `f(args...)`
  - Template argument expansion: `Tuple<Args...>`
  - Expression expansion: `(args + ...)`

- [ ] **Fold Expressions**
  - Unary left fold: `(... op args)`
  - Unary right fold: `(args op ...)`
  - Binary left fold: `(init op ... op args)`
  - Binary right fold: `(args op ... op init)`
  - All fold operators: `+, -, *, /, %, &, |, ^, <<, >>, &&, ||, ,`

- [ ] **sizeof...() Operator**
  - Evaluate pack size at compile time
  - Substitute with constant in C code

### Quality Requirements

- [ ] **Test Coverage**: 95%+ for all variadic features
- [ ] **Documentation**: Complete conceptual model
- [ ] **Performance**: Minimal code bloat from monomorphization
- [ ] **Error Handling**: Clear diagnostics for unsupported patterns

### Validation Cases

1. **Simple Variadic Function**
   ```cpp
   template<typename... Args>
   void log(Args... args);
   ```

2. **Variadic Class Template**
   ```cpp
   template<typename... Types>
   struct Tuple { /* ... */ };
   ```

3. **Recursive Pack Expansion**
   ```cpp
   template<typename T, typename... Rest>
   T max(T first, Rest... rest);
   ```

4. **Fold Expressions (C++17)**
   ```cpp
   template<typename... Args>
   auto sum(Args... args) { return (args + ...); }
   ```

5. **Perfect Forwarding**
   ```cpp
   template<typename... Args>
   void forward_call(Args&&... args);
   ```

## Risks and Mitigations

### Risk 1: Exponential Code Bloat

**Problem**: Too many instantiations → huge C output

**Mitigation**:
- Implement smart deduplication
- Share code between similar instantiations
- Warn when excessive instantiations detected
- Allow user-configurable instantiation limits

### Risk 2: Complex Fold Expressions

**Problem**: Nested folds, custom operators

**Mitigation**:
- Start with simple arithmetic folds
- Document unsupported patterns clearly
- Provide workaround suggestions
- Implement incrementally

### Risk 3: Template Metaprogramming Patterns

**Problem**: Variadic templates often used with SFINAE, type traits, etc.

**Mitigation**:
- Defer until Phase 62 (SFINAE) if needed
- Focus on simple use cases first
- Document advanced patterns as unsupported

## Recommendation

**DEFER INDEFINITELY**

**Rationale**:
1. Requires Phase 11 (templates) which is itself complex
2. Used in <20% of typical C++ codebases
3. High implementation cost vs. benefit
4. Can transpile most C++ code without it
5. Libraries using variadic templates can often be replaced

**Alternative Approach**:
- Users can manually refactor variadic templates to non-variadic versions
- Provide migration guide for common patterns
- Focus effort on more impactful features

**Reconsideration Triggers**:
- Phase 11 is complete and stable
- 80%+ C++ feature coverage achieved
- Multiple users request this specific feature
- Template metaprogramming becomes blocking issue

## Resources

### Research Materials

- C++ Template Metaprogramming patterns
- Variadic template instantiation algorithms
- Code generation for pack expansion
- Fold expression semantics (C++17)

### Related Phases

- **Phase 11**: Template Infrastructure (prerequisite)
- **Phase 13**: Lambdas (variadic lambdas)
- **Phase 35**: std::tuple (uses variadic templates)
- **Phase 62**: SFINAE (often combined with variadic templates)

### Example Codebases

- Boost.MP11 (metaprogramming library)
- std::tuple implementation
- Variadic logging libraries
- Generic container libraries

## Notes

- This is a **placeholder plan** for a deferred feature
- Detailed design deferred until prerequisites are met
- May be superseded by simpler approaches
- Low priority - focus on core features first

---

**Last Updated**: 2025-12-26
**Status**: DEFERRED (VERY LOW Priority)
**Next Review**: After Phase 11 completion
