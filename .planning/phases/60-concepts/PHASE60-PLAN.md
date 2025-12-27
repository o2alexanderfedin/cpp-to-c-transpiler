# Phase 60: Concepts (C++20)

**Status**: DEFERRED (VERY LOW Priority)
**Estimated Effort**: 100-150 hours
**Current Progress**: 0%
**Dependencies**: Phase 11 (Template Infrastructure)
**Target Completion**: Deferred until C++20 adoption is widespread

## Objective

Implement support for C++20 Concepts, enabling:
- Named constraints on template parameters: `template<Sortable T>`
- Concept definitions: `concept Integral = std::is_integral_v<T>;`
- `requires` clauses: `requires(T a, T b) { a + b; }`
- `requires` expressions
- Constrained auto: `Integral auto x = 5;`
- Abbreviated function templates: `void sort(Sortable auto& container)`

## Context: Why This Is Deferred

### Complexity Factors

1. **C++20 Feature - Limited Adoption**
   - C++20 is relatively new (2020)
   - Many codebases still use C++11, C++14, C++17
   - Compiler support varies (GCC 10+, Clang 10+, MSVC 2019+)
   - Low priority until widespread adoption

2. **Compile-Time Only Feature**
   - Concepts are purely compile-time constraints
   - Don't affect runtime behavior
   - Primarily improve error messages and documentation
   - Limited value in transpilation context

3. **Template System Dependency**
   - Requires fully functional template system (Phase 11)
   - Phase 11 itself is complex and not yet implemented
   - Concepts add another layer of complexity

4. **Translation Strategy Unclear**
   - C has no equivalent to concepts
   - Options:
     - Strip concepts entirely (treat as comments)
     - Validate at transpile time, then remove
     - Generate runtime assertions
   - Each approach has trade-offs

5. **Low ROI (Return on Investment)**
   - Massive implementation effort (100-150 hrs)
   - Benefits mostly compile-time error checking
   - Most C++ code doesn't use concepts yet
   - Can transpile 95%+ of C++ code without concepts

### Strategic Decision

**Defer indefinitely** until:
- C++20 adoption becomes widespread (50%+ of codebases)
- Phase 11 (templates) is fully complete and stable
- Clear user demand emerges
- Better translation strategy is identified

## Conceptual Translation Approach

Concepts are **compile-time constraints** - they don't generate code, they validate types.

### Option 1: Strip Concepts (Simplest)

**C++ Input**:
```cpp
template<typename T>
concept Addable = requires(T a, T b) {
    { a + b } -> std::convertible_to<T>;
};

template<Addable T>
T add(T a, T b) {
    return a + b;
}

int result = add(5, 3);
```

**C Translation**:
```c
// Concept definition → removed entirely

// Template with concept constraint → regular monomorphized function
int add__int(int a, int b) {
    return a + b;
}

int result = add__int(5, 3);
```

**Pros**: Simple, no runtime overhead
**Cons**: Lose compile-time validation, errors delayed to C compilation

### Option 2: Validate Then Strip (Better)

**Approach**:
1. Evaluate concept constraints during transpilation
2. Reject invalid instantiations with helpful errors
3. Remove concepts from generated C code

**C++ Input**:
```cpp
template<std::integral T>
T multiply(T a, T b) {
    return a * b;
}

auto x = multiply(5, 3);        // OK
auto y = multiply(1.5, 2.0);    // ERROR during transpilation
```

**Transpilation**:
```
✓ multiply<int> satisfies std::integral → generate code
✗ multiply<double> violates std::integral → error: "double does not satisfy concept std::integral"
```

**C Output**:
```c
// Only valid instantiation
int multiply__int(int a, int b) {
    return a * b;
}

int x = multiply__int(5, 3);
// float instantiation rejected - no code generated
```

**Pros**: Catches errors early, good error messages
**Cons**: Complex to implement, requires constraint evaluation engine

### Option 3: Runtime Assertions (Worst)

**C++ Input**:
```cpp
template<std::floating_point T>
T sqrt_approx(T x) {
    return /* ... */;
}
```

**C Translation**:
```c
// Generic version with runtime type check
void sqrt_approx__double(double x) {
    assert(/* is_floating_point<double> */);  // Always true, pointless
    // ...
}
```

**Pros**: None
**Cons**: Runtime overhead, defeats purpose of concepts, complex

### Recommended Approach: Option 2 (If Implemented)

**Validate at transpile time, strip from C output**

This preserves the intent of concepts (early error detection) while generating clean C code.

## Technical Challenges

### 1. Concept Definition Analysis

**Challenge**: Parse and understand concept definitions

**C++ Syntax**:
```cpp
template<typename T>
concept Sortable = requires(T a, T b) {
    { a < b } -> std::convertible_to<bool>;
    { a > b } -> std::convertible_to<bool>;
};
```

**Required**:
- Parse `requires` expressions
- Understand expression requirements
- Evaluate type requirements
- Check return type constraints (`->` syntax)

### 2. Constraint Evaluation

**Challenge**: Determine if type satisfies concept

**Requires**:
- Type trait evaluation (Phase 14)
- SFINAE-like substitution (Phase 62)
- Expression validity checking
- Return type compatibility

**Example**:
```cpp
concept HasSize = requires(T t) {
    { t.size() } -> std::convertible_to<size_t>;
};

struct Vector { size_t size(); };  // Satisfies
struct List { int length(); };      // Doesn't satisfy (wrong return type)
```

### 3. Constrained Template Instantiation

**Challenge**: Filter template instantiations based on concepts

**C++**:
```cpp
template<std::integral T>
void process(T value);

process(42);      // OK - int is integral
process(3.14);    // ERROR - double is not integral
```

**Transpiler Must**:
- Evaluate concept for each instantiation
- Reject invalid instantiations with clear errors
- Only generate code for valid instantiations

### 4. Abbreviated Function Templates

**Challenge**: `auto` parameters with concept constraints

**C++**:
```cpp
void print(Printable auto value) {
    std::cout << value;
}
```

**Equivalent to**:
```cpp
template<Printable T>
void print(T value) {
    std::cout << value;
}
```

**Transpiler Must**:
- Detect abbreviated syntax
- Expand to full template
- Apply concept constraints

### 5. Standard Library Concepts

**Challenge**: C++20 defines many standard concepts

**Examples**:
- `std::integral`, `std::floating_point`, `std::signed_integral`
- `std::same_as<T, U>`, `std::derived_from<T, U>`
- `std::convertible_to<T, U>`, `std::constructible_from<T, Args...>`
- `std::movable`, `std::copyable`, `std::swappable`
- `std::sortable`, `std::random_access_iterator`

**Required**:
- Implement evaluation logic for each standard concept
- May require Phase 14 (Type Traits)
- Complex interdependencies

## Implementation Strategy (IF Pursued)

### Phase 60.1: Concept Definition Analysis (30-40 hrs)

**Objective**: Parse and represent concept definitions

**Tasks**:
1. Detect concept definitions in C++ AST
2. Parse `requires` expressions
3. Extract constraint requirements
4. Build internal concept representation

**Deliverables**:
- ConceptDefinition AST node
- RequiresExpression analyzer
- Constraint representation
- Test suite for concept parsing

**AST Nodes**:
```cpp
class ConceptDefinition {
    std::string name;
    std::vector<TemplateParameter> params;
    RequiresExpression constraints;
};

class RequiresExpression {
    std::vector<ExpressionRequirement> expr_reqs;
    std::vector<TypeRequirement> type_reqs;
    std::vector<NestedRequirement> nested_reqs;
};
```

### Phase 60.2: Constraint Evaluation Engine (40-60 hrs)

**Objective**: Evaluate if types satisfy concepts

**Tasks**:
1. Implement type trait evaluation
2. Check expression validity
3. Verify return type constraints
4. Handle nested concepts

**Deliverables**:
- ConceptEvaluator class
- Type trait evaluator
- Expression checker
- Test suite for constraint evaluation

**Example Usage**:
```cpp
ConceptEvaluator evaluator;
Type type = /* int */;
ConceptDefinition concept = /* std::integral */;

bool satisfies = evaluator.evaluate(type, concept);
// Returns: true (int is integral)
```

### Phase 60.3: Constrained Template Handling (30-50 hrs)

**Objective**: Apply concepts to template instantiation

**Tasks**:
1. Detect concept-constrained templates
2. Evaluate constraints for each instantiation
3. Reject invalid instantiations
4. Generate helpful error messages

**Deliverables**:
- ConstrainedTemplateHandler class
- Instantiation validator
- Error message generator
- Test suite for template constraints

**Error Message Example**:
```
Error: Cannot instantiate sort<std::string>
  Constraint violation: std::string does not satisfy concept Numeric
  Required: operator<(T, T) -> bool
  Problem: std::string::operator< is not defined
```

## Dependencies

### Hard Dependencies

1. **Phase 11: Template Infrastructure** (REQUIRED)
   - Template instantiation mechanism
   - Type deduction
   - Template specialization
   - Cannot implement concepts without templates

2. **Phase 14: Type Traits** (REQUIRED)
   - Many standard concepts use type traits
   - `std::is_integral`, `std::is_same`, etc.
   - Constraint evaluation depends on type traits

### Soft Dependencies

1. **Phase 62: SFINAE**
   - Concepts replace many SFINAE use cases
   - Similar constraint checking logic
   - May share implementation

2. **Phase 59: Variadic Templates**
   - Some concepts constrain parameter packs
   - `std::constructible_from<T, Args...>`

## Success Criteria (IF Implemented)

### Functional Requirements

- [ ] **Concept Definitions**
  - Parse concept definitions
  - Support `requires` expressions
  - Handle nested concepts
  - Support conjunctions/disjunctions

- [ ] **Concept Constraints**
  - Apply concepts to template parameters
  - Validate instantiations
  - Reject invalid types with clear errors

- [ ] **Abbreviated Syntax**
  - Constrained auto: `Sortable auto x`
  - Abbreviated function templates: `void f(Numeric auto x)`

- [ ] **Standard Library Concepts**
  - Implement core language concepts (integral, floating_point, etc.)
  - Implement comparison concepts (equality_comparable, totally_ordered)
  - Implement object concepts (movable, copyable, swappable)
  - Document unsupported concepts

### Quality Requirements

- [ ] **Test Coverage**: 90%+ for all concept features
- [ ] **Error Messages**: Clear, actionable diagnostics
- [ ] **Performance**: Constraint evaluation <100ms per template
- [ ] **Documentation**: Complete guide to supported concepts

### Validation Cases

1. **Simple Concept**
   ```cpp
   template<typename T>
   concept Numeric = std::is_arithmetic_v<T>;

   template<Numeric T>
   T add(T a, T b) { return a + b; }
   ```

2. **Requires Expression**
   ```cpp
   template<typename T>
   concept HasSize = requires(T t) {
       { t.size() } -> std::convertible_to<size_t>;
   };
   ```

3. **Multiple Constraints**
   ```cpp
   template<typename T>
   concept Sortable = std::totally_ordered<T> && std::swappable<T>;
   ```

4. **Constrained Auto**
   ```cpp
   std::integral auto x = 5;
   std::floating_point auto y = 3.14;
   ```

5. **Subsumption (Advanced)**
   ```cpp
   template<std::integral T>
   void f(T x);  // Less constrained

   template<std::signed_integral T>
   void f(T x);  // More constrained - preferred
   ```

## Risks and Mitigations

### Risk 1: C++20 Adoption is Slow

**Problem**: Feature may be rarely used for years

**Mitigation**:
- Monitor C++20 adoption rates
- Defer until demand is clear
- Focus on more impactful features first

### Risk 2: Complex Constraint Evaluation

**Problem**: Evaluating arbitrary requires expressions is hard

**Mitigation**:
- Start with simple concepts only
- Gradually add complexity
- Document unsupported patterns
- Provide clear error messages

### Risk 3: Standard Library Dependency

**Problem**: Many concepts depend on <concepts>, <type_traits>

**Mitigation**:
- Implement standard concepts incrementally
- Start with language concepts (integral, etc.)
- Defer library concepts (ranges, etc.)
- Allow user-defined concepts first

### Risk 4: Interaction with Other Features

**Problem**: Concepts interact with templates, SFINAE, overload resolution

**Mitigation**:
- Implement in isolation first
- Integration testing with templates
- Defer complex interactions
- Document known limitations

## Alternative Approach: Concept Stripping

**Simplest Implementation**:

Instead of evaluating concepts, simply **strip them** from the code:

1. **Detect** concept-constrained templates
2. **Remove** concept constraints
3. **Generate** unconstrained monomorphized functions
4. **Rely** on C compiler to catch type errors

**Example**:
```cpp
// C++ with concepts
template<std::integral T>
T add(T a, T b) { return a + b; }

// Transpiled C (concepts removed)
int add__int(int a, int b) { return a + b; }
```

**Pros**:
- Extremely simple (hours vs. weeks)
- No constraint evaluation needed
- C compiler catches most errors anyway

**Cons**:
- Lose early error detection
- Error messages are worse
- Invalid instantiations might generate code

**Recommendation**: If concepts support is needed urgently, use stripping approach first.

## Recommendation

**DEFER INDEFINITELY**

**Rationale**:
1. **C++20 is too new**: Limited adoption, many codebases use older standards
2. **Compile-time only**: Doesn't affect runtime behavior, limited value in transpilation
3. **Massive effort**: 100-150 hours for marginal benefit
4. **Low demand**: Most C++ code doesn't use concepts yet
5. **Alternative exists**: Concept stripping is trivial if needed

**When to Reconsider**:
- C++20 adoption reaches 50%+ of C++ codebases
- Phase 11 (templates) is complete and stable
- Multiple users request concept support
- Becomes blocking issue for target codebases

**Interim Solution**:
- Provide concept-stripping tool
- Document manual workarounds
- Guide users to refactor concepts to type traits/SFINAE

## Resources

### Research Materials

- C++20 Concepts specification (ISO/IEC 14882:2020)
- Constraint evaluation algorithms
- Type trait implementation
- Concept subsumption rules

### Related Phases

- **Phase 11**: Template Infrastructure (prerequisite)
- **Phase 14**: Type Traits (prerequisite)
- **Phase 62**: SFINAE (related constraint mechanism)
- **Phase 59**: Variadic Templates (concepts can constrain packs)

### Example Codebases

- C++20 Ranges library (heavy concept usage)
- Boost.Concept (pre-C++20 concept emulation)
- Modern C++ libraries using concepts

### Standard Concepts Reference

**Core Language Concepts**:
- `same_as`, `derived_from`, `convertible_to`, `common_reference_with`
- `integral`, `signed_integral`, `unsigned_integral`, `floating_point`

**Comparison Concepts**:
- `equality_comparable`, `totally_ordered`

**Object Concepts**:
- `movable`, `copyable`, `semiregular`, `regular`

**Callable Concepts**:
- `invocable`, `predicate`, `relation`, `strict_weak_order`

## Notes

- This is a **placeholder plan** for a deferred C++20 feature
- Detailed design deferred until C++20 becomes mainstream
- May be superseded by simpler concept-stripping approach
- **VERY LOW PRIORITY** - focus on C++11/14/17 features first

---

**Last Updated**: 2025-12-26
**Status**: DEFERRED (VERY LOW Priority)
**Next Review**: When C++20 adoption reaches 30%
