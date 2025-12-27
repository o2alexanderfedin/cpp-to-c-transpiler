# Phase 62: SFINAE (Substitution Failure Is Not An Error)

**Status**: DEFERRED (VERY LOW Priority)
**Estimated Effort**: 120-180 hours
**Current Progress**: 0%
**Dependencies**: Phase 11 (Template Infrastructure), Phase 14 (Type Traits)
**Target Completion**: Deferred until advanced metaprogramming becomes necessary

## Objective

Implement support for SFINAE (Substitution Failure Is Not An Error), enabling:
- Template overload resolution based on type properties
- `std::enable_if` for conditional template instantiation
- SFINAE-friendly type trait checks
- Expression SFINAE: `decltype(expr)` validity checking
- `std::void_t` for detecting valid expressions
- Compile-time function/class selection based on type capabilities

## Context: Why This Is Deferred

### Complexity Factors

1. **Advanced Template Metaprogramming**
   - SFINAE is one of the most complex C++ features
   - Requires deep understanding of template instantiation
   - Primarily used in library development, not application code
   - Most programmers avoid SFINAE when possible

2. **Template Infrastructure Dependency**
   - Requires fully functional template system (Phase 11)
   - Phase 11 itself is complex and not yet implemented
   - SFINAE adds another layer of complexity on top
   - Cannot implement until templates are stable

3. **Type Trait Dependency**
   - Most SFINAE patterns use type traits (Phase 14)
   - `std::enable_if`, `std::is_*`, `std::void_t`, etc.
   - Need type trait evaluation engine
   - Circular dependency with type traits

4. **Modern C++ Provides Alternatives**
   - C++20 Concepts (Phase 60) replace many SFINAE use cases
   - `if constexpr` (C++17) simplifies many patterns
   - C++20 encourages moving away from SFINAE
   - Industry trend is to deprecate SFINAE in favor of concepts

5. **Translation to C is Extremely Complex**
   - SFINAE is about **compile-time function selection**
   - C has no equivalent mechanism
   - Must evaluate SFINAE conditions during transpilation
   - Generate only selected overloads in C output
   - Error-prone and difficult to debug

6. **Low ROI (Return on Investment)**
   - 120-180 hours of implementation
   - Used in <10% of C++ codebases (mostly libraries)
   - Most application code can avoid SFINAE
   - Can transpile 90%+ of C++ code without it

### Strategic Decision

**Defer indefinitely** until:
- Phase 11 (templates) is fully complete and stable
- Phase 14 (type traits) is implemented
- Real user demand emerges for SFINAE support
- Alternative approaches (concept stripping, manual refactoring) prove insufficient

## Conceptual Translation Approach

SFINAE enables **compile-time overload selection**. Translation requires evaluating SFINAE conditions during transpilation and generating only selected overloads.

### Example 1: std::enable_if for Function Overloading

**C++ Input**:
```cpp
#include <type_traits>

// Overload for integral types
template<typename T>
typename std::enable_if<std::is_integral<T>::value, T>::type
add(T a, T b) {
    return a + b;
}

// Overload for floating-point types
template<typename T>
typename std::enable_if<std::is_floating_point<T>::value, T>::type
add(T a, T b) {
    return a + b + 0.1;  // Different implementation
}

// Usage
int x = add(5, 3);        // Calls integral version
double y = add(1.5, 2.5); // Calls floating-point version
```

**Conceptual C Translation**:
```c
// Transpiler evaluates std::enable_if conditions
// Generates only the selected overload for each instantiation

// add<int> - is_integral<int> is true, first overload selected
int add__int(int a, int b) {
    return a + b;
}

// add<double> - is_floating_point<double> is true, second overload selected
double add__double(double a, double b) {
    return a + b + 0.1;
}

// Usage
int x = add__int(5, 3);
double y = add__double(1.5, 2.5);
```

**Key Point**: Transpiler must evaluate `std::is_integral<int>` → true, select first overload.

### Example 2: Expression SFINAE with decltype

**C++ Input**:
```cpp
#include <utility>

// Only enabled if T has .size() method
template<typename T>
auto get_size(T& container) -> decltype(container.size()) {
    return container.size();
}

// Fallback: return 1 if no .size() method
template<typename T>
size_t get_size(...) {
    return 1;
}

struct Vector { size_t size() { return 10; } };
struct Scalar { };

// Usage
Vector v;
Scalar s;
size_t v_size = get_size(v);  // Calls first overload (has .size())
size_t s_size = get_size(s);  // Calls second overload (no .size())
```

**Conceptual C Translation**:
```c
// Transpiler checks if Vector has .size() method
typedef struct {
    // ...
} Vector;
size_t Vector__size(Vector* this) { return 10; }

// get_size<Vector> - decltype(v.size()) is valid, first overload selected
size_t get_size__Vector(Vector* container) {
    return Vector__size(container);
}

// Transpiler checks if Scalar has .size() method
typedef struct {
    // ...
} Scalar;
// No .size() method

// get_size<Scalar> - decltype(s.size()) is invalid, second overload selected
size_t get_size__Scalar(Scalar* container) {
    return 1;
}

// Usage
Vector v;
Scalar s;
size_t v_size = get_size__Vector(&v);
size_t s_size = get_size__Scalar(&s);
```

**Key Point**: Transpiler must check if `Scalar` has `.size()` method, detect failure, select fallback.

### Example 3: std::void_t for Detection Idiom

**C++ Input**:
```cpp
#include <type_traits>

// Primary template
template<typename, typename = void>
struct has_size : std::false_type { };

// Specialization if T::size() is valid
template<typename T>
struct has_size<T, std::void_t<decltype(std::declval<T>().size())>>
    : std::true_type { };

// Use in enable_if
template<typename T>
std::enable_if_t<has_size<T>::value, size_t>
get_size(T& container) {
    return container.size();
}

template<typename T>
std::enable_if_t<!has_size<T>::value, size_t>
get_size(T& obj) {
    return 1;
}
```

**Conceptual C Translation**:
```c
// Transpiler evaluates has_size<Vector>:
//   - Check if Vector::size() exists → yes
//   - has_size<Vector>::value = true
//   - Select first overload

size_t get_size__Vector(Vector* container) {
    return Vector__size(container);
}

// Transpiler evaluates has_size<Scalar>:
//   - Check if Scalar::size() exists → no
//   - has_size<Scalar>::value = false
//   - Select second overload

size_t get_size__Scalar(Scalar* obj) {
    return 1;
}
```

### Example 4: SFINAE with Trailing Return Type

**C++ Input**:
```cpp
// Only enabled if T supports operator+
template<typename T>
auto add(T a, T b) -> decltype(a + b) {
    return a + b;
}

struct Point { int x, y; };
Point operator+(Point a, Point b) {
    return {a.x + b.x, a.y + b.y};
}

int sum = add(1, 2);         // OK: int supports +
Point p = add({1,2}, {3,4}); // OK: Point supports +
// add("hello", "world");    // ERROR: const char* doesn't support +
```

**Conceptual C Translation**:
```c
// add<int> - decltype(1 + 2) is valid (int)
int add__int(int a, int b) {
    return a + b;
}

// add<Point> - decltype(p1 + p2) is valid (Point)
Point add__Point(Point a, Point b) {
    return Point__operator_add(a, b);
}

// add<const char*> - decltype(s1 + s2) is invalid
// Overload not generated, compile error at transpilation time

int sum = add__int(1, 2);
Point p = add__Point((Point){1,2}, (Point){3,4});
```

## Technical Challenges

### 1. Substitution Failure Detection

**Challenge**: Determine when template substitution fails

**Substitution Failures**:
- Type doesn't exist: `typename T::value_type` when `T` has no `value_type`
- Expression is invalid: `a + b` when `+` not defined
- Constant expression fails: `T::value` when `T` has no `value` member
- Function call fails: `f(a)` when no matching `f` exists

**Required**:
- Attempt template parameter substitution
- Catch failures gracefully (not errors)
- Select alternative overload/specialization
- Report only if no overload is viable

### 2. Enable_if Evaluation

**Challenge**: Evaluate `std::enable_if` conditions

**Pattern**:
```cpp
template<typename T>
std::enable_if_t<condition, ReturnType>
function(T arg);
```

**Transpiler Must**:
1. Evaluate `condition` for each instantiation
2. If `true`: instantiate function, `enable_if_t<true, R>` → `R`
3. If `false`: substitution failure, try other overloads
4. Generate C code only for successful instantiations

**Example**:
```cpp
std::enable_if_t<std::is_integral<int>::value, int>
// Transpiler: is_integral<int> → true
// enable_if_t<true, int> → int
```

### 3. Expression SFINAE

**Challenge**: Check if arbitrary expressions are valid

**Pattern**:
```cpp
template<typename T>
auto f(T x) -> decltype(x.foo()) {
    return x.foo();
}
```

**Transpiler Must**:
1. Parse `decltype(x.foo())`
2. Check if `T` has method `foo()`
3. Check if `foo()` is callable
4. Determine return type
5. If any check fails → substitution failure

**Complexity**:
- Requires symbol table lookup
- Method signature matching
- Overload resolution
- Template parameter substitution

### 4. SFINAE in Class Template Partial Specialization

**Challenge**: Select class template specialization based on SFINAE

**Pattern**:
```cpp
// Primary template
template<typename T, typename = void>
struct is_iterable : std::false_type { };

// Specialization if T is iterable
template<typename T>
struct is_iterable<T, std::void_t<
    decltype(std::begin(std::declval<T>())),
    decltype(std::end(std::declval<T>()))
>> : std::true_type { };
```

**Transpiler Must**:
1. Evaluate specialization conditions
2. Select most specialized template
3. Generate appropriate C typedef/struct

### 5. Overload Resolution with SFINAE

**Challenge**: Choose best overload when multiple are viable

**C++ Overload Resolution Rules**:
1. Exact match preferred
2. Template specialization preferred over primary
3. More constrained template preferred
4. SFINAE eliminates non-viable candidates

**Transpiler Must**:
- Implement full overload resolution algorithm
- Consider SFINAE in viability
- Select best match
- Generate only selected overload

### 6. Interaction with Type Traits

**Challenge**: Most SFINAE uses type traits

**Common Type Traits**:
- `std::is_integral`, `std::is_floating_point`, `std::is_pointer`
- `std::is_same`, `std::is_base_of`, `std::is_convertible`
- `std::enable_if`, `std::conditional`, `std::void_t`

**Required**:
- Implement type trait evaluation (Phase 14)
- Integrate with SFINAE evaluation
- Handle compound type trait expressions

## Implementation Strategy (IF Pursued)

### Phase 62.1: Type Trait Evaluation (40-60 hrs)

**Objective**: Evaluate type traits at transpile time

**Tasks**:
1. Implement core type traits
2. Evaluate trait expressions
3. Substitute trait results
4. Handle compound traits

**Deliverables**:
- TypeTraitEvaluator class
- Support for 20+ standard type traits
- Test suite for trait evaluation

**Prerequisites**: Phase 14 (Type Traits)

### Phase 62.2: Substitution Failure Detection (40-60 hrs)

**Objective**: Detect when template substitution fails

**Tasks**:
1. Implement substitution attempt mechanism
2. Catch type/expression failures
3. Mark overloads as non-viable
4. Continue with other candidates

**Deliverables**:
- SubstitutionEngine class
- Failure detection logic
- Test suite for various failure modes

### Phase 62.3: Enable_if Support (20-30 hrs)

**Objective**: Handle `std::enable_if` patterns

**Tasks**:
1. Detect `enable_if` usage
2. Evaluate conditions
3. Substitute results
4. Remove non-viable overloads

**Deliverables**:
- EnableIfEvaluator class
- Condition evaluator
- Test suite for enable_if patterns

### Phase 62.4: Expression SFINAE (30-40 hrs)

**Objective**: Validate expressions in `decltype`

**Tasks**:
1. Parse `decltype` expressions
2. Check expression validity
3. Determine result type
4. Handle failures gracefully

**Deliverables**:
- ExpressionValidator class
- decltype evaluator
- Test suite for expression SFINAE

### Phase 62.5: Overload Resolution Integration (20-30 hrs)

**Objective**: Integrate SFINAE into overload resolution

**Tasks**:
1. Extend overload resolver with SFINAE
2. Eliminate non-viable candidates
3. Select best match
4. Generate selected overload only

**Deliverables**:
- Enhanced OverloadResolver
- SFINAE-aware candidate selection
- Test suite for complex overload sets

## Dependencies

### Hard Dependencies

1. **Phase 11: Template Infrastructure** (REQUIRED)
   - Template instantiation
   - Template specialization
   - Template parameter substitution
   - Cannot implement SFINAE without templates

2. **Phase 14: Type Traits** (REQUIRED)
   - `std::enable_if`, `std::conditional`, `std::void_t`
   - Type checking traits (`is_integral`, `is_same`, etc.)
   - Trait evaluation engine

### Soft Dependencies

1. **Phase 60: Concepts**
   - Concepts replace many SFINAE use cases
   - Similar constraint evaluation logic
   - May share implementation

2. **Phase 59: Variadic Templates**
   - SFINAE often used with parameter packs
   - Variadic `enable_if` patterns

## Success Criteria (IF Implemented)

### Functional Requirements

- [ ] **std::enable_if Support**
  - Evaluate enable_if conditions
  - Select viable overloads
  - Generate only selected instantiations

- [ ] **Expression SFINAE**
  - Validate `decltype` expressions
  - Check method/operator existence
  - Determine return types

- [ ] **std::void_t Detection Idiom**
  - Support detection idiom pattern
  - Evaluate expression validity
  - Select template specializations

- [ ] **Class Template SFINAE**
  - Partial specialization selection
  - SFINAE in template parameters
  - Specialization priority rules

- [ ] **Type Trait Integration**
  - Evaluate standard type traits
  - Support compound trait expressions
  - Handle all common SFINAE patterns

### Quality Requirements

- [ ] **Test Coverage**: 90%+ for SFINAE features
- [ ] **Error Messages**: Clear diagnostics when all overloads fail
- [ ] **Performance**: Substitution attempts <50ms per template
- [ ] **Documentation**: Complete SFINAE translation guide

### Validation Cases

1. **Basic enable_if**
   ```cpp
   template<typename T>
   std::enable_if_t<std::is_integral<T>::value, T>
   twice(T x) { return x * 2; }
   ```

2. **Expression SFINAE**
   ```cpp
   template<typename T>
   auto get_size(T& x) -> decltype(x.size()) {
       return x.size();
   }
   ```

3. **Detection Idiom**
   ```cpp
   template<typename T>
   using has_size_t = decltype(std::declval<T>().size());

   template<typename T>
   constexpr bool has_size_v = std::is_detected_v<has_size_t, T>;
   ```

4. **Overload Set**
   ```cpp
   template<typename T>
   std::enable_if_t<std::is_integral<T>::value>
   print(T x);

   template<typename T>
   std::enable_if_t<std::is_floating_point<T>::value>
   print(T x);
   ```

5. **Class Template Specialization**
   ```cpp
   template<typename T, typename = void>
   struct Wrapper { static constexpr bool value = false; };

   template<typename T>
   struct Wrapper<T, std::void_t<typename T::value_type>> {
       static constexpr bool value = true;
   };
   ```

## Risks and Mitigations

### Risk 1: Overwhelming Complexity

**Problem**: SFINAE is one of the most complex C++ features

**Mitigation**:
- Start with simple enable_if patterns only
- Gradually add complexity
- Document unsupported patterns clearly
- Provide workaround suggestions

### Risk 2: Incomplete Type Trait Coverage

**Problem**: Need many type traits for common SFINAE patterns

**Mitigation**:
- Prioritize most common type traits
- Implement incrementally
- Allow user-defined trait specifications
- Document supported traits

### Risk 3: Debugging Difficulty

**Problem**: SFINAE errors are notoriously hard to debug

**Mitigation**:
- Provide detailed substitution failure messages
- Show which conditions failed
- Suggest alternative approaches
- Log substitution attempts (verbose mode)

### Risk 4: Modern C++ Alternatives

**Problem**: C++17/C++20 make SFINAE less necessary

**Mitigation**:
- Encourage users to use `if constexpr` (C++17)
- Suggest concepts (C++20) where applicable
- Provide migration guide from SFINAE
- Focus on legacy code support

## Alternative Approaches

### Option 1: SFINAE Stripping

**Approach**: Remove SFINAE, generate all overloads, rely on C compiler

**Pros**: Simple implementation
**Cons**: Type errors delayed, code bloat, may not compile

### Option 2: Manual Refactoring Guide

**Approach**: Don't support SFINAE, provide manual refactoring guide

**Pros**: Zero implementation effort
**Cons**: User burden, may be infeasible for complex code

### Option 3: Limited SFINAE (enable_if only)

**Approach**: Support only `std::enable_if`, not expression SFINAE

**Pros**: Covers 80% of use cases, much simpler
**Cons**: Incomplete support, some patterns still unsupported

**Recommendation**: If SFINAE support is needed, start with Option 3.

## Recommendation

**DEFER INDEFINITELY**

**Rationale**:
1. **Extremely complex**: 120-180 hours, high risk
2. **Template dependency**: Requires Phase 11 completion
3. **Type trait dependency**: Requires Phase 14 completion
4. **Low usage**: <10% of C++ codebases use SFINAE heavily
5. **Modern alternatives**: C++17/C++20 provide better options
6. **Transpilation challenge**: SFINAE evaluation is error-prone

**When to Reconsider**:
- Phase 11 and Phase 14 are complete and stable
- Users report SFINAE as blocking issue
- Automated SFINAE → `if constexpr` refactoring proves insufficient
- Heavy template library transpilation becomes priority

**Interim Solution**:
- Provide SFINAE → `if constexpr` migration guide
- Offer manual refactoring service
- Support limited SFINAE (enable_if only) if critical

**Current Stance**: Focus on more impactful features first.

## Resources

### Research Materials

- "C++ Templates: The Complete Guide" (Vandevoorde, Josuttis, Gregor)
- SFINAE patterns and idioms
- Type trait implementation techniques
- Overload resolution algorithms

### Related Phases

- **Phase 11**: Template Infrastructure (prerequisite)
- **Phase 14**: Type Traits (prerequisite)
- **Phase 60**: Concepts (SFINAE alternative)
- **Phase 59**: Variadic Templates (often combined)

### Common SFINAE Patterns

1. **enable_if overloading**
2. **Expression validity checking**
3. **Detection idiom** (`std::void_t`)
4. **Tag dispatch** (alternative to SFINAE)
5. **Concept emulation** (pre-C++20)

### SFINAE Alternatives

- **C++17 `if constexpr`**: Compile-time branching
- **C++20 Concepts**: Named constraints
- **Tag dispatch**: Runtime selection
- **Overloading**: Simple cases

## Notes

- This is a **placeholder plan** for a deferred advanced feature
- SFINAE is primarily for **library developers**, not application developers
- Modern C++ (C++17+) provides better alternatives
- **VERY LOW PRIORITY** - defer until absolutely necessary
- Consider **not implementing** at all, provide migration guide instead

---

**Last Updated**: 2025-12-26
**Status**: DEFERRED (VERY LOW Priority)
**Next Review**: After Phase 11 and Phase 14 completion
