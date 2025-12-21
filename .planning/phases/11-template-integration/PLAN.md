# Phase 11 Plan: Template Integration (v2.4.0)

**Phase**: 11 of 17
**Roadmap**: `.planning/ROADMAP.md`
**Brief**: `.planning/BRIEF.md`
**Target Version**: v2.4.0
**Status**: PENDING
**Prerequisite**: None

## Phase Goal

Integrate template monomorphization infrastructure (TemplateMonomorphizer.cpp and TemplateExtractor.cpp) into CppToCVisitor to enable translation of C++ template classes and functions into monomorphized C code with proper instantiation tracking.

## Deliverables

### Source Code
- [ ] CppToCVisitor integration (visitor methods for template processing)
- [ ] TemplateInstantiationTracker helper class
- [ ] Template instantiation deduplication logic
- [ ] Template specialization handling
- [ ] Monomorphized code collection mechanism

### Tests
- [ ] `tests/TemplateIntegrationTest.cpp` (12+ tests)
  - Basic template class instantiation
  - Multiple template functions
  - Template specializations (full and partial)
  - Nested templates (e.g., `vector<pair<int, string>>`)
  - Template class method calling
  - Template function calls
  - Implicit vs. explicit instantiations
  - Dependent type resolution
  - Template friend functions
  - Instance deduplication (same template, same args)
  - Template specialization override
  - Complex template hierarchies

### CLI Integration
- [ ] Add `--template-monomorphization={off,on}` flag
- [ ] Add `--template-instantiation-limit=<N>` flag (prevent explosion)

### Documentation
- [ ] Update `docs/CHANGELOG.md` for v2.4.0
- [ ] Update `README.md`
- [ ] Update `website/src/pages/features.astro`
- [ ] Add template integration examples to docs

### Release
- [ ] Git-flow release v2.4.0

## Technical Design

### Architecture Overview

```
Input: C++ Code with Templates
           ↓
┌─────────────────────────────────────┐
│  CppToCVisitor::Visit*Template*()   │ ← NEW visitor methods
│  - VisitClassTemplateDecl()         │
│  - VisitFunctionTemplateDecl()      │
│  - VisitClassTemplateSpecialization │
└─────────────────────────────────────┘
           ↓
┌─────────────────────────────────────┐
│ TemplateExtractor                   │ ← EXISTING infrastructure
│ - Extract all instantiations        │
│ - Track unique instances            │
│ - Handle implicit/explicit          │
└─────────────────────────────────────┘
           ↓
┌─────────────────────────────────────┐
│ TemplateMonomorphizer               │ ← EXISTING infrastructure
│ - Generate C code for instances     │
│ - Perform type substitution         │
│ - Mangle names                      │
└─────────────────────────────────────┘
           ↓
┌─────────────────────────────────────┐
│ TemplateInstantiationTracker        │ ← NEW helper
│ - Track visited instantiations      │
│ - Prevent duplicate generation      │
│ - Link monomorphized code           │
└─────────────────────────────────────┘
           ↓
Output: C Code with Monomorphized Types
```

### Key Components

#### 1. CppToCVisitor Integration Points

**Location**: `src/CppToCVisitor.cpp`

**New Visitor Methods**:

```cpp
// Visit template class declarations
bool VisitClassTemplateDecl(clang::ClassTemplateDecl *D);

// Visit template function declarations
bool VisitFunctionTemplateDecl(clang::FunctionTemplateDecl *D);

// Visit explicit specializations
bool VisitClassTemplateSpecializationDecl(
    clang::ClassTemplateSpecializationDecl *D);
```

**Integration Flow**:

1. When visiting translation unit, call TemplateExtractor to find all instantiations
2. For each instantiation:
   - Check if already processed (deduplication)
   - Call TemplateMonomorphizer::monomorphize()
   - Store generated code in output buffer
   - Track instantiation for linking
3. Emit all monomorphized code after main translation unit code

#### 2. TemplateInstantiationTracker (NEW)

Purpose: Track which template instantiations have been processed, prevent duplicate generation.

**Header**: `include/TemplateInstantiationTracker.h`

```cpp
class TemplateInstantiationTracker {
public:
    // Add instantiation to tracking set
    bool addInstantiation(const std::string& instantiationKey);

    // Check if already tracked
    bool isTracked(const std::string& instantiationKey) const;

    // Get all tracked instantiations
    std::vector<std::string> getAllTracked() const;

private:
    std::set<std::string> trackedInstantiations;
};
```

#### 3. Template Argument Key Generation

Generate unique keys for template instantiations:

```cpp
// Example keys:
// "Stack<int>"
// "Stack<double>"
// "Vector<Pair<int,string>>"
// "Array<double,20>"

std::string generateTemplateKey(
    const std::string& templateName,
    const clang::TemplateArgumentList& args);
```

### Template → Monomorphized C Examples

#### Example 1: Simple Template Class

**Input: C++**
```cpp
template<typename T>
class Stack {
    T data;
public:
    Stack() : data(T()) {}
    void push(T value) { data = value; }
    T pop() { return data; }
};

int main() {
    Stack<int> intStack;
    intStack.push(42);

    Stack<double> doubleStack;
    doubleStack.push(3.14);
}
```

**Output: Monomorphized C**
```c
// Stack<int> instantiation
typedef struct Stack_int {
    int data;
} Stack_int;

Stack_int* Stack_int_ctor(void) {
    Stack_int* self = malloc(sizeof(Stack_int));
    self->data = 0;
    return self;
}

void Stack_int_push(Stack_int* self, int value) {
    self->data = value;
}

int Stack_int_pop(Stack_int* self) {
    return self->data;
}

// Stack<double> instantiation
typedef struct Stack_double {
    double data;
} Stack_double;

Stack_double* Stack_double_ctor(void) {
    Stack_double* self = malloc(sizeof(Stack_double));
    self->data = 0.0;
    return self;
}

void Stack_double_push(Stack_double* self, double value) {
    self->data = value;
}

double Stack_double_pop(Stack_double* self) {
    return self->data;
}

// main() uses monomorphized versions
int main() {
    Stack_int* intStack = Stack_int_ctor();
    Stack_int_push(intStack, 42);

    Stack_double* doubleStack = Stack_double_ctor();
    Stack_double_push(doubleStack, 3.14);
}
```

#### Example 2: Template Function with Multiple Instantiations

**Input: C++**
```cpp
template<typename T>
T max(T a, T b) {
    return a > b ? a : b;
}

int main() {
    int maxInt = max(10, 20);
    double maxDouble = max(3.14, 2.71);
    const char* maxStr = max("hello", "world");
}
```

**Output: Monomorphized C**
```c
// max<int>
int max_int(int a, int b) {
    return a > b ? a : b;
}

// max<double>
double max_double(double a, double b) {
    return a > b ? a : b;
}

// max<const char*>
const char* max_const_char_ptr(const char* a, const char* b) {
    return a > b ? a : b;  // Note: This compares pointers, not strings
}

int main() {
    int maxInt = max_int(10, 20);
    double maxDouble = max_double(3.14, 2.71);
    const char* maxStr = max_const_char_ptr("hello", "world");
}
```

#### Example 3: Template Specialization

**Input: C++**
```cpp
// Primary template
template<typename T>
class Container {
public:
    void process() { /* generic */ }
};

// Full specialization
template<>
class Container<bool> {
public:
    void process() { /* specialized for bool */ }
};

int main() {
    Container<int> intC;
    intC.process();

    Container<bool> boolC;
    boolC.process();  // Calls specialized version
}
```

**Output: Monomorphized C**
```c
// Container<int> - uses primary template
typedef struct Container_int {
    // fields...
} Container_int;

void Container_int_process(Container_int* self) {
    // generic implementation
}

// Container<bool> - uses specialization
typedef struct Container_bool {
    // specialized fields...
} Container_bool;

void Container_bool_process(Container_bool* self) {
    // specialized implementation
}

int main() {
    Container_int intC;
    Container_int_process(&intC);

    Container_bool boolC;
    Container_bool_process(&boolC);
}
```

#### Example 4: Nested Template

**Input: C++**
```cpp
template<typename T>
class Vector {
    T* data;
    int size;
};

template<typename K, typename V>
class Pair {
    K key;
    V value;
};

int main() {
    Vector<Pair<int, double>> pairs;  // Nested: Vector<Pair<int,double>>
}
```

**Output: Monomorphized C**
```c
// First generate Pair<int,double>
typedef struct Pair_int_double {
    int key;
    double value;
} Pair_int_double;

// Then generate Vector<Pair<int,double>> using monomorphized type
typedef struct Vector_Pair_int_double {
    Pair_int_double* data;
    int size;
} Vector_Pair_int_double;

int main() {
    Vector_Pair_int_double pairs;
}
```

### Integration Algorithm

**Algorithm**: Template instantiation detection and monomorphization

```
PROCESS_TRANSLATION_UNIT(tu):
  1. Create TemplateExtractor
  2. extractor.extractTemplateInstantiations(tu)
  3. classInstantiations = extractor.getClassInstantiations()
  4. functionInstantiations = extractor.getFunctionInstantiations()

  5. CREATE tracker = TemplateInstantiationTracker()

  6. FOR EACH classInst in classInstantiations:
       key = generateTemplateKey(classInst)
       IF NOT tracker.isTracked(key):
           code = TemplateMonomorphizer::monomorphizeClass(classInst)
           outputBuffer += code
           tracker.addInstantiation(key)

  7. FOR EACH funcInst in functionInstantiations:
       key = generateTemplateKey(funcInst)
       IF NOT tracker.isTracked(key):
           code = TemplateMonomorphizer::monomorphizeFunction(funcInst)
           outputBuffer += code
           tracker.addInstantiation(key)

  8. EMIT all generated code to output file
  9. CONTINUE with normal translation unit code
```

### Challenge Mitigation Strategies

#### Challenge 1: Finding All Instantiations (Explicit + Implicit)

**Strategy**:
- Explicit instantiations: `template class Stack<int>;` - Clang creates ClassTemplateSpecializationDecl
- Implicit instantiations: `Stack<int> x;` - Clang creates on demand during parsing
- RecursiveASTVisitor will visit both when full AST is traversed
- TemplateExtractor deduplicates using unique keys

**Implementation**:
```cpp
// In TemplateExtractor::VisitClassTemplateSpecializationDecl()
if (TSK == TSK_Undeclared && !D->hasDefinition()) {
    return true;  // Skip declarations without definitions
}
// Accept: explicit instantiations, implicit instantiations, specializations
classInstantiations.push_back(D);
```

#### Challenge 2: Handling Partial Specializations

**Strategy**:
- Partial specializations (e.g., `template<typename T> class Vector<T*>`) create separate ClassTemplateSpecializationDecl
- TemplateExtractor captures all specializations
- TemplateMonomorphizer handles each independently
- Selection order: explicit specialization > partial specialization > primary template

**Implementation**:
```cpp
// TemplateExtractor captures:
// 1. Primary template: Vector<T>
// 2. Partial specialization: Vector<T*>
// 3. Full specialization: Vector<int>
// 4. User instantiations: Vector<double>, Vector<int*>

// Each gets separate struct typedef and methods
typedef struct Vector_double { ... } Vector_double;
typedef struct Vector_int_ptr { ... } Vector_int_ptr;  // uses partial spec
typedef struct Vector_int { ... } Vector_int;          // uses full spec
```

#### Challenge 3: Template Friend Functions

**Strategy**:
- Friend function templates are function template instantiations
- TemplateExtractor finds them via VisitFunctionTemplateDecl
- TemplateMonomorphizer generates C code as regular functions
- Access control is lost in C (not an issue)

**Implementation**:
```cpp
template<typename T>
class Stack {
    template<typename U>
    friend void printStack(const Stack<U>& s);
};

template<typename T>
void printStack(const Stack<T>& s) {
    // ...
}

// Generates monomorphized versions:
void printStack_int(const Stack_int* s);
void printStack_double(const Stack_double* s);
```

#### Challenge 4: Dependent Names Resolution

**Strategy**:
- Dependent names (e.g., `typename T::iterator`) are resolved by Clang during instantiation
- TemplateMonomorphizer receives resolved QualType values
- No need for manual resolution in this phase

**Implementation**:
```cpp
// Clang resolves before TemplateMonomorphizer sees it
template<typename T>
void process(T value) {
    typename T::type result = value;  // Resolved by Clang
}

// TemplateMonomorphizer receives resolved types for each instantiation
```

### Instantiation Tracking

**Deduplication Key Format**:

```
TemplateName<TemplateArg1,TemplateArg2,...>

Examples:
- Stack<int>
- Stack<double>
- Vector<Pair<int,string>>
- Array<double,20>
- Pair<int,string>
```

**Tracking Implementation**:

```cpp
class TemplateInstantiationTracker {
    std::set<std::string> tracked;  // Unique instantiation keys

    bool addInstantiation(const std::string& key) {
        if (tracked.count(key)) {
            return false;  // Already tracked
        }
        tracked.insert(key);
        return true;  // New instantiation
    }
};

// Usage in CppToCVisitor
if (tracker.addInstantiation(key)) {
    // Generate code only for new instantiations
    std::string code = monomorphizer.monomorphizeClass(classInst);
    outputBuffer += code;
}
```

### Name Mangling

Leverage existing NameMangler.cpp for consistent naming:

```cpp
// Example outputs from NameMangler
"Stack__int"           // Stack<int>
"Stack__double"        // Stack<double>
"Vector__Pair__int__string"  // Vector<Pair<int,string>>
"max__int"             // max<int>
"max__double"          // max<double>
```

## Test Cases (12+)

### 1. SimpleClassTemplateInstantiation
- Input: `Stack<int>` and `Stack<double>` in same function
- Verify: Two separate struct typedefs generated
- Verify: Methods for each type distinct

### 2. TemplateFunction_MultipleInstantiations
- Input: `max(int, int)`, `max(double, double)`, `max(string, string)`
- Verify: Three function variants generated
- Verify: Each function signature correct

### 3. ExplicitInstantiation
- Input: `template class Stack<int>;` (explicit)
- Verify: Stack<int> struct generated
- Verify: Methods generated

### 4. ImplicitInstantiation
- Input: `Stack<int> x;` (implicit via usage)
- Verify: Stack<int> struct generated
- Verify: Implicit instantiation extracted correctly

### 5. NestedTemplateInstantiation
- Input: `Vector<Pair<int, double>>`
- Verify: Both Pair<int,double> and Vector<Pair<int,double>> generated
- Verify: Correct dependency order (Pair first)

### 6. TemplateSpecialization_Full
- Input: Primary template + full specialization `template<> class Stack<bool>`
- Verify: Specialization used instead of primary
- Verify: Struct typedef uses specialization implementation

### 7. TemplateSpecialization_Partial
- Input: Primary template + partial specialization `template<typename T> class Vector<T*>`
- Verify: Partial specialization matched for pointer types
- Verify: Correct struct generation for both primary and partial

### 8. TemplateFunctionCallingTemplateClass
- Input: `template<typename T> void test() { Stack<T> s; }`
- Verify: Function template instantiation with nested class template
- Verify: Correct code generation for both

### 9. DeduplicationSameTemplate_SameArgs
- Input: Two uses of `Stack<int>` in different functions
- Verify: Only one struct/method set generated
- Verify: Both usages reference same generated code

### 10. TemplateFriendFunction
- Input: Template class with friend template function
- Verify: Friend function instantiation extracted
- Verify: Access control lost (acceptable in C)

### 11. DependentTypeResolution
- Input: `template<typename T> class Container { T data; }`
- Verify: T resolved correctly for each instantiation
- Verify: Struct field types correct for Container<int>, Container<double>, etc.

### 12. ComplexTemplateHierarchy
- Input: Multiple inheritance with templates
- Verify: Monomorphized type hierarchy correct
- Verify: Method resolution order (MRO) preserved

## Dependencies

- **No new external dependencies**
- Infrastructure: TemplateMonomorphizer.cpp, TemplateExtractor.cpp (EXIST)
- Requires: NameMangler.cpp (existing)
- Requires: clang AST API (existing)

**Parallel Execution**: Can run with Phases 6, 7, 8, 9, 12, 13

## Verification Criteria

- [ ] 12+ tests passing (100%)
- [ ] Template classes instantiate correctly (struct typedefs generated)
- [ ] Template functions generate for each type used (function signatures distinct)
- [ ] Specializations override primary template (correct implementation chosen)
- [ ] All instantiations link correctly (no undefined references)
- [ ] Deduplication works (same template+args → single definition)
- [ ] Nested templates handled (dependency order correct)
- [ ] No performance regression (<10% slowdown)

## Implementation Checklist

### Phase Checkpoint 1: Core Integration
- [ ] Create `include/TemplateInstantiationTracker.h`
- [ ] Implement TemplateInstantiationTracker.cpp
- [ ] Add visitor methods to CppToCVisitor
- [ ] Integrate TemplateExtractor call in visitor
- [ ] Integrate TemplateMonomorphizer call in visitor
- [ ] Unit tests for tracker
- [ ] Integration tests: SimpleClassTemplateInstantiation
- [ ] Commit: "feat: integrate template monomorphizer into visitor"

### Phase Checkpoint 2: Template Variants
- [ ] Handle function templates properly
- [ ] Handle class templates properly
- [ ] Add deduplication logic
- [ ] Integration tests: ExplicitInstantiation, ImplicitInstantiation
- [ ] Integration tests: NestedTemplateInstantiation
- [ ] Commit: "feat: template variant handling and deduplication"

### Phase Checkpoint 3: Specializations & Complex Cases
- [ ] Handle full specializations
- [ ] Handle partial specializations
- [ ] Handle friend templates
- [ ] Handle dependent types
- [ ] Integration tests: All specialization + complex tests
- [ ] Commit: "feat: template specialization and complex cases"

### Phase Checkpoint 4: Testing & Polish
- [ ] All 12+ tests passing
- [ ] Run linters (clang-format, clang-tidy)
- [ ] Code review subtask
- [ ] Update CLI with new flags
- [ ] Update documentation
- [ ] Commit: "test: template integration comprehensive tests"
- [ ] Release: v2.4.0 via git-flow

## Risk Mitigation

### Risk: Template Instantiation Explosion
- **Mitigation**: Add `--template-instantiation-limit` flag
- **Default**: 1000 instantiations max (prevent infinite recursion)
- **Action**: Error if limit exceeded

### Risk: Circular Template Dependencies
- **Mitigation**: Track processing stack in TemplateInstantiationTracker
- **Action**: Detect cycles and error gracefully

### Risk: Performance Degradation
- **Target**: <10% slowdown vs. Phase 10
- **Mitigation**: Profile hot paths, optimize key generation
- **Measurement**: Benchmark with large template-heavy C++ programs

### Risk: Generated Code Bloat
- **Mitigation**: Deduplication prevents duplicate instantiations
- **Analysis**: Count monomorphized types, measure code size impact
- **Expected**: ~1-3x code size increase for template-heavy programs

## Success Metrics

**Functional**:
- ✅ Template classes monomorphize correctly
- ✅ Template functions monomorphize correctly
- ✅ Specializations recognized and used
- ✅ All instantiations extracted and processed
- ✅ Zero duplicate definitions

**Quality**:
- ✅ 12+ tests, 100% passing
- ✅ All linters passing
- ✅ Code review approved
- ✅ No performance regression (>10%)

**Documentation**:
- ✅ CHANGELOG.md updated
- ✅ README.md feature list updated
- ✅ website/features.astro updated
- ✅ Examples added to docs

**Release**:
- ✅ v2.4.0 released via git-flow
- ✅ Tag created: `v2.4.0`
- ✅ Release notes published
