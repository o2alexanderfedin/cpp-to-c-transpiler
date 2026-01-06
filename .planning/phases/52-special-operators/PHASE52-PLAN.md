# Phase 52: Special Operator Overloading Implementation

**Phase**: 52 - Special Operators (v2.12.0)
**Type**: Feature Implementation (Map-Reduce Parallelization)
**Estimated Effort**: 105-165 hours
**Priority**: MEDIUM (complex semantics, critical for advanced patterns)
**Current Support**: 20% (subscript/call operators partially done)

---

## Objective

Implement comprehensive support for C++ special operator overloading, including assignment, member access, subscript, call, stream, and conversion operators. This phase covers the **most complex** operators with special semantics that are critical for RAII, smart pointers, containers, and I/O.

**Why This Matters**: Special operators enable fundamental C++ patterns:
- **Smart pointers**: `operator->`, `operator*`, `operator bool()`
- **Containers**: `operator[]` (instance version, not static from Phase 2)
- **Functors**: `operator()` (instance version)
- **Stream I/O**: `operator<<`, `operator>>` for custom types
- **Assignment semantics**: Copy assignment, move assignment
- **Type conversions**: `operator T()`, `explicit operator bool()`

Without special operators, ~25% of real-world C++ patterns cannot be transpiled (smart pointers, iterators, custom containers, I/O-enabled types).

---

## Current State Analysis

### What Works (20% Complete)
- **Static subscript/call**: `static operator[]` and `static operator()` (StaticOperatorTranslator from Phase 2)
- **Multidimensional subscript**: `operator[](i, j, k)` (MultidimSubscriptTranslator from Phase 1)
- **Name mangling**: Infrastructure exists for all operators
- **Test framework**: 12 subscript/call tests + 12 special operator tests exist

### What's Missing (80% Gap)
- **Instance subscript**: Non-static `operator[]` (single argument, most common case)
- **Instance call operator**: Non-static `operator()` for functors
- **Smart pointer operators**: `operator->`, `operator*` (dereference)
- **Stream operators**: `operator<<`, `operator>>` (distinct from bitwise shift)
- **Conversion operators**: `operator T()`, `explicit operator bool()`
- **Assignment operators**: Copy assignment (`operator=`), move assignment
- **Address-of operator**: `operator&` (rarely overloaded, but exists)

### Current Blockers
1. **CppToCVisitor.cpp:95-101**: TODO for copy assignment storage (CRITICAL)
2. **CppToCVisitor.cpp:84-93**: TODO for move assignment storage (CRITICAL)
3. **Stream vs shift disambiguation**: `operator<<` has two meanings (bitwise shift vs stream output)
4. **Conversion operator detection**: Different AST node (`CXXConversionDecl` vs `CXXMethodDecl`)
5. **Smart pointer chaining**: `ptr->method()` must handle both `operator->` and method call

---

## Translation Patterns

### Instance Subscript Operator ([])

**C++ Code**:
```cpp
class Array {
    int* data;
    size_t size;
public:
    int& operator[](size_t index) {
        return data[index];  // Non-const version (read-write)
    }

    const int& operator[](size_t index) const {
        return data[index];  // Const version (read-only)
    }
};

Array arr(10);
arr[5] = 42;           // Uses non-const operator[]
int x = arr[5];        // Can use either version
const Array& carr = arr;
int y = carr[5];       // Uses const operator[]
```

**Transpiled C Code**:
```c
typedef struct Array {
    int* data;
    size_t size;
} Array;

// Non-const version (returns pointer for modification)
int* Array_operator_subscript_size_t(Array* this, size_t index);

// Const version (returns pointer to const)
const int* Array_operator_subscript_size_t_const(const Array* this, size_t index);

// Implementation
int* Array_operator_subscript_size_t(Array* this, size_t index) {
    return &this->data[index];  // Return pointer to element
}

const int* Array_operator_subscript_size_t_const(const Array* this, size_t index) {
    return &this->data[index];
}

// Call sites
Array arr = Array_constructor(10);
*Array_operator_subscript_size_t(&arr, 5) = 42;  // Dereference to assign
int x = *Array_operator_subscript_size_t(&arr, 5);
const Array* carr = &arr;
int y = *Array_operator_subscript_size_t_const(carr, 5);
```

**Key Insights**:
- Returns **reference** (pointer in C) to allow modification: `arr[i] = value`
- Const and non-const versions must both exist
- Dereference required at call site when used as lvalue

---

### Instance Call Operator (Functors)

**C++ Code**:
```cpp
class Adder {
    int base;
public:
    Adder(int b) : base(b) {}

    int operator()(int x) const {
        return base + x;
    }

    int operator()(int x, int y) const {  // Overloaded with different arity
        return base + x + y;
    }
};

Adder add10(10);
int result1 = add10(5);      // 15
int result2 = add10(5, 3);   // 18
```

**Transpiled C Code**:
```c
typedef struct Adder {
    int base;
} Adder;

// One-argument version
int Adder_operator_call_int_const(const Adder* this, int x);

// Two-argument version (overloaded by arity)
int Adder_operator_call_int_int_const(const Adder* this, int x, int y);

// Implementations
int Adder_operator_call_int_const(const Adder* this, int x) {
    return this->base + x;
}

int Adder_operator_call_int_int_const(const Adder* this, int x, int y) {
    return this->base + x + y;
}

// Call sites
Adder add10 = Adder_constructor(10);
int result1 = Adder_operator_call_int_const(&add10, 5);
int result2 = Adder_operator_call_int_int_const(&add10, 5, 3);
```

**Key Insights**:
- Enables functor pattern (objects that behave like functions)
- Can be overloaded with different arities (0, 1, 2+ arguments)
- Common in standard algorithms (e.g., `std::transform`, `std::for_each`)

---

### Smart Pointer Operators (-> and *)

**C++ Code**:
```cpp
class SmartPointer {
    int* ptr;
public:
    SmartPointer(int* p) : ptr(p) {}

    int* operator->() const {
        return ptr;  // Returns raw pointer
    }

    int& operator*() const {
        return *ptr;  // Dereference
    }

    explicit operator bool() const {  // Conversion operator (see below)
        return ptr != nullptr;
    }
};

struct Data {
    int value;
    void method();
};

SmartPointer sp(new Data{42});
sp->value = 100;     // Calls operator-> then accesses member
(*sp).value = 200;   // Calls operator* then accesses member
sp->method();        // Chained: operator-> then method call

if (sp) {            // Calls operator bool()
    // ...
}
```

**Transpiled C Code**:
```c
typedef struct SmartPointer {
    int* ptr;
} SmartPointer;

typedef struct Data {
    int value;
} Data;
void Data_method(Data* this);

// Arrow operator (returns raw pointer)
int* SmartPointer_operator_arrow_const(const SmartPointer* this);

// Dereference operator (returns reference/pointer)
int* SmartPointer_operator_star_const(const SmartPointer* this);

// Bool conversion (see Conversion Operators section)
bool SmartPointer_operator_bool_const(const SmartPointer* this);

// Implementations
int* SmartPointer_operator_arrow_const(const SmartPointer* this) {
    return this->ptr;
}

int* SmartPointer_operator_star_const(const SmartPointer* this) {
    return this->ptr;  // Return pointer (C's "reference")
}

bool SmartPointer_operator_bool_const(const SmartPointer* this) {
    return this->ptr != NULL;
}

// Call sites
SmartPointer sp = SmartPointer_constructor(malloc(sizeof(Data)));
SmartPointer_operator_arrow_const(&sp)->value = 100;  // Chained access
(*SmartPointer_operator_star_const(&sp)).value = 200;
Data_method(SmartPointer_operator_arrow_const(&sp));  // Chained method call

if (SmartPointer_operator_bool_const(&sp)) {
    // ...
}
```

**Key Insights**:
- `operator->` returns raw pointer for chained member access
- `operator*` returns reference (pointer in C) for dereference
- Critical for smart pointer patterns (RAII, resource management)

---

### Stream Operators (<< >>)

**C++ Code**:
```cpp
class Point {
    int x, y;
    friend std::ostream& operator<<(std::ostream& os, const Point& p) {
        os << "(" << p.x << ", " << p.y << ")";
        return os;
    }

    friend std::istream& operator>>(std::istream& is, Point& p) {
        char discard;
        is >> discard >> p.x >> discard >> p.y >> discard;  // Read "(x, y)"
        return is;
    }
};

Point p{1, 2};
std::cout << p << std::endl;  // Output: (1, 2)

Point q;
std::cin >> q;  // Input: (3, 4)
```

**Transpiled C Code**:
```c
#include <stdio.h>

typedef struct Point {
    int x, y;
} Point;

// Stream output (FILE* instead of std::ostream)
void Point_operator_output(FILE* os, const Point* p);

// Stream input (FILE* instead of std::istream)
void Point_operator_input(FILE* is, Point* p);

// Implementations
void Point_operator_output(FILE* os, const Point* p) {
    fprintf(os, "(%d, %d)", p->x, p->y);
}

void Point_operator_input(FILE* is, Point* p) {
    char discard;
    fscanf(is, "%c%d%c%d%c", &discard, &p->x, &discard, &p->y, &discard);
}

// Call sites
Point p = {1, 2};
Point_operator_output(stdout, &p);
fputs("\n", stdout);

Point q;
Point_operator_input(stdin, &q);
```

**Key Insights**:
- Stream operators are **friend functions** (non-member)
- Must distinguish from bitwise shift operators (`<<` for shifting bits)
- First parameter is stream (`std::ostream&` or `std::istream&`)
- Transpile to C using `FILE*` and `fprintf`/`fscanf`
- Return type is stream reference (for chaining), but C version can be `void`

**Disambiguation**:
- **Stream operator**: First parameter is `std::ostream&` or `std::istream&`
- **Bitwise shift operator**: First parameter is class type (e.g., `BigInt&`)

---

### Conversion Operators (operator T())

**C++ Code**:
```cpp
class Celsius {
    double value;
public:
    Celsius(double v) : value(v) {}

    // Implicit conversion to double
    operator double() const {
        return value;
    }

    // Explicit conversion to int
    explicit operator int() const {
        return static_cast<int>(value);
    }

    // Explicit conversion to bool (truthiness)
    explicit operator bool() const {
        return value != 0.0;
    }
};

Celsius temp(36.5);
double d = temp;           // Implicit conversion (calls operator double())
int i = static_cast<int>(temp);  // Explicit conversion (calls operator int())
if (temp) {                // Explicit conversion (calls operator bool())
    // ...
}
```

**Transpiled C Code**:
```c
#include <stdbool.h>

typedef struct Celsius {
    double value;
} Celsius;

// Implicit conversion (can call directly)
double Celsius_operator_to_double_const(const Celsius* this);

// Explicit conversion (requires explicit call)
int Celsius_operator_to_int_const(const Celsius* this);

// Explicit bool conversion
bool Celsius_operator_to_bool_const(const Celsius* this);

// Implementations
double Celsius_operator_to_double_const(const Celsius* this) {
    return this->value;
}

int Celsius_operator_to_int_const(const Celsius* this) {
    return (int)this->value;
}

bool Celsius_operator_to_bool_const(const Celsius* this) {
    return this->value != 0.0;
}

// Call sites
Celsius temp = Celsius_constructor(36.5);
double d = Celsius_operator_to_double_const(&temp);  // Implicit in C++, explicit in C
int i = Celsius_operator_to_int_const(&temp);  // Explicit cast
if (Celsius_operator_to_bool_const(&temp)) {
    // ...
}
```

**Key Insights**:
- **Implicit conversion**: `operator T()` without `explicit`
- **Explicit conversion**: `explicit operator T()` requires cast
- **Common pattern**: `explicit operator bool()` for truthiness checks
- **AST node**: `CXXConversionDecl` (not `CXXMethodDecl`)

**Special Case - operator bool()**:
- Used in conditionals: `if (obj)`, `while (obj)`, `!obj`
- Must work with `VisitIfStmt`, `VisitWhileStmt`, etc.
- Transpile conditional to: `if (ClassName_operator_to_bool(&obj))`

---

### Assignment Operators (= copy and move)

**C++ Code**:
```cpp
class String {
    char* data;
    size_t length;
public:
    // Copy assignment (deep copy)
    String& operator=(const String& other) {
        if (this != &other) {  // Self-assignment check
            delete[] data;
            length = other.length;
            data = new char[length + 1];
            strcpy(data, other.data);
        }
        return *this;
    }

    // Move assignment (transfer ownership)
    String& operator=(String&& other) noexcept {
        if (this != &other) {
            delete[] data;
            data = other.data;
            length = other.length;
            other.data = nullptr;  // Other is now empty
            other.length = 0;
        }
        return *this;
    }
};

String s1("hello"), s2("world");
s1 = s2;        // Copy assignment
s1 = String("temp");  // Move assignment (rvalue)
```

**Transpiled C Code**:
```c
typedef struct String {
    char* data;
    size_t length;
} String;

// Copy assignment (returns pointer to this)
String* String_operator_assign_const_String_ref(String* this, const String* other);

// Move assignment (rvalue reference → pointer in C, no ownership semantics)
String* String_operator_assign_String_rvalue_ref(String* this, String* other);

// Implementations
String* String_operator_assign_const_String_ref(String* this, const String* other) {
    if (this != other) {  // Self-assignment check
        free(this->data);
        this->length = other->length;
        this->data = malloc(this->length + 1);
        strcpy(this->data, other->data);
    }
    return this;
}

String* String_operator_assign_String_rvalue_ref(String* this, String* other) {
    if (this != other) {
        free(this->data);
        this->data = other->data;
        this->length = other->length;
        other->data = NULL;  // Transfer ownership
        other->length = 0;
    }
    return this;
}

// Call sites
String s1 = String_constructor("hello");
String s2 = String_constructor("world");
String_operator_assign_const_String_ref(&s1, &s2);  // Copy

String temp = String_constructor("temp");
String_operator_assign_String_rvalue_ref(&s1, &temp);  // Move (temp is temporary)
```

**Key Insights**:
- **Copy assignment**: Deep copy, parameter is `const T&`
- **Move assignment**: Transfer ownership, parameter is `T&&` (rvalue reference)
- **Return `*this`**: Returns pointer in C for chaining: `a = b = c`
- **Self-assignment check**: CRITICAL to avoid crashes
- **TODO completion**: This task completes CppToCVisitor.cpp:84-93 and :95-101

---

## Map-Reduce Task Breakdown

### Map Phase: 12 Parallel Operator Tasks (6-16 hours each)

This is the **most complex** phase due to special semantics of each operator.

#### Task 1: Instance Subscript Operator ([]) [8-12 hours]

**Deliverables**:
- `SpecialOperatorTranslator::translateInstanceSubscript()` method
- Handle single-argument `operator[]` (not multidimensional from Phase 1)
- Const and non-const versions
- Reference return handling (pointer in C)
- Unit tests:
  - Non-const `operator[]` for modification (6 tests)
  - Const `operator[]` for read-only access (4 tests)
  - Reference return usage: `arr[i] = value`
  - Const correctness
  - Out-of-bounds behavior (if applicable)

**Verification**:
- ✅ `arr[5] = 42` → `*Array_operator_subscript(&arr, 5) = 42`
- ✅ Const version used for const objects
- ✅ Dereference happens at call site for lvalue usage

**Estimated Effort**: 8-12 hours

---

#### Task 2: Instance Call Operator (()) [10-14 hours]

**Deliverables**:
- `SpecialOperatorTranslator::translateInstanceCall()` method
- Handle variable arity: 0, 1, 2+ arguments
- Overload disambiguation (same operator, different parameter counts)
- Functor pattern support
- Unit tests:
  - `operator()` with 0 arguments (4 tests)
  - `operator()` with 1 argument (4 tests)
  - `operator()` with 2+ arguments (4 tests)
  - Overloaded by arity (3 tests)
  - Const correctness (3 tests)

**Verification**:
- ✅ `functor(a, b)` → `ClassName_operator_call_TypeA_TypeB(&functor, a, b)`
- ✅ Different arities generate different function names

**Estimated Effort**: 10-14 hours (arity disambiguation complexity)

---

#### Task 3: Arrow Operator (->) [10-14 hours]

**Deliverables**:
- `SpecialOperatorTranslator::translateArrow()` method
- Smart pointer pattern support
- Chaining: `ptr->member` and `ptr->method()`
- Integration with member access AST nodes
- Unit tests:
  - Basic `operator->` (4 tests)
  - Chained member access: `ptr->value` (4 tests)
  - Chained method call: `ptr->method()` (4 tests)
  - Const correctness (2 tests)
  - Null pointer check (2 tests)

**Verification**:
- ✅ `ptr->value` → `SmartPointer_operator_arrow(&ptr)->value`
- ✅ `ptr->method()` → `Class_method(SmartPointer_operator_arrow(&ptr))`

**Special Challenge**: Must integrate with `VisitMemberExpr` and `VisitCXXMemberCallExpr`

**Estimated Effort**: 10-14 hours (AST integration complexity)

---

#### Task 4: Dereference Operator (*) [8-12 hours]

**Deliverables**:
- `SpecialOperatorTranslator::translateDereference()` method
- Smart pointer dereference support
- Reference return handling
- Unit tests:
  - Basic `operator*` (4 tests)
  - Dereference then access: `(*ptr).value` (4 tests)
  - Const correctness (2 tests)
  - Lvalue usage: `*ptr = value` (3 tests)

**Verification**:
- ✅ `*ptr` → `*SmartPointer_operator_star(&ptr)` (double dereference in C)
- ✅ `(*ptr).value` → `SmartPointer_operator_star(&ptr)->value`

**Estimated Effort**: 8-12 hours

---

#### Task 5: Stream Output Operator (<<) [12-16 hours]

**Deliverables**:
- `SpecialOperatorTranslator::translateStreamOutput()` method
- Distinguish from bitwise left shift (different first parameter type)
- Convert `std::ostream&` to `FILE*`
- Friend operator support (non-member)
- Unit tests:
  - Friend `operator<<` (6 tests)
  - Member `operator<<` (2 tests, rare)
  - Chaining: `cout << a << b` (4 tests)
  - Custom formatting (2 tests)
  - Disambiguation from bitwise shift (2 tests)

**Verification**:
- ✅ `cout << obj` → `ClassName_operator_output(stdout, &obj)`
- ✅ Stream operator distinct from bitwise shift
- ✅ Chaining works: `cout << a << b` → `ClassName_operator_output(stdout, &a); ClassName_operator_output(stdout, &b);`

**Disambiguation Logic**:
```cpp
bool isStreamOperator(CXXOperatorCallExpr* E) {
    // Check first parameter type
    QualType FirstParamType = E->getArg(0)->getType();
    if (FirstParamType->isReferenceType()) {
        QualType Pointee = FirstParamType->getPointeeType();
        if (Pointee.getAsString().find("ostream") != std::string::npos) {
            return true;  // Stream output operator
        }
    }
    return false;  // Bitwise shift operator
}
```

**Estimated Effort**: 12-16 hours (disambiguation + FILE* conversion complexity)

---

#### Task 6: Stream Input Operator (>>) [12-16 hours]

**Deliverables**:
- `SpecialOperatorTranslator::translateStreamInput()` method
- Similar to Task 5 but for `std::istream&`
- Convert to `FILE*` with `fscanf`
- Distinguish from bitwise right shift
- Unit tests:
  - Friend `operator>>` (6 tests)
  - Member `operator>>` (2 tests, rare)
  - Input parsing (4 tests)
  - Error handling (2 tests)
  - Disambiguation from bitwise shift (2 tests)

**Verification**:
- ✅ `cin >> obj` → `ClassName_operator_input(stdin, &obj)`
- ✅ Input parsing correct

**Estimated Effort**: 12-16 hours

---

#### Task 7: Conversion to bool (explicit operator bool()) [8-12 hours]

**Deliverables**:
- `SpecialOperatorTranslator::translateBoolConversion()` method
- `explicit operator bool()` detection (via `CXXConversionDecl`)
- Integration with conditionals: `if (obj)`, `while (obj)`, `!obj`
- Unit tests:
  - Basic `operator bool()` (4 tests)
  - In `if` statement (3 tests)
  - In `while` loop (2 tests)
  - With `operator!`: `!obj` (3 tests)
  - Explicit cast: `static_cast<bool>(obj)` (2 tests)

**Verification**:
- ✅ `if (obj)` → `if (ClassName_operator_to_bool(&obj))`
- ✅ `!obj` → `!ClassName_operator_to_bool(&obj)`

**Special Integration**: Must integrate with `VisitIfStmt`, `VisitWhileStmt`, etc.

**Estimated Effort**: 8-12 hours

---

#### Task 8: Generic Conversion Operators (operator T()) [10-14 hours]

**Deliverables**:
- `SpecialOperatorTranslator::translateConversion()` method
- Handle all conversion types: `operator int()`, `operator double()`, `operator CustomType()`
- Implicit vs explicit conversions
- AST node: `CXXConversionDecl` (not `CXXMethodDecl`)
- Unit tests:
  - Implicit conversion: `operator double()` (4 tests)
  - Explicit conversion: `explicit operator int()` (4 tests)
  - Custom type conversion (3 tests)
  - Const correctness (2 tests)
  - Multiple conversions in same class (3 tests)

**Verification**:
- ✅ `double d = obj` → `double d = ClassName_operator_to_double(&obj)`
- ✅ `explicit` keyword enforced at call sites

**Estimated Effort**: 10-14 hours (CXXConversionDecl complexity)

---

#### Task 9: Copy Assignment Operator (operator=) [12-16 hours]

**Deliverables**:
- `SpecialOperatorTranslator::translateCopyAssignment()` method
- Deep copy semantics
- Self-assignment check injection (critical)
- Return reference (pointer in C) for chaining
- **Complete TODO at CppToCVisitor.cpp:95-101**
- Unit tests:
  - Basic copy assignment (4 tests)
  - Self-assignment: `a = a` (3 tests)
  - Chaining: `a = b = c` (3 tests)
  - Deep copy verification (4 tests)
  - Resource cleanup (2 tests)

**Verification**:
- ✅ `a = b` → `ClassName_operator_assign(&a, &b)`
- ✅ Self-assignment safe: `a = a` doesn't crash
- ✅ Chaining works: `a = b = c`

**Critical TODO Completion**: This task resolves a known blocker.

**Estimated Effort**: 12-16 hours (self-assignment + TODO resolution)

---

#### Task 10: Move Assignment Operator (operator=(T&&)) [12-16 hours]

**Deliverables**:
- `SpecialOperatorTranslator::translateMoveAssignment()` method
- Transfer ownership semantics
- Rvalue reference handling (`T&&` → pointer in C)
- Self-assignment check
- **Complete TODO at CppToCVisitor.cpp:84-93**
- Unit tests:
  - Basic move assignment (4 tests)
  - Resource transfer (4 tests)
  - Source object empty after move (3 tests)
  - Self-move safety: `a = std::move(a)` (2 tests)
  - Chaining (2 tests)

**Verification**:
- ✅ `a = std::move(b)` → `ClassName_operator_assign_move(&a, &b)` (b becomes empty)
- ✅ Ownership transferred, not copied

**Critical TODO Completion**: This task resolves a known blocker.

**Estimated Effort**: 12-16 hours (rvalue reference + TODO resolution)

---

#### Task 11: Address-of Operator (operator&) [6-10 hours]

**Deliverables**:
- `SpecialOperatorTranslator::translateAddressOf()` method
- RARE operator (usually not overloaded)
- Returns pointer type
- Unit tests:
  - Basic `operator&` (4 tests)
  - Custom pointer-like behavior (3 tests)
  - Const correctness (2 tests)

**Verification**:
- ✅ `&obj` → `ClassName_operator_addressof(&obj)` (confusing but correct)

**Note**: This operator is rarely overloaded in practice. Support mainly for completeness.

**Estimated Effort**: 6-10 hours (rare, simpler)

---

#### Task 12: Comma Operator (operator,) [6-10 hours]

**Deliverables**:
- `SpecialOperatorTranslator::translateComma()` method
- VERY RARE operator (almost never overloaded)
- Sequencing semantics: evaluate left, then right, return right
- Unit tests:
  - Basic `operator,` (3 tests)
  - Sequencing verification (3 tests)
  - Return value (2 tests)

**Verification**:
- ✅ `(a, b)` → `ClassName_operator_comma(&a, &b)` (returns b)

**Note**: Extremely rare. Support for completeness.

**Estimated Effort**: 6-10 hours (rare, simpler)

---

### Map Phase Summary

**Total Parallel Tasks**: 12
**Total Estimated Effort**: 114-172 hours (map phase)
**Parallelization**: All 12 tasks can run simultaneously
**Wall-Clock Time (12 cores)**: 12-16 hours (2 days)

---

### Reduce Phase: Integration & Validation (16-25 hours)

#### Reduce Task 1: SpecialOperatorTranslator Integration (4-6 hours)

**Deliverables**:
- Create `include/SpecialOperatorTranslator.h`
- Create `src/SpecialOperatorTranslator.cpp`
- Integrate with CppToCVisitor
- Complete TODOs at CppToCVisitor.cpp:84-93, :95-101

**Verification**:
- ✅ All 12 operators route through SpecialOperatorTranslator
- ✅ TODOs resolved (copy/move assignment storage)

---

#### Reduce Task 2: Smart Pointer Integration Tests (4-6 hours)

**Deliverables**:
- Create `tests/integration/special-operators/SmartPointerTest.cpp`
- Integration tests for smart pointer patterns:
  - `operator->` + member access
  - `operator*` + dereference
  - `operator bool()` in conditionals
  - RAII pattern validation
- At least 10 integration tests

**Example**:
```cpp
// C++ code
std::unique_ptr<Data> ptr = std::make_unique<Data>(42);
ptr->method();
if (ptr) {
    int value = ptr->value;
}

// Transpiled C code
SmartPointer ptr = SmartPointer_constructor(malloc(sizeof(Data)));
Data_method(SmartPointer_operator_arrow(&ptr));
if (SmartPointer_operator_bool(&ptr)) {
    int value = SmartPointer_operator_arrow(&ptr)->value;
}
```

---

#### Reduce Task 3: Container & Functor Integration Tests (3-5 hours)

**Deliverables**:
- Tests for `operator[]` in custom container
- Tests for `operator()` in functors
- At least 8 integration tests

---

#### Reduce Task 4: Stream I/O Integration Tests (3-5 hours)

**Deliverables**:
- Tests for `operator<<` with custom types
- Tests for `operator>>` with parsing
- Round-trip tests (write then read)
- At least 6 integration tests

---

#### Reduce Task 5: Assignment Operator Integration Tests (2-3 hours)

**Deliverables**:
- Tests for copy assignment chains: `a = b = c`
- Tests for move assignment with resource transfer
- Self-assignment safety tests
- At least 6 integration tests

---

### Reduce Phase Summary

**Total Effort**: 16-25 hours
**Wall-Clock Time**: 2-3 days (sequential)

---

## Total Phase 52 Effort

| Phase | Effort (hours) | Parallelization | Wall-Clock (12 cores) |
|-------|----------------|-----------------|----------------------|
| Map Phase (12 tasks) | 114-172 | ✅ Full | 12-16 hours (2 days) |
| Reduce Phase (5 tasks) | 16-25 | ❌ Sequential | 16-25 hours (2-3 days) |
| **TOTAL** | **130-197** | **Mixed** | **28-41 hours (4-5 days)** |

**Aggressive parallelization**: 4-5 days wall-clock time with 12 parallel agents
**Sequential execution**: 130-197 hours = 16-25 days (3-5 weeks)

---

## Implementation Architecture

### Class Hierarchy

```cpp
// include/SpecialOperatorTranslator.h
class SpecialOperatorTranslator {
public:
    explicit SpecialOperatorTranslator(CNodeBuilder& Builder);

    // Entry points
    FunctionDecl* transformMethod(CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU);
    FunctionDecl* transformConversion(CXXConversionDecl* CD, ASTContext& Ctx, TranslationUnitDecl* C_TU);
    CallExpr* transformCall(CXXOperatorCallExpr* E, ASTContext& Ctx);

private:
    CNodeBuilder& m_builder;

    // Subscript and call operators
    FunctionDecl* translateInstanceSubscript(CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU);
    FunctionDecl* translateInstanceCall(CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU);

    // Smart pointer operators
    FunctionDecl* translateArrow(CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU);
    FunctionDecl* translateDereference(CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU);

    // Stream operators
    FunctionDecl* translateStreamOutput(CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU);
    FunctionDecl* translateStreamInput(CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU);

    // Conversion operators
    FunctionDecl* translateBoolConversion(CXXConversionDecl* CD, ASTContext& Ctx, TranslationUnitDecl* C_TU);
    FunctionDecl* translateConversion(CXXConversionDecl* CD, ASTContext& Ctx, TranslationUnitDecl* C_TU);

    // Assignment operators
    FunctionDecl* translateCopyAssignment(CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU);
    FunctionDecl* translateMoveAssignment(CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU);

    // Rare operators
    FunctionDecl* translateAddressOf(CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU);
    FunctionDecl* translateComma(CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU);

    // Call transformations
    CallExpr* transformSubscriptCall(CXXOperatorCallExpr* E, ASTContext& Ctx);
    CallExpr* transformCallOperatorCall(CXXOperatorCallExpr* E, ASTContext& Ctx);
    CallExpr* transformArrowCall(CXXOperatorCallExpr* E, ASTContext& Ctx);
    CallExpr* transformDereferenceCall(CXXOperatorCallExpr* E, ASTContext& Ctx);
    CallExpr* transformStreamCall(CXXOperatorCallExpr* E, ASTContext& Ctx);
    CallExpr* transformAssignmentCall(CXXOperatorCallExpr* E, ASTContext& Ctx);

    // Utilities
    std::string generateOperatorName(const CXXMethodDecl* MD);
    std::string generateConversionName(const CXXConversionDecl* CD);
    bool isStreamOperator(CXXOperatorCallExpr* E) const;
    bool isBitwiseShiftOperator(CXXOperatorCallExpr* E) const;
    FunctionDecl* findOrCreateFunction(const CXXMethodDecl* MD, ASTContext& Ctx, TranslationUnitDecl* C_TU);
};
```

---

## Test Strategy

### Unit Tests (120-160 tests total)

**Per-Operator Tests**:
- Instance subscript: 10-14 tests
- Instance call: 18-22 tests
- Arrow operator: 16-20 tests
- Dereference operator: 13-17 tests
- Stream output: 16-20 tests
- Stream input: 16-20 tests
- Bool conversion: 14-18 tests
- Generic conversion: 16-20 tests
- Copy assignment: 16-20 tests
- Move assignment: 15-19 tests
- Address-of: 9-13 tests
- Comma: 8-12 tests

**Test File Structure**:
```
tests/unit/special-operators/
├── CMakeLists.txt
├── InstanceSubscriptOperatorTest.cpp
├── InstanceCallOperatorTest.cpp
├── ArrowOperatorTest.cpp
├── DereferenceOperatorTest.cpp
├── StreamOutputOperatorTest.cpp
├── StreamInputOperatorTest.cpp
├── BoolConversionOperatorTest.cpp
├── ConversionOperatorTest.cpp
├── CopyAssignmentOperatorTest.cpp
├── MoveAssignmentOperatorTest.cpp
├── AddressOfOperatorTest.cpp
└── CommaOperatorTest.cpp
```

**Total Unit Tests**: 167-225 tests

### Integration Tests (30-40 tests)

**Test Categories**:
1. **Smart Pointers** (10-12 tests): Full smart pointer pattern
2. **Containers** (6-8 tests): Custom container with `operator[]`
3. **Functors** (6-8 tests): Functor pattern with `operator()`
4. **Stream I/O** (6-8 tests): Round-trip I/O tests
5. **Assignment Chains** (2-4 tests): `a = b = c` with copy/move

**Test File Structure**:
```
tests/integration/special-operators/
├── CMakeLists.txt
├── SmartPointerTest.cpp
├── ContainerTest.cpp
├── FunctorTest.cpp
├── StreamIOTest.cpp
└── AssignmentChainTest.cpp
```

### Real-World Validation (5-8 projects)

**Example Projects**:
1. **Smart Pointer Library**: unique_ptr-like class
2. **Custom Container**: Dynamic array with `operator[]`
3. **Functor Library**: Callable objects for algorithms
4. **I/O Serialization**: Custom types with stream operators
5. **RAII Resource Manager**: Copy/move assignment with resource management
6. **Iterator Implementation**: `operator*`, `operator->`, `operator++`
7. **Expression Template Library**: Complex operator chaining
8. **Custom String Class**: All special operators combined

**Success Criteria**:
- ✅ At least 6/8 projects work correctly
- ✅ Smart pointer patterns function correctly
- ✅ I/O round-trips preserve data

---

## Success Criteria

### Functional Requirements
- ✅ All 12 special operators translate correctly
- ✅ Smart pointer patterns work (`operator->`, `operator*`, `operator bool`)
- ✅ Container patterns work (`operator[]`, `operator()`)
- ✅ Stream I/O works (`operator<<`, `operator>>`)
- ✅ Assignment semantics correct (copy deep copies, move transfers ownership)
- ✅ Conversion operators work (implicit and explicit)
- ✅ Self-assignment safe for copy/move assignment
- ✅ Operator chaining preserved

### Quality Requirements
- ✅ 100% unit test pass rate (167-225 tests)
- ✅ 90%+ integration test pass rate (30-40 tests)
- ✅ 75%+ real-world validation (6/8 projects)
- ✅ No memory leaks (valgrind clean)
- ✅ Performance within 10% of C++

### Critical TODO Completion
- ✅ CppToCVisitor.cpp:84-93 TODO resolved (move assignment storage)
- ✅ CppToCVisitor.cpp:95-101 TODO resolved (copy assignment storage)

### Code Quality
- ✅ SOLID principles
- ✅ DRY across all operators
- ✅ Consistent with Phases 50-51
- ✅ Comprehensive documentation

---

## Dependencies

### Required (Blocking)
- None

### Optional (Enhancements)
- **Phase 50**: Arithmetic operators (can run in parallel)
- **Phase 51**: Comparison operators (can run in parallel)

**Parallel Execution**: ✅ **Phase 52 can run in parallel with Phases 50-51**

---

## Deliverables

### Code Artifacts
1. ✅ `include/SpecialOperatorTranslator.h` (700-1000 lines)
2. ✅ `src/SpecialOperatorTranslator.cpp` (2500-3500 lines)
3. ✅ Integration with `src/CppToCVisitor.cpp` (100-150 lines)
4. ✅ Complete TODOs (40-60 lines)

### Test Artifacts
1. ✅ Unit tests: `tests/unit/special-operators/*.cpp` (167-225 tests)
2. ✅ Integration tests: `tests/integration/special-operators/*.cpp` (30-40 tests)
3. ✅ Real-world validation: 5-8 projects

### Documentation
1. ✅ `docs/SPECIAL_OPERATORS.md`
2. ✅ `docs/SMART_POINTERS.md` (patterns guide)
3. ✅ Updated `docs/OPERATOR_OVERLOADING_REFERENCE.md`
4. ✅ Updated `README.md`
5. ✅ Updated `FEATURE-MATRIX.md` (20% → 100% special operator support)

### Phase Summary
1. ✅ `.planning/phases/52-special-operators/PHASE52-SUMMARY.md`

---

## Execution Plan

### Recommended Approach (Parallel Map-Reduce)

**Day 1-2**: Map Phase (12 parallel agents)
```bash
Task 1: Instance subscript operator
Task 2: Instance call operator
Task 3: Arrow operator
Task 4: Dereference operator
Task 5: Stream output operator
Task 6: Stream input operator
Task 7: Bool conversion operator
Task 8: Generic conversion operators
Task 9: Copy assignment operator
Task 10: Move assignment operator
Task 11: Address-of operator
Task 12: Comma operator
```

**Day 3-5**: Reduce Phase (sequential)
```bash
Reduce Task 1: Integration
Reduce Task 2: Smart pointer tests
Reduce Task 3: Container & functor tests
Reduce Task 4: Stream I/O tests
Reduce Task 5: Assignment tests
```

**Day 5**: Git Flow Release
```bash
git flow release start v2.12.0
git commit -m "feat(phase52): Implement special operator overloading (12 operators, TODO resolution)"
git flow release finish v2.12.0
```

---

## Quality Gates

Before declaring Phase 52 complete:
- [ ] All 12 map tasks complete
- [ ] SpecialOperatorTranslator integrated
- [ ] TODOs at CppToCVisitor.cpp:84-93, :95-101 resolved
- [ ] 100% unit test pass rate (167-225 tests)
- [ ] 90%+ integration test pass rate (30-40 tests)
- [ ] 75%+ real-world validation (6/8 projects)
- [ ] Smart pointer patterns validated
- [ ] Stream I/O round-trips work
- [ ] Assignment operators safe (self-assignment, resource management)
- [ ] Zero memory leaks
- [ ] Performance within 10%
- [ ] All linters passing
- [ ] No regressions
- [ ] Documentation complete
- [ ] PHASE52-SUMMARY.md created

---

## Next Steps

After Phase 52 completion:
- **Phase 53**: Operator Overloading Integration & Testing (after Phases 50-52 complete)
- **Phase 54**: Real-World Operator Validation

---

**Ready to execute**: Use parallel map-reduce approach (4-5 days vs 3-5 weeks sequential)

This is the **most complex** operator phase but also the **most rewarding** - enables smart pointers, containers, functors, and I/O patterns critical for real C++ code.
