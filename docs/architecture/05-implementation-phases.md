# Implementation Phases: Progressive C++ to C Transpiler Development

## Overview

This document defines 12 implementation phases for building the C++ to C transpiler, ordered by complexity from simplest (direct C mapping) to most complex (templates and virtual methods). Each phase is independently testable and builds upon previous phases.

**Implementation Philosophy:**
- Start with features that map directly to C (no transformation)
- Progressively add transformations (simple → complex)
- Each phase is fully tested before moving to next
- TDD mandatory: write tests before implementation
- 100% handler coverage required

---

## Phase 1: Basic Functions & Arithmetic

### Phase Goal
Establish the foundational transpilation pipeline by implementing standalone functions with simple arithmetic operations and local variables. This phase validates the end-to-end architecture: C++ AST → C AST → C code.

### Complexity Level
**1** (Simplest) - Direct 1:1 mapping to C

### C++ Features
- Standalone function declarations and definitions
- Function parameters (simple types: int, float, double, char)
- Local variable declarations with initialization
- Arithmetic operators: `+`, `-`, `*`, `/`, `%`
- Integer and floating-point literals
- Variable references (DeclRefExpr)
- Return statements
- Function calls (no overloading)

### C Mapping Strategy
**Direct 1:1 mapping** - These C++ constructs have identical syntax in C:
```
C++: int add(int a, int b) { return a + b; }
C:   int add(int a, int b) { return a + b; }
```

No transformations needed. This phase establishes the pipeline without translation complexity.

### Required Handlers
1. **FunctionHandler** (new) - Translate function declarations/definitions
2. **VariableHandler** (new) - Translate local variable declarations
3. **ExpressionHandler** (new, basic) - Translate arithmetic expressions, literals, variable references
4. **StatementHandler** (new, basic) - Translate return statements, compound statements

### New Handler Code
**FunctionHandler:**
- `handleFunctionDecl()` - Create C FunctionDecl from C++ FunctionDecl
- `translateParameters()` - Convert parameter list
- `translateReturnType()` - Convert return type (simple types only)

**VariableHandler:**
- `handleVarDecl()` - Translate local variable declarations
- `handleInitExpr()` - Translate initialization expressions

**ExpressionHandler:**
- `handleBinaryOperator()` - Translate `+`, `-`, `*`, `/`, `%`
- `handleIntegerLiteral()` - Pass through integer literals
- `handleFloatingLiteral()` - Pass through float/double literals
- `handleDeclRefExpr()` - Translate variable references

**StatementHandler:**
- `handleReturnStmt()` - Translate return statements
- `handleCompoundStmt()` - Translate `{ }` blocks
- `handleDeclStmt()` - Translate variable declaration statements

### AST Nodes
From Phase 36 catalog:
- `FunctionDecl` - Function declarations
- `ParmVarDecl` - Function parameters
- `CompoundStmt` - `{ }` blocks
- `VarDecl` - Variable declarations
- `DeclStmt` - Declaration statements
- `BinaryOperator` - Arithmetic operations
- `IntegerLiteral` - Integer constants
- `FloatingLiteral` - Float/double constants
- `DeclRefExpr` - Variable references
- `ImplicitCastExpr` - Automatic type casts (transparent)
- `ReturnStmt` - Return statements

### Dependencies
**None** - This is the foundation phase.

All handlers are built from scratch in this phase.

### Test Strategy

**Unit Tests (50+ tests):**
- FunctionHandler: empty function, with parameters, with return type, with body
- VariableHandler: uninitialized, initialized, multiple types
- ExpressionHandler: each operator separately, literal types, variable refs
- StatementHandler: return with/without value, compound statements

**Handler Integration Tests (20-30 tests):**
- Function with local variables
- Function with arithmetic expressions
- Function calling another function
- Multiple functions in same file

**E2E Integration Tests (5-10 tests):**
- Complete programs that compile and run
- Verify generated C code produces same output as C++ code

**Coverage Target:** 100% line coverage for all Phase 1 handlers

### Verification Criteria
- [ ] All unit tests pass (50+)
- [ ] All integration tests pass (20-30)
- [ ] All E2E tests compile with `gcc -std=c99`
- [ ] Generated C code produces correct output
- [ ] No memory leaks in generated code (valgrind)
- [ ] 100% code coverage for FunctionHandler, VariableHandler, ExpressionHandler (basic), StatementHandler (basic)
- [ ] At least 5 complete programs transpile, compile, and run correctly

### Example Translations

**Example 1: Simple Function**
```cpp
// C++ Input
int add(int a, int b) {
    return a + b;
}

// C Output
int add(int a, int b) {
    return a + b;
}
```

**Example 2: Function with Local Variables**
```cpp
// C++ Input
int calculate(int x) {
    int result = x * 2;
    int final = result + 10;
    return final;
}

// C Output
int calculate(int x) {
    int result = x * 2;
    int final = result + 10;
    return final;
}
```

**Example 3: Arithmetic Expressions**
```cpp
// C++ Input
double average(double a, double b) {
    return (a + b) / 2.0;
}

// C Output
double average(double a, double b) {
    return (a + b) / 2.0;
}
```

**Example 4: Function Calls**
```cpp
// C++ Input
int add(int a, int b) { return a + b; }
int sum_three(int x, int y, int z) {
    return add(add(x, y), z);
}

// C Output
int add(int a, int b) { return a + b; }
int sum_three(int x, int y, int z) {
    return add(add(x, y), z);
}
```

**Example 5: Multiple Variable Declarations**
```cpp
// C++ Input
int compute() {
    int a = 10;
    int b = 20;
    int c = a + b;
    int d = c * 2;
    return d;
}

// C Output
int compute(void) {
    int a = 10;
    int b = 20;
    int c = a + b;
    int d = c * 2;
    return d;
}
```

### Estimated Effort
**Handler Implementation:**
- FunctionHandler: 200-300 LOC, 3-4 hours
- VariableHandler (local vars): 150-200 LOC, 2-3 hours
- ExpressionHandler (basic): 300-400 LOC, 4-5 hours
- StatementHandler (basic): 50-100 LOC, 1-2 hours

**Testing:**
- Unit tests: 800-1000 LOC, 6-8 hours
- Integration tests: 300-400 LOC, 3-4 hours
- E2E tests: 200-300 LOC, 2-3 hours

**Total:** 2000-2700 LOC, 21-29 hours (~3-4 days)

---

## Phase 2: Control Flow

### Phase Goal
Add support for all basic control flow constructs: conditionals, loops, and switch statements. These features enable complex program logic while maintaining 1:1 C mapping.

### Complexity Level
**1** (Simple) - Direct 1:1 mapping to C

### C++ Features
- If/else statements
- While loops
- For loops (including range-based for on arrays - optional)
- Switch/case statements
- Break and continue statements
- Comparison operators: `==`, `!=`, `<`, `>`, `<=`, `>=`
- Logical operators: `&&`, `||`, `!`
- Unary operators: `++`, `--`, `-` (negation), `+` (unary plus)

### C Mapping Strategy
**Direct mapping** - Control flow syntax is identical in C and C++:
```cpp
// C++ Input
if (x > 0) {
    y = x;
} else {
    y = -x;
}

// C Output (identical)
if (x > 0) {
    y = x;
} else {
    y = -x;
}
```

### Required Handlers
- **StatementHandler** (extend) - Add control flow statement translation
- **ExpressionHandler** (extend) - Add comparison and logical operators

### New Handler Code
**StatementHandler additions:**
- `handleIfStmt()` - Translate if/else
- `handleWhileStmt()` - Translate while loops
- `handleForStmt()` - Translate for loops
- `handleSwitchStmt()` - Translate switch statements
- `handleCaseStmt()` - Translate case labels
- `handleDefaultStmt()` - Translate default label
- `handleBreakStmt()` - Translate break
- `handleContinueStmt()` - Translate continue

**ExpressionHandler additions:**
- `handleBinaryOperator()` - Extend for comparison operators (`==`, `!=`, `<`, etc.)
- `handleBinaryOperator()` - Extend for logical operators (`&&`, `||`)
- `handleUnaryOperator()` - Add for `!`, `++`, `--`, `-`, `+`

### AST Nodes
- `IfStmt` - If/else statements
- `WhileStmt` - While loops
- `ForStmt` - For loops
- `SwitchStmt` - Switch statements
- `CaseStmt` - Case labels
- `DefaultStmt` - Default label
- `BreakStmt` - Break statements
- `ContinueStmt` - Continue statements
- `BinaryOperator` - Comparison and logical operators
- `UnaryOperator` - Unary operators

### Dependencies
**Phase 1** - Requires function, variable, and expression infrastructure

### Test Strategy
**Unit Tests (40+ tests):**
- Each control flow construct separately
- Nested if/else
- Multiple loop types
- Switch with multiple cases
- Break/continue behavior

**Integration Tests (15-20 tests):**
- Control flow within functions
- Multiple nested loops
- Switch with fallthrough

**E2E Tests (5-10 tests):**
- Programs with complex control flow
- Fibonacci, factorial, sorting algorithms

### Verification Criteria
- [ ] All unit tests pass
- [ ] All integration tests pass
- [ ] Generated C code compiles
- [ ] Control flow behavior matches C++
- [ ] 100% coverage for control flow handlers

### Example Translations

**Example 1: If/Else**
```cpp
// C++ Input
int abs(int x) {
    if (x < 0) {
        return -x;
    } else {
        return x;
    }
}

// C Output
int abs(int x) {
    if (x < 0) {
        return -x;
    } else {
        return x;
    }
}
```

**Example 2: While Loop**
```cpp
// C++ Input
int factorial(int n) {
    int result = 1;
    while (n > 1) {
        result *= n;
        n--;
    }
    return result;
}

// C Output
int factorial(int n) {
    int result = 1;
    while (n > 1) {
        result *= n;
        n--;
    }
    return result;
}
```

**Example 3: For Loop**
```cpp
// C++ Input
int sum_array(int arr[], int size) {
    int sum = 0;
    for (int i = 0; i < size; i++) {
        sum += arr[i];
    }
    return sum;
}

// C Output
int sum_array(int arr[], int size) {
    int sum = 0;
    for (int i = 0; i < size; i++) {
        sum += arr[i];
    }
    return sum;
}
```

**Example 4: Switch Statement**
```cpp
// C++ Input
const char* day_name(int day) {
    switch (day) {
        case 0: return "Sunday";
        case 1: return "Monday";
        case 2: return "Tuesday";
        default: return "Unknown";
    }
}

// C Output
const char* day_name(int day) {
    switch (day) {
        case 0: return "Sunday";
        case 1: return "Monday";
        case 2: return "Tuesday";
        default: return "Unknown";
    }
}
```

**Example 5: Nested Loops with Break**
```cpp
// C++ Input
int find_in_matrix(int matrix[][10], int rows, int target) {
    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < 10; j++) {
            if (matrix[i][j] == target) {
                return 1;
            }
        }
    }
    return 0;
}

// C Output
int find_in_matrix(int matrix[][10], int rows, int target) {
    for (int i = 0; i < rows; i++) {
        for (int j = 0; j < 10; j++) {
            if (matrix[i][j] == target) {
                return 1;
            }
        }
    }
    return 0;
}
```

### Estimated Effort
**Handler Extensions:**
- StatementHandler: +200-300 LOC, 3-4 hours
- ExpressionHandler: +100-150 LOC, 2-3 hours

**Testing:**
- Unit tests: 600-800 LOC, 5-6 hours
- Integration tests: 250-350 LOC, 2-3 hours
- E2E tests: 200-300 LOC, 2-3 hours

**Total:** 1350-1900 LOC, 14-19 hours (~2-3 days)

---

## Phase 3: Global Variables & Types

### Phase Goal
Add support for global variables, static local variables, string literals, and type casting. This completes basic C functionality.

### Complexity Level
**1** (Simple) - Mostly direct mapping with storage class handling

### C++ Features
- Global variable declarations and definitions
- Static local variables
- String literals (`const char*`)
- Character literals
- Type casts (C-style and implicit)
- Const qualifiers on variables
- Array types (basic)

### C Mapping Strategy
**Direct mapping with storage class:**
```cpp
// C++ Input
int globalCounter = 0;
static const char* message = "Hello";

// C Output
int globalCounter = 0;
static const char* message = "Hello";
```

**Arrays map directly:**
```cpp
// C++ Input
int values[10] = {1, 2, 3};

// C Output
int values[10] = {1, 2, 3};
```

### Required Handlers
- **VariableHandler** (extend) - Add global and static variable support
- **ExpressionHandler** (extend) - Add string/char literals, casts

### New Handler Code
**VariableHandler additions:**
- `handleVarDecl()` - Extend for global scope
- `handleStaticLocal()` - Handle static local variables
- `handleArrayDecl()` - Handle array declarations
- `handleInitListExpr()` - Handle array initialization

**ExpressionHandler additions:**
- `handleStringLiteral()` - Translate string literals
- `handleCharacterLiteral()` - Translate char literals
- `handleCStyleCastExpr()` - Translate C-style casts
- `handleImplicitCastExpr()` - Handle implicit casts (usually transparent)
- `handleArraySubscriptExpr()` - Translate `arr[i]`

### AST Nodes
- `VarDecl` (global scope) - Global variables
- `StringLiteral` - String constants
- `CharacterLiteral` - Character constants
- `ImplicitCastExpr` - Implicit type casts
- `CStyleCastExpr` - Explicit C-style casts
- `ArraySubscriptExpr` - Array indexing
- `InitListExpr` - Array/struct initialization

### Dependencies
**Phase 1** - Requires variable and expression infrastructure

### Test Strategy
**Unit Tests (30+ tests):**
- Global variable declarations
- Static local variables
- String literals of various lengths
- Character literals
- Type casts
- Array declarations and access

**Integration Tests (10-15 tests):**
- Global variables used across functions
- Static local persistence across calls
- String manipulation

**E2E Tests (5-10 tests):**
- Programs using global state
- String processing

### Verification Criteria
- [ ] All unit tests pass
- [ ] Global variables have correct linkage
- [ ] Static locals persist across calls
- [ ] String literals work correctly
- [ ] Arrays work correctly
- [ ] 100% coverage for global variable handling

### Example Translations

**Example 1: Global Variables**
```cpp
// C++ Input
int globalCounter = 0;

void increment() {
    globalCounter++;
}

int getCounter() {
    return globalCounter;
}

// C Output
int globalCounter = 0;

void increment(void) {
    globalCounter++;
}

int getCounter(void) {
    return globalCounter;
}
```

**Example 2: Static Local Variable**
```cpp
// C++ Input
int get_next_id() {
    static int id = 0;
    return ++id;
}

// C Output
int get_next_id(void) {
    static int id = 0;
    return ++id;
}
```

**Example 3: String Literals**
```cpp
// C++ Input
const char* get_greeting() {
    return "Hello, World!";
}

// C Output
const char* get_greeting(void) {
    return "Hello, World!";
}
```

**Example 4: Array Declaration and Access**
```cpp
// C++ Input
int fibonacci[10] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34};

int get_fib(int n) {
    return fibonacci[n];
}

// C Output
int fibonacci[10] = {0, 1, 1, 2, 3, 5, 8, 13, 21, 34};

int get_fib(int n) {
    return fibonacci[n];
}
```

**Example 5: Type Casting**
```cpp
// C++ Input
double to_double(int x) {
    return (double)x / 2.0;
}

// C Output
double to_double(int x) {
    return (double)x / 2.0;
}
```

### Estimated Effort
**Handler Extensions:**
- VariableHandler: +150-200 LOC, 2-3 hours
- ExpressionHandler: +100-150 LOC, 2-3 hours

**Testing:**
- Unit tests: 400-500 LOC, 3-4 hours
- Integration tests: 150-200 LOC, 2-3 hours
- E2E tests: 150-200 LOC, 1-2 hours

**Total:** 950-1250 LOC, 10-15 hours (~1-2 days)

---

## Phase 4: Structs (C-style)

### Phase Goal
Add support for C-style structs without methods. This establishes the foundation for class translation in later phases.

### Complexity Level
**2** (Intermediate) - Direct mapping but requires type system integration

### C++ Features
- Struct declarations (C-style, no methods)
- Field declarations
- Field access (`struct.field`)
- Struct initialization (brace-init)
- Passing structs to functions (by value and by pointer)
- Nested structs (struct as field type)

### C Mapping Strategy
**Direct mapping** - C++ structs without methods are identical to C structs:
```cpp
// C++ Input
struct Point {
    int x;
    int y;
};

// C Output
struct Point {
    int x;
    int y;
};
```

### Required Handlers
- **RecordHandler** (new) - Translate struct declarations
- **ExpressionHandler** (extend) - Add field access (MemberExpr)

### New Handler Code
**RecordHandler:**
- `handleRecordDecl()` - Translate C-style struct declarations
- `translateFields()` - Translate field declarations
- `handleNestedRecords()` - Handle nested struct definitions

**ExpressionHandler additions:**
- `handleMemberExpr()` - Translate field access (`.` and `->`)
- `handleInitListExpr()` - Extend for struct initialization

### AST Nodes
- `RecordDecl` - Struct declarations
- `FieldDecl` - Struct fields
- `MemberExpr` - Field access
- `InitListExpr` - Struct initialization

### Dependencies
**Phase 1, 3** - Requires variable and type infrastructure

### Test Strategy
**Unit Tests (25+ tests):**
- Simple struct declaration
- Struct with multiple fields
- Nested structs
- Field access
- Struct initialization

**Integration Tests (10-15 tests):**
- Functions taking/returning structs
- Struct arrays
- Nested struct access

**E2E Tests (5-10 tests):**
- Programs using struct-based data structures

### Verification Criteria
- [ ] All unit tests pass
- [ ] Struct layout matches C++ layout
- [ ] Field access works correctly
- [ ] Initialization works correctly
- [ ] 100% coverage for RecordHandler

### Example Translations

**Example 1: Simple Struct**
```cpp
// C++ Input
struct Point {
    int x;
    int y;
};

Point create_point(int x, int y) {
    Point p = {x, y};
    return p;
}

// C Output
struct Point {
    int x;
    int y;
};

struct Point create_point(int x, int y) {
    struct Point p = {x, y};
    return p;
}
```

**Example 2: Nested Struct**
```cpp
// C++ Input
struct Rectangle {
    struct Point {
        int x;
        int y;
    } topLeft;
    struct Point bottomRight;
};

// C Output
struct Point {
    int x;
    int y;
};

struct Rectangle {
    struct Point topLeft;
    struct Point bottomRight;
};
```

**Example 3: Struct with Initialization**
```cpp
// C++ Input
struct Color {
    unsigned char r;
    unsigned char g;
    unsigned char b;
    unsigned char a;
};

Color red() {
    return {255, 0, 0, 255};
}

// C Output
struct Color {
    unsigned char r;
    unsigned char g;
    unsigned char b;
    unsigned char a;
};

struct Color red(void) {
    struct Color __temp = {255, 0, 0, 255};
    return __temp;
}
```

**Example 4: Function with Struct Parameters**
```cpp
// C++ Input
struct Point {
    int x;
    int y;
};

int distance_squared(Point a, Point b) {
    int dx = b.x - a.x;
    int dy = b.y - a.y;
    return dx * dx + dy * dy;
}

// C Output
struct Point {
    int x;
    int y;
};

int distance_squared(struct Point a, struct Point b) {
    int dx = b.x - a.x;
    int dy = b.y - a.y;
    return dx * dx + dy * dy;
}
```

**Example 5: Struct Pointer Access**
```cpp
// C++ Input
struct Node {
    int value;
    Node* next;
};

void set_value(Node* node, int val) {
    node->value = val;
}

// C Output
struct Node {
    int value;
    struct Node* next;
};

void set_value(struct Node* node, int val) {
    node->value = val;
}
```

### Estimated Effort
**Handler Implementation:**
- RecordHandler: 200-300 LOC, 3-4 hours
- ExpressionHandler extensions: 100-150 LOC, 2-3 hours

**Testing:**
- Unit tests: 350-450 LOC, 3-4 hours
- Integration tests: 200-250 LOC, 2-3 hours
- E2E tests: 150-200 LOC, 1-2 hours

**Total:** 1000-1350 LOC, 11-16 hours (~1.5-2 days)

---

## Phase 5: Pointers & References

### Phase Goal
Add full pointer support and translate C++ references to C pointers. This enables low-level memory manipulation.

### Complexity Level
**2** (Intermediate) - References require transformation, pointers are direct

### C++ Features
- Pointer types (`int*`, `void*`, etc.)
- Address-of operator (`&variable`)
- Dereference operator (`*ptr`)
- Pointer arithmetic (`ptr + 1`, `ptr++`, etc.)
- C++ references (`int&`) - translate to pointers
- Const references (`const int&`)
- Null pointer (`nullptr` → `NULL`)

### C Mapping Strategy
**Pointers:** Direct mapping (same syntax)
```cpp
int* ptr = &x;
*ptr = 10;
```

**References → Pointers:**
```cpp
// C++ Input
void swap(int& a, int& b) {
    int temp = a;
    a = b;
    b = temp;
}

// C Output
void swap(int* a, int* b) {
    int temp = *a;
    *a = *b;
    *b = temp;
}
```

**nullptr → NULL:**
```cpp
// C++ Input
int* ptr = nullptr;

// C Output
int* ptr = NULL;
```

### Required Handlers
- **FunctionHandler** (extend) - Handle reference parameters
- **ExpressionHandler** (extend) - Add pointer operations, dereference references
- **TypeTranslator** (new) - Translate reference types to pointer types

### New Handler Code
**FunctionHandler additions:**
- `translateReferenceParam()` - Convert reference parameters to pointers
- Update call sites to pass addresses

**ExpressionHandler additions:**
- `handleUnaryOperator()` - Extend for `&` (address-of), `*` (dereference)
- `handleBinaryOperator()` - Extend for pointer arithmetic
- `handleCXXNullPtrLiteralExpr()` - Translate `nullptr` to `NULL`
- Auto-dereference for references (insert `*` where needed)

**TypeTranslator:**
- `translateType()` - Convert `T&` to `T*`
- `translateType()` - Convert `const T&` to `const T*`

### AST Nodes
- `PointerType` - Pointer types
- `ReferenceType` - Reference types (translate to pointers)
- `UnaryOperator` (`UO_AddrOf`, `UO_Deref`) - Address-of and dereference
- `BinaryOperator` (pointer arithmetic) - Pointer addition/subtraction
- `CXXNullPtrLiteralExpr` - nullptr literal

### Dependencies
**Phase 1, 3, 4** - Requires function, variable, and type infrastructure

### Test Strategy
**Unit Tests (30+ tests):**
- Pointer declarations
- Address-of operator
- Dereference operator
- Pointer arithmetic
- Reference parameter translation
- nullptr translation

**Integration Tests (15-20 tests):**
- Functions with reference parameters
- Pointer-based algorithms
- Mixed pointer/reference usage

**E2E Tests (5-10 tests):**
- Linked list implementation
- Swap functions
- Array manipulation via pointers

### Verification Criteria
- [ ] All unit tests pass
- [ ] References correctly translated to pointers
- [ ] Reference usage sites auto-dereference
- [ ] Pointer arithmetic works
- [ ] 100% coverage for pointer/reference handling

### Example Translations

**Example 1: Reference Parameters**
```cpp
// C++ Input
void swap(int& a, int& b) {
    int temp = a;
    a = b;
    b = temp;
}

void test() {
    int x = 10, y = 20;
    swap(x, y);
}

// C Output
void swap(int* a, int* b) {
    int temp = *a;
    *a = *b;
    *b = temp;
}

void test(void) {
    int x = 10, y = 20;
    swap(&x, &y);
}
```

**Example 2: Const References**
```cpp
// C++ Input
int sum(const int& a, const int& b) {
    return a + b;
}

// C Output
int sum(const int* a, const int* b) {
    return *a + *b;
}
```

**Example 3: Pointer Arithmetic**
```cpp
// C++ Input
int sum_array(int* arr, int size) {
    int sum = 0;
    for (int* p = arr; p < arr + size; p++) {
        sum += *p;
    }
    return sum;
}

// C Output
int sum_array(int* arr, int size) {
    int sum = 0;
    for (int* p = arr; p < arr + size; p++) {
        sum += *p;
    }
    return sum;
}
```

**Example 4: nullptr Translation**
```cpp
// C++ Input
int* create_or_null(bool create) {
    if (create) {
        return new int(42);  // Note: Phase 5 doesn't handle 'new', manual malloc
    }
    return nullptr;
}

// C Output
int* create_or_null(int create) {
    if (create) {
        int* __temp = (int*)malloc(sizeof(int));
        *__temp = 42;
        return __temp;
    }
    return NULL;
}
```

**Example 5: Address-of and Dereference**
```cpp
// C++ Input
void modify(int* ptr) {
    *ptr = 100;
}

void test() {
    int value = 50;
    modify(&value);
}

// C Output
void modify(int* ptr) {
    *ptr = 100;
}

void test(void) {
    int value = 50;
    modify(&value);
}
```

### Estimated Effort
**Handler Extensions:**
- FunctionHandler: +100-150 LOC, 2-3 hours
- ExpressionHandler: +200-250 LOC, 3-4 hours
- TypeTranslator: 150-200 LOC, 2-3 hours

**Testing:**
- Unit tests: 400-500 LOC, 4-5 hours
- Integration tests: 250-300 LOC, 2-3 hours
- E2E tests: 200-250 LOC, 2-3 hours

**Total:** 1300-1650 LOC, 15-21 hours (~2-3 days)

---

## Phase 6: Classes (Simple)

### Phase Goal
Translate C++ classes to C structs and methods to functions with explicit `this` parameter. This is the first major transformation phase.

### Complexity Level
**3** (Moderate) - Requires class → struct and method → function transformation

### C++ Features
- Class declarations (`class ClassName { ... }`)
- Member variables (private/public/protected)
- Member functions (methods)
- Constructors (simple, no initialization lists yet)
- Destructors
- `this` pointer
- Access specifiers (ignored in C)

### C Mapping Strategy
**Class → Struct:**
```cpp
// C++ Input
class Counter {
private:
    int count;
public:
    int getCount() { return count; }
};

// C Output
struct Counter {
    int count;  // Access specifiers removed
};

int Counter_getCount(struct Counter* this) {
    return this->count;
}
```

**Method → Function with `this`:**
- Add explicit `this` parameter (always first parameter)
- Method name: `ClassName_methodName`
- Member access: `this->field`

**Constructor → Init function:**
```cpp
// C++ Input
Counter() { count = 0; }

// C Output
void Counter_init(struct Counter* this) {
    this->count = 0;
}
```

**Destructor → Cleanup function:**
```cpp
// C++ Input
~Counter() { /* cleanup */ }

// C Output
void Counter_destroy(struct Counter* this) {
    /* cleanup */
}
```

### Required Handlers
- **RecordHandler** (extend) - Translate CXXRecordDecl to RecordDecl
- **MethodHandler** (new) - Translate methods to functions
- **ConstructorHandler** (new) - Translate constructors to init functions
- **ExpressionHandler** (extend) - Translate `this` pointer, member access

### New Handler Code
**RecordHandler extensions:**
- `handleCXXRecordDecl()` - Translate class to struct
- `stripAccessSpecifiers()` - Remove public/private/protected
- `extractMemberVariables()` - Get fields only (no methods)

**MethodHandler:**
- `handleCXXMethodDecl()` - Translate method to function
- `addThisParameter()` - Add `struct ClassName* this` as first param
- `mangleMethodName()` - Create `ClassName_methodName`
- `translateMemberAccess()` - Convert field access to `this->field`

**ConstructorHandler:**
- `handleCXXConstructorDecl()` - Translate to `ClassName_init`
- `translateConstructorBody()` - Handle member initialization

**DestructorHandler:**
- `handleCXXDestructorDecl()` - Translate to `ClassName_destroy`

**ExpressionHandler additions:**
- `handleCXXThisExpr()` - Translate `this` keyword
- `handleMemberExpr()` - Extend for method calls (translate to function calls)

### AST Nodes
- `CXXRecordDecl` - C++ class declarations
- `FieldDecl` - Member variables
- `CXXMethodDecl` - Member functions
- `CXXConstructorDecl` - Constructors
- `CXXDestructorDecl` - Destructors
- `CXXThisExpr` - `this` keyword
- `MemberExpr` - Member access (extended from Phase 4)

### Dependencies
**Phase 4** - Requires struct infrastructure
**Phase 1** - Requires function infrastructure

### Test Strategy
**Unit Tests (40+ tests):**
- Simple class to struct
- Access specifier removal
- Method translation with `this`
- Constructor translation
- Destructor translation
- `this` pointer usage

**Integration Tests (20-25 tests):**
- Class with multiple methods
- Constructor + destructor
- Classes with member variables of class types

**E2E Tests (5-10 tests):**
- Complete class-based programs
- Object lifecycle (construction + usage + destruction)

### Verification Criteria
- [ ] All unit tests pass
- [ ] Classes correctly translated to structs
- [ ] Methods correctly translated to functions with `this`
- [ ] Constructors create valid init functions
- [ ] Destructors create valid cleanup functions
- [ ] 100% coverage for class translation handlers

### Example Translations

**Example 1: Simple Class**
```cpp
// C++ Input
class Counter {
private:
    int count;
public:
    Counter() { count = 0; }
    void increment() { count++; }
    int getCount() { return count; }
};

// C Output (header)
struct Counter {
    int count;
};

void Counter_init(struct Counter* this);
void Counter_increment(struct Counter* this);
int Counter_getCount(struct Counter* this);

// C Output (implementation)
void Counter_init(struct Counter* this) {
    this->count = 0;
}

void Counter_increment(struct Counter* this) {
    this->count++;
}

int Counter_getCount(struct Counter* this) {
    return this->count;
}
```

**Example 2: Class with Constructor Parameters**
```cpp
// C++ Input
class Point {
    int x, y;
public:
    Point(int x, int y) {
        this->x = x;
        this->y = y;
    }
    int getX() { return x; }
    int getY() { return y; }
};

// C Output
struct Point {
    int x;
    int y;
};

void Point_init(struct Point* this, int x, int y) {
    this->x = x;
    this->y = y;
}

int Point_getX(struct Point* this) {
    return this->x;
}

int Point_getY(struct Point* this) {
    return this->y;
}
```

**Example 3: Class with Destructor**
```cpp
// C++ Input
class FileHandle {
    int fd;
public:
    FileHandle(int fd) { this->fd = fd; }
    ~FileHandle() { close(fd); }
    int getFd() { return fd; }
};

// C Output
struct FileHandle {
    int fd;
};

void FileHandle_init(struct FileHandle* this, int fd) {
    this->fd = fd;
}

void FileHandle_destroy(struct FileHandle* this) {
    close(this->fd);
}

int FileHandle_getFd(struct FileHandle* this) {
    return this->fd;
}
```

**Example 4: Multiple Member Variables**
```cpp
// C++ Input
class Rectangle {
    int width;
    int height;
public:
    Rectangle(int w, int h) : width(w), height(h) {}
    int area() { return width * height; }
    int perimeter() { return 2 * (width + height); }
};

// C Output
struct Rectangle {
    int width;
    int height;
};

void Rectangle_init(struct Rectangle* this, int w, int h) {
    this->width = w;
    this->height = h;
}

int Rectangle_area(struct Rectangle* this) {
    return this->width * this->height;
}

int Rectangle_perimeter(struct Rectangle* this) {
    return 2 * (this->width + this->height);
}
```

**Example 5: Class Usage**
```cpp
// C++ Input
void test() {
    Counter c;
    c.increment();
    c.increment();
    int count = c.getCount();
}

// C Output
void test(void) {
    struct Counter c;
    Counter_init(&c);
    Counter_increment(&c);
    Counter_increment(&c);
    int count = Counter_getCount(&c);
    Counter_destroy(&c);  // Auto-injected
}
```

### Estimated Effort
**Handler Implementation:**
- RecordHandler extensions: +100-150 LOC, 2-3 hours
- MethodHandler: 250-350 LOC, 4-5 hours
- ConstructorHandler: 200-250 LOC, 3-4 hours
- DestructorHandler: 100-150 LOC, 2-3 hours
- ExpressionHandler extensions: +100-150 LOC, 2-3 hours

**Testing:**
- Unit tests: 600-800 LOC, 6-8 hours
- Integration tests: 350-450 LOC, 3-4 hours
- E2E tests: 250-350 LOC, 2-3 hours

**Total:** 1950-2600 LOC, 24-33 hours (~3-4 days)

---

## Phase 7: Method Calls

### Phase Goal
Translate C++ method call syntax (`obj.method()`) to C function call syntax with explicit `this` argument.

### Complexity Level
**3** (Moderate) - Requires call-site transformation

### C++ Features
- Method calls on objects (`obj.method(args)`)
- Method calls through pointers (`ptr->method(args)`)
- Method overloading (name mangling)
- Chained method calls (`obj.method1().method2()`)

### C Mapping Strategy
**Method call → Function call with `this`:**
```cpp
// C++ Input
Counter c;
c.increment();

// C Output
struct Counter c;
Counter_init(&c);
Counter_increment(&c);
```

**Pointer method call:**
```cpp
// C++ Input
Counter* ptr = &c;
ptr->increment();

// C Output
struct Counter* ptr = &c;
Counter_increment(ptr);
```

**Method overloading → Name mangling:**
```cpp
// C++ Input
class Math {
    int add(int a, int b) { return a + b; }
    double add(double a, double b) { return a + b; }
};

// C Output
int Math_add_int_int(struct Math* this, int a, int b) {
    return a + b;
}

double Math_add_double_double(struct Math* this, double a, double b) {
    return a + b;
}
```

### Required Handlers
- **ExpressionHandler** (extend) - Translate method call expressions
- **MethodHandler** (extend) - Generate overload-safe names

### New Handler Code
**ExpressionHandler additions:**
- `handleCXXMemberCallExpr()` - Translate method calls
- `extractObjectExpr()` - Get object being called on
- `insertThisArgument()` - Add object as first argument
- `translateToCallExpr()` - Convert to regular C function call

**MethodHandler additions:**
- `mangleOverloadedName()` - Create unique names for overloads
- `generateTypeSignature()` - Create type-based suffix for overloads

### AST Nodes
- `MemberExpr` - Member access (method reference)
- `CXXMemberCallExpr` - Method call expression
- `CallExpr` - Regular function call (target C AST)

### Dependencies
**Phase 6** - Requires class and method infrastructure

### Test Strategy
**Unit Tests (30+ tests):**
- Simple method calls
- Method calls through pointers
- Method overloading
- Chained calls
- Const method calls

**Integration Tests (15-20 tests):**
- Complex call chains
- Overloaded method calls
- Mixed object/pointer calls

**E2E Tests (5-10 tests):**
- Programs with extensive method usage
- Builder pattern implementations

### Verification Criteria
- [ ] All unit tests pass
- [ ] Method calls correctly transformed
- [ ] Overloads get unique names
- [ ] Chained calls work correctly
- [ ] 100% coverage for method call handling

### Example Translations

**Example 1: Simple Method Call**
```cpp
// C++ Input
class Counter {
    int count;
public:
    void increment() { count++; }
    int get() { return count; }
};

void test() {
    Counter c;
    c.increment();
    int val = c.get();
}

// C Output
void test(void) {
    struct Counter c;
    Counter_init(&c);
    Counter_increment(&c);
    int val = Counter_get(&c);
    Counter_destroy(&c);
}
```

**Example 2: Method Call Through Pointer**
```cpp
// C++ Input
void increment_counter(Counter* ptr) {
    ptr->increment();
}

// C Output
void increment_counter(struct Counter* ptr) {
    Counter_increment(ptr);
}
```

**Example 3: Method Overloading**
```cpp
// C++ Input
class Math {
public:
    int add(int a, int b) { return a + b; }
    double add(double a, double b) { return a + b; }
};

void test() {
    Math m;
    int i = m.add(1, 2);
    double d = m.add(1.5, 2.5);
}

// C Output
int Math_add_i_i(struct Math* this, int a, int b) {
    return a + b;
}

double Math_add_d_d(struct Math* this, double a, double b) {
    return a + b;
}

void test(void) {
    struct Math m;
    Math_init(&m);
    int i = Math_add_i_i(&m, 1, 2);
    double d = Math_add_d_d(&m, 1.5, 2.5);
    Math_destroy(&m);
}
```

**Example 4: Chained Method Calls**
```cpp
// C++ Input
class Builder {
    int value;
public:
    Builder& setValue(int v) { value = v; return *this; }
    int build() { return value; }
};

void test() {
    Builder b;
    int result = b.setValue(10).build();
}

// C Output
struct Builder* Builder_setValue(struct Builder* this, int v) {
    this->value = v;
    return this;
}

int Builder_build(struct Builder* this) {
    return this->value;
}

void test(void) {
    struct Builder b;
    Builder_init(&b);
    int result = Builder_build(Builder_setValue(&b, 10));
    Builder_destroy(&b);
}
```

**Example 5: Const Method**
```cpp
// C++ Input
class Point {
    int x, y;
public:
    int getX() const { return x; }
    int getY() const { return y; }
};

// C Output
int Point_getX(const struct Point* this) {
    return this->x;
}

int Point_getY(const struct Point* this) {
    return this->y;
}
```

### Estimated Effort
**Handler Extensions:**
- ExpressionHandler: +250-350 LOC, 4-5 hours
- MethodHandler: +100-150 LOC, 2-3 hours

**Testing:**
- Unit tests: 450-550 LOC, 4-5 hours
- Integration tests: 250-300 LOC, 2-3 hours
- E2E tests: 200-250 LOC, 2-3 hours

**Total:** 1250-1600 LOC, 14-19 hours (~2-3 days)

---

## Phase 8: Enums

### Phase Goal
Translate both unscoped and scoped enums, with automatic name prefixing for scoped enums.

### Complexity Level
**2** (Intermediate) - Scoped enums require name prefixing

### C++ Features
- Unscoped enums (`enum Color { Red, Green, Blue }`)
- Scoped enums (`enum class State { Menu, Playing }`)
- Enum constant references
- Enum values in expressions
- Enum underlying types

### C Mapping Strategy
**Unscoped enums:** Direct mapping
```cpp
// C++ Input
enum Color { Red, Green, Blue };

// C Output
enum Color { Red, Green, Blue };
```

**Scoped enums:** Prefix constants with enum name
```cpp
// C++ Input
enum class GameState { Menu, Playing, GameOver };

// C Output
enum GameState { GameState__Menu, GameState__Playing, GameState__GameOver };
```

**Enum references:** Update to prefixed names
```cpp
// C++ Input
GameState state = GameState::Menu;

// C Output
enum GameState state = GameState__Menu;
```

### Required Handlers
- **EnumHandler** (new) - Translate enum declarations
- **ExpressionHandler** (extend) - Translate enum constant references

### New Handler Code
**EnumHandler:**
- `handleEnumDecl()` - Translate enum declarations
- `generateEnumConstants()` - Create enum constants with optional prefixing
- `prefixScopedEnum()` - Add `EnumName__` prefix for scoped enums

**ExpressionHandler additions:**
- `handleDeclRefExpr()` - Extend for enum constant references
- `prefixEnumReference()` - Update scoped enum references

### AST Nodes
- `EnumDecl` - Enum declarations
- `EnumConstantDecl` - Enum constants
- `DeclRefExpr` - References to enum constants (already handled, extend)

### Dependencies
**Phase 1** - Requires basic expression infrastructure

### Test Strategy
**Unit Tests (25+ tests):**
- Unscoped enum declaration
- Scoped enum declaration
- Enum constant references
- Enum in switch statements
- Enum underlying types

**Integration Tests (10-15 tests):**
- Enums with switch statements
- Enums as function parameters
- Enums in structs

**E2E Tests (5-10 tests):**
- State machine implementations
- Programs using enums for configuration

### Verification Criteria
- [ ] All unit tests pass
- [ ] Unscoped enums unchanged
- [ ] Scoped enums correctly prefixed
- [ ] Enum references correctly translated
- [ ] 100% coverage for EnumHandler

### Example Translations

**Example 1: Unscoped Enum**
```cpp
// C++ Input
enum Color {
    Red = 0,
    Green = 1,
    Blue = 2
};

Color getColor() {
    return Green;
}

// C Output
enum Color {
    Red = 0,
    Green = 1,
    Blue = 2
};

enum Color getColor(void) {
    return Green;
}
```

**Example 2: Scoped Enum**
```cpp
// C++ Input
enum class GameState {
    Menu,
    Playing,
    GameOver
};

GameState getInitialState() {
    return GameState::Menu;
}

// C Output
enum GameState {
    GameState__Menu,
    GameState__Playing,
    GameState__GameOver
};

enum GameState getInitialState(void) {
    return GameState__Menu;
}
```

**Example 3: Enum in Switch**
```cpp
// C++ Input
enum class Direction { North, South, East, West };

void move(Direction dir) {
    switch (dir) {
        case Direction::North: /* ... */ break;
        case Direction::South: /* ... */ break;
        case Direction::East: /* ... */ break;
        case Direction::West: /* ... */ break;
    }
}

// C Output
enum Direction { Direction__North, Direction__South, Direction__East, Direction__West };

void move(enum Direction dir) {
    switch (dir) {
        case Direction__North: /* ... */ break;
        case Direction__South: /* ... */ break;
        case Direction__East: /* ... */ break;
        case Direction__West: /* ... */ break;
    }
}
```

**Example 4: Enum as Struct Member**
```cpp
// C++ Input
enum class Status { Success, Error };

struct Result {
    Status status;
    int value;
};

// C Output
enum Status { Status__Success, Status__Error };

struct Result {
    enum Status status;
    int value;
};
```

**Example 5: Enum with Explicit Values**
```cpp
// C++ Input
enum class ErrorCode {
    None = 0,
    NotFound = 404,
    ServerError = 500
};

// C Output
enum ErrorCode {
    ErrorCode__None = 0,
    ErrorCode__NotFound = 404,
    ErrorCode__ServerError = 500
};
```

### Estimated Effort
**Handler Implementation:**
- EnumHandler: 200-250 LOC, 3-4 hours
- ExpressionHandler extensions: +50-100 LOC, 1-2 hours

**Testing:**
- Unit tests: 350-400 LOC, 3-4 hours
- Integration tests: 150-200 LOC, 2-3 hours
- E2E tests: 150-200 LOC, 1-2 hours

**Total:** 900-1150 LOC, 10-15 hours (~1-2 days)

---

## Phase 9: Inheritance (Single)

### Phase Goal
Support single inheritance by embedding base class as first field in derived struct.

### Complexity Level
**4** (Advanced) - Requires struct composition and field access rewriting

### C++ Features
- Single inheritance (`class Derived : public Base`)
- Base class field access
- Base class method calls
- Constructor chaining (call base constructor)
- Destructor chaining (call base destructor)

### C Mapping Strategy
**Inheritance → Composition:**
```cpp
// C++ Input
class Base {
    int baseField;
public:
    void baseMethod() {}
};

class Derived : public Base {
    int derivedField;
public:
    void derivedMethod() {}
};

// C Output
struct Base {
    int baseField;
};

struct Derived {
    struct Base __base;  // Base embedded as first field
    int derivedField;
};

void Base_baseMethod(struct Base* this) {}
void Derived_derivedMethod(struct Derived* this) {}
```

**Field access:**
```cpp
// C++ Input
void Derived::useBase() {
    baseField = 10;  // Access base field
}

// C Output
void Derived_useBase(struct Derived* this) {
    this->__base.baseField = 10;  // Access through embedded base
}
```

**Method calls:**
```cpp
// C++ Input
void Derived::callBase() {
    baseMethod();  // Call base method
}

// C Output
void Derived_callBase(struct Derived* this) {
    Base_baseMethod(&this->__base);  // Pass embedded base
}
```

### Required Handlers
- **RecordHandler** (extend) - Handle inheritance relationships
- **ConstructorHandler** (extend) - Add base constructor calls
- **ExpressionHandler** (extend) - Rewrite base field access

### New Handler Code
**RecordHandler extensions:**
- `handleInheritance()` - Detect base classes
- `embedBaseStruct()` - Add `__base` field as first member
- `checkSingleInheritance()` - Verify only single inheritance

**ConstructorHandler extensions:**
- `callBaseConstructor()` - Insert base init call
- `initializeBaseFirst()` - Ensure base initialized before derived

**DestructorHandler extensions:**
- `callBaseDestructor()` - Insert base destroy call after derived cleanup

**ExpressionHandler additions:**
- `rewriteBaseFieldAccess()` - Convert `field` to `this->__base.field`
- `rewriteBaseMethodCall()` - Convert `method()` to `Base_method(&this->__base)`

### AST Nodes
- `CXXBaseSpecifier` - Base class specification
- `CXXRecordDecl` (with bases) - Derived class
- `MemberExpr` (base field access) - Requires rewriting

### Dependencies
**Phase 6** - Requires class infrastructure
**Phase 7** - Requires method call infrastructure

### Test Strategy
**Unit Tests (30+ tests):**
- Simple single inheritance
- Base field access
- Base method calls
- Constructor chaining
- Destructor chaining

**Integration Tests (15-20 tests):**
- Derived class using base functionality
- Multiple levels of inheritance (Base → Middle → Derived)
- Virtual-like method calls (non-virtual first)

**E2E Tests (5-10 tests):**
- Shape hierarchy (Shape → Circle, Rectangle)
- Entity-Component patterns

### Verification Criteria
- [ ] All unit tests pass
- [ ] Base embedded as first field
- [ ] Base field access correct
- [ ] Base method calls correct
- [ ] Constructor/destructor chaining works
- [ ] 100% coverage for inheritance handling

### Example Translations

**Example 1: Simple Inheritance**
```cpp
// C++ Input
class Animal {
protected:
    int age;
public:
    Animal(int age) : age(age) {}
    int getAge() { return age; }
};

class Dog : public Animal {
    int barkVolume;
public:
    Dog(int age, int volume) : Animal(age), barkVolume(volume) {}
    void bark() { /* ... */ }
};

// C Output
struct Animal {
    int age;
};

void Animal_init(struct Animal* this, int age) {
    this->age = age;
}

int Animal_getAge(struct Animal* this) {
    return this->age;
}

struct Dog {
    struct Animal __base;
    int barkVolume;
};

void Dog_init(struct Dog* this, int age, int volume) {
    Animal_init(&this->__base, age);
    this->barkVolume = volume;
}

void Dog_bark(struct Dog* this) {
    /* ... */
}
```

**Example 2: Base Field Access**
```cpp
// C++ Input
class Derived : public Base {
public:
    void useBase() {
        baseField = 10;  // Access base field
    }
};

// C Output
struct Derived {
    struct Base __base;
};

void Derived_useBase(struct Derived* this) {
    this->__base.baseField = 10;
}
```

**Example 3: Base Method Call**
```cpp
// C++ Input
class Derived : public Base {
public:
    void callBase() {
        baseMethod();  // Call base method
    }
};

// C Output
void Derived_callBase(struct Derived* this) {
    Base_baseMethod(&this->__base);
}
```

**Example 4: Multiple Levels**
```cpp
// C++ Input
class Base {
    int a;
};

class Middle : public Base {
    int b;
};

class Derived : public Middle {
    int c;
};

// C Output
struct Base {
    int a;
};

struct Middle {
    struct Base __base;
    int b;
};

struct Derived {
    struct Middle __base;  // Contains Base nested
    int c;
};
```

**Example 5: Usage Example**
```cpp
// C++ Input
void test() {
    Dog dog(5, 10);
    int age = dog.getAge();  // Base method
    dog.bark();              // Derived method
}

// C Output
void test(void) {
    struct Dog dog;
    Dog_init(&dog, 5, 10);
    int age = Animal_getAge(&dog.__base);
    Dog_bark(&dog);
    Dog_destroy(&dog);
}
```

### Estimated Effort
**Handler Extensions:**
- RecordHandler: +200-250 LOC, 3-4 hours
- ConstructorHandler: +100-150 LOC, 2-3 hours
- DestructorHandler: +50-100 LOC, 1-2 hours
- ExpressionHandler: +150-200 LOC, 3-4 hours

**Testing:**
- Unit tests: 500-600 LOC, 5-6 hours
- Integration tests: 300-350 LOC, 3-4 hours
- E2E tests: 250-300 LOC, 2-3 hours

**Total:** 1550-1950 LOC, 19-26 hours (~2.5-3.5 days)

---

## Phase 10: Templates (Monomorphization)

### Phase Goal
Support class and function templates via monomorphization - generate concrete C struct/function for each template instantiation.

### Complexity Level
**5** (Most Complex) - Requires template analysis and code generation

### C++ Features
- Class templates (`template<typename T> class Container`)
- Function templates (`template<typename T> T max(T a, T b)`)
- Template instantiation
- Multiple template parameters
- Template specialization (explicit instantiation)

### C Mapping Strategy
**Template → Multiple Concrete Types:**
```cpp
// C++ Input
template<typename T>
class Box {
    T value;
public:
    void set(T v) { value = v; }
    T get() { return value; }
};

Box<int> intBox;
Box<double> doubleBox;

// C Output
struct Box__int {
    int value;
};

void Box__int_set(struct Box__int* this, int v) {
    this->value = v;
}

int Box__int_get(struct Box__int* this) {
    return this->value;
}

struct Box__double {
    double value;
};

void Box__double_set(struct Box__double* this, double v) {
    this->value = v;
}

double Box__double_get(struct Box__double* this) {
    return this->value;
}
```

**Function templates:**
```cpp
// C++ Input
template<typename T>
T max(T a, T b) {
    return (a > b) ? a : b;
}

int i = max(10, 20);
double d = max(1.5, 2.5);

// C Output
int max__int(int a, int b) {
    return (a > b) ? a : b;
}

double max__double(double a, double b) {
    return (a > b) ? a : b;
}

int i = max__int(10, 20);
double d = max__double(1.5, 2.5);
```

### Required Handlers
- **TemplateMonomorphizer** (extend existing) - Detect and generate instantiations
- **RecordHandler** (extend) - Handle template class instantiation
- **FunctionHandler** (extend) - Handle template function instantiation

### New Handler Code
**TemplateMonomorphizer:**
- `findAllInstantiations()` - Scan AST for template uses
- `generateMonomorphized()` - Create concrete type/function for each instantiation
- `mangleTemplateName()` - Create unique name: `ClassName__type1_type2`
- `substituteTemplateParams()` - Replace `T` with concrete type throughout

**RecordHandler extensions:**
- `handleClassTemplateSpecialization()` - Process instantiated templates

**FunctionHandler extensions:**
- `handleFunctionTemplateSpecialization()` - Process instantiated function templates

### AST Nodes
- `ClassTemplateDecl` - Template class declarations
- `FunctionTemplateDecl` - Template function declarations
- `ClassTemplateSpecializationDecl` - Instantiated template class
- `TemplateTypeParmDecl` - Template type parameters (`typename T`)
- `TemplateSpecializationType` - Template type usage

### Dependencies
**Phase 6** - Requires class infrastructure
**Phase 1** - Requires function infrastructure

### Test Strategy
**Unit Tests (40+ tests):**
- Simple class template with single type param
- Class template with multiple type params
- Function template
- Template instantiation detection
- Name mangling for templates

**Integration Tests (20-25 tests):**
- Template class with methods
- Template functions called with different types
- Nested templates

**E2E Tests (5-10 tests):**
- Generic container implementations
- Template-based algorithms

### Verification Criteria
- [ ] All unit tests pass
- [ ] All template instantiations detected
- [ ] Concrete types generated correctly
- [ ] Template code substitution correct
- [ ] 100% coverage for template handling

### Example Translations

**Example 1: Simple Class Template**
```cpp
// C++ Input
template<typename T>
class Container {
    T value;
public:
    void set(T v) { value = v; }
    T get() { return value; }
};

void test() {
    Container<int> intContainer;
    intContainer.set(42);

    Container<float> floatContainer;
    floatContainer.set(3.14f);
}

// C Output
struct Container__int {
    int value;
};

void Container__int_set(struct Container__int* this, int v) {
    this->value = v;
}

int Container__int_get(struct Container__int* this) {
    return this->value;
}

struct Container__float {
    float value;
};

void Container__float_set(struct Container__float* this, float v) {
    this->value = v;
}

float Container__float_get(struct Container__float* this) {
    return this->value;
}

void test(void) {
    struct Container__int intContainer;
    Container__int_init(&intContainer);
    Container__int_set(&intContainer, 42);

    struct Container__float floatContainer;
    Container__float_init(&floatContainer);
    Container__float_set(&floatContainer, 3.14f);

    Container__int_destroy(&intContainer);
    Container__float_destroy(&floatContainer);
}
```

**Example 2: Function Template**
```cpp
// C++ Input
template<typename T>
T max(T a, T b) {
    return (a > b) ? a : b;
}

void test() {
    int maxInt = max(10, 20);
    double maxDouble = max(1.5, 2.5);
}

// C Output
int max__int(int a, int b) {
    return (a > b) ? a : b;
}

double max__double(double a, double b) {
    return (a > b) ? a : b;
}

void test(void) {
    int maxInt = max__int(10, 20);
    double maxDouble = max__double(1.5, 2.5);
}
```

**Example 3: Multiple Template Parameters**
```cpp
// C++ Input
template<typename K, typename V>
class Pair {
    K key;
    V value;
public:
    Pair(K k, V v) : key(k), value(v) {}
    K getKey() { return key; }
    V getValue() { return value; }
};

// C Output
struct Pair__int_double {
    int key;
    double value;
};

void Pair__int_double_init(struct Pair__int_double* this, int k, double v) {
    this->key = k;
    this->value = v;
}

int Pair__int_double_getKey(struct Pair__int_double* this) {
    return this->key;
}

double Pair__int_double_getValue(struct Pair__int_double* this) {
    return this->value;
}
```

**Example 4: Nested Template**
```cpp
// C++ Input
template<typename T>
class Outer {
    template<typename U>
    class Inner {
        T t;
        U u;
    };
};

// C Output (monomorphized)
struct Outer__int__Inner__double {
    int t;
    double u;
};
```

**Example 5: Template with Template Parameter**
```cpp
// C++ Input
template<typename T>
class Container {
    T* data;
    int size;
};

Container<int> intContainer;
Container<Container<int>> nestedContainer;

// C Output
struct Container__int {
    int* data;
    int size;
};

struct Container__Container__int {
    struct Container__int* data;
    int size;
};
```

### Estimated Effort
**Handler Implementation:**
- TemplateMonomorphizer extensions: +400-500 LOC, 6-8 hours
- RecordHandler extensions: +100-150 LOC, 2-3 hours
- FunctionHandler extensions: +100-150 LOC, 2-3 hours

**Testing:**
- Unit tests: 700-900 LOC, 8-10 hours
- Integration tests: 400-500 LOC, 4-5 hours
- E2E tests: 300-400 LOC, 3-4 hours

**Total:** 2000-2600 LOC, 25-33 hours (~3-4 days)

---

## Phase 11: Virtual Methods (Advanced)

### Phase Goal
Support virtual methods and polymorphism using vtables (virtual method tables).

### Complexity Level
**5** (Most Complex) - Requires vtable generation and indirection

### C++ Features
- Virtual methods
- Virtual destructors
- Pure virtual methods (abstract classes)
- Virtual method overriding
- Polymorphic calls through base pointers

### C Mapping Strategy
**Virtual methods → Vtable:**
```cpp
// C++ Input
class Base {
public:
    virtual void method() {}
    virtual ~Base() {}
};

class Derived : public Base {
public:
    void method() override {}  // Override
};

// C Output
// Vtable struct
struct Base__vtable {
    void (*method)(struct Base*);
    void (*destructor)(struct Base*);
};

struct Base {
    struct Base__vtable* __vtable;
};

// Vtable instances
struct Base__vtable Base__vtable_instance = {
    .method = Base_method,
    .destructor = Base_destroy
};

struct Base__vtable Derived__vtable_instance = {
    .method = Derived_method,  // Overridden
    .destructor = Derived_destroy
};

// Polymorphic call
void call_method(struct Base* obj) {
    obj->__vtable->method(obj);  // Indirect call through vtable
}
```

### Required Handlers
- **VirtualMethodHandler** (new) - Generate vtables and virtual dispatch
- **RecordHandler** (extend) - Add vtable pointer to classes with virtual methods
- **ConstructorHandler** (extend) - Initialize vtable pointer
- **ExpressionHandler** (extend) - Translate virtual calls to vtable indirection

### New Handler Code
**VirtualMethodHandler:**
- `generateVtable()` - Create vtable struct definition
- `populateVtableInstance()` - Create vtable instance with function pointers
- `addVtablePointer()` - Add `__vtable` field to struct
- `initializeVtable()` - Set vtable pointer in constructor

**RecordHandler extensions:**
- `detectVirtualMethods()` - Identify classes with virtual methods
- `addVtableField()` - Add `struct ClassName__vtable* __vtable` as first field

**ConstructorHandler extensions:**
- `setVtablePointer()` - Initialize `this->__vtable = &ClassName__vtable_instance`

**ExpressionHandler additions:**
- `handleVirtualCall()` - Translate `obj->virtualMethod()` to `obj->__vtable->virtualMethod(obj)`

### AST Nodes
- `CXXMethodDecl` (`isVirtual()`) - Virtual method declarations
- `CXXDestructorDecl` (`isVirtual()`) - Virtual destructors
- `CXXRecordDecl` (has virtual methods) - Classes with vtables

### Dependencies
**Phase 9** - Requires inheritance infrastructure
**Phase 6, 7** - Requires class and method infrastructure

### Test Strategy
**Unit Tests (40+ tests):**
- Simple virtual method
- Virtual method override
- Pure virtual method (abstract class)
- Virtual destructor
- Vtable generation

**Integration Tests (20-25 tests):**
- Polymorphic calls
- Multiple inheritance (not supported, error handling)
- Virtual method chains

**E2E Tests (5-10 tests):**
- Shape polymorphism example
- Plugin architecture

### Verification Criteria
- [ ] All unit tests pass
- [ ] Vtables generated correctly
- [ ] Polymorphic calls work
- [ ] Virtual destructors called correctly
- [ ] 100% coverage for virtual method handling

### Example Translations

**Example 1: Simple Virtual Method**
```cpp
// C++ Input
class Shape {
public:
    virtual double area() = 0;  // Pure virtual
    virtual ~Shape() {}
};

class Circle : public Shape {
    double radius;
public:
    Circle(double r) : radius(r) {}
    double area() override { return 3.14159 * radius * radius; }
};

// C Output
// Vtable definitions
struct Shape__vtable {
    double (*area)(struct Shape*);
    void (*destructor)(struct Shape*);
};

struct Shape {
    struct Shape__vtable* __vtable;
};

struct Circle {
    struct Shape __base;
    double radius;
};

// Method implementations
double Circle_area(struct Circle* this) {
    return 3.14159 * this->radius * this->radius;
}

void Circle_destroy(struct Circle* this) {
    Shape_destroy(&this->__base);
}

// Vtable instances
struct Shape__vtable Circle__vtable_instance = {
    .area = (double (*)(struct Shape*))Circle_area,
    .destructor = (void (*)(struct Shape*))Circle_destroy
};

void Circle_init(struct Circle* this, double r) {
    this->__base.__vtable = &Circle__vtable_instance;
    this->radius = r;
}

// Polymorphic usage
double get_area(struct Shape* shape) {
    return shape->__vtable->area(shape);
}
```

**Example 2: Virtual Destructor**
```cpp
// C++ Input
class Base {
public:
    virtual ~Base() { cleanup(); }
protected:
    void cleanup() {}
};

class Derived : public Base {
    int* data;
public:
    Derived() { data = new int[10]; }
    ~Derived() override { delete[] data; }
};

void test() {
    Base* ptr = new Derived();
    delete ptr;  // Must call Derived::~Derived
}

// C Output
void Base_cleanup(struct Base* this) {}
void Base_destroy(struct Base* this) {
    Base_cleanup(this);
}

void Derived_destroy(struct Derived* this) {
    free(this->data);
    Base_destroy(&this->__base);
}

struct Base__vtable Base__vtable_instance = {
    .destructor = Base_destroy
};

struct Base__vtable Derived__vtable_instance = {
    .destructor = (void (*)(struct Base*))Derived_destroy
};

void test(void) {
    struct Derived* ptr = (struct Derived*)malloc(sizeof(struct Derived));
    Derived_init(ptr);

    // Polymorphic delete
    ptr->__base.__vtable->destructor((struct Base*)ptr);
    free(ptr);
}
```

**Example 3: Multiple Virtual Methods**
```cpp
// C++ Input
class Animal {
public:
    virtual void speak() = 0;
    virtual void move() = 0;
};

class Dog : public Animal {
public:
    void speak() override { printf("Woof!\n"); }
    void move() override { printf("Running\n"); }
};

// C Output
struct Animal__vtable {
    void (*speak)(struct Animal*);
    void (*move)(struct Animal*);
};

struct Animal {
    struct Animal__vtable* __vtable;
};

void Dog_speak(struct Dog* this) {
    printf("Woof!\n");
}

void Dog_move(struct Dog* this) {
    printf("Running\n");
}

struct Animal__vtable Dog__vtable_instance = {
    .speak = (void (*)(struct Animal*))Dog_speak,
    .move = (void (*)(struct Animal*))Dog_move
};
```

**Example 4: Non-virtual and Virtual Mix**
```cpp
// C++ Input
class Base {
public:
    void nonVirtual() {}
    virtual void virtualMethod() {}
};

// C Output
struct Base__vtable {
    void (*virtualMethod)(struct Base*);
};

struct Base {
    struct Base__vtable* __vtable;
};

void Base_nonVirtual(struct Base* this) {}
void Base_virtualMethod(struct Base* this) {}

// Non-virtual: direct call
void test(struct Base* obj) {
    Base_nonVirtual(obj);  // Direct call
    obj->__vtable->virtualMethod(obj);  // Indirect call
}
```

**Example 5: Abstract Class Prevention**
```cpp
// C++ Input
class Abstract {
public:
    virtual void pureVirtual() = 0;
};

// Cannot instantiate:
// Abstract a;  // Error in C++

// C Output
struct Abstract__vtable {
    void (*pureVirtual)(struct Abstract*);
};

// No implementation for pureVirtual - linker error if called
// Must be overridden in derived class
```

### Estimated Effort
**Handler Implementation:**
- VirtualMethodHandler: 500-700 LOC, 8-10 hours
- RecordHandler extensions: +100-150 LOC, 2-3 hours
- ConstructorHandler extensions: +50-100 LOC, 1-2 hours
- ExpressionHandler extensions: +150-200 LOC, 3-4 hours

**Testing:**
- Unit tests: 700-900 LOC, 8-10 hours
- Integration tests: 400-500 LOC, 4-5 hours
- E2E tests: 300-400 LOC, 3-4 hours

**Total:** 2200-2950 LOC, 29-38 hours (~4-5 days)

---

## Phase 12: Namespaces

### Phase Goal
Support C++ namespaces by prefixing all names with namespace path.

### Complexity Level
**3** (Moderate) - Name transformation and scope tracking

### C++ Features
- Namespace declarations (`namespace Name { ... }`)
- Nested namespaces (`namespace Outer { namespace Inner { ... } }`)
- Using directives (`using namespace Name;`)
- Anonymous namespaces (translate to `static`)

### C Mapping Strategy
**Namespace → Name prefix:**
```cpp
// C++ Input
namespace Math {
    int add(int a, int b) { return a + b; }

    namespace Advanced {
        double sqrt(double x) { /* ... */ }
    }
}

// C Output
int Math_add(int a, int b) {
    return a + b;
}

double Math_Advanced_sqrt(double x) {
    /* ... */
}
```

**Using directive → Resolve at translation time:**
```cpp
// C++ Input
using namespace Math;
int result = add(1, 2);

// C Output
int result = Math_add(1, 2);
```

**Anonymous namespace → static:**
```cpp
// C++ Input
namespace {
    int helper() { return 42; }
}

// C Output
static int helper(void) {
    return 42;
}
```

### Required Handlers
- **NamespaceHandler** (new) - Track namespace context
- All handlers (extend) - Add namespace prefix to names

### New Handler Code
**NamespaceHandler:**
- `enterNamespace()` - Track namespace entry
- `exitNamespace()` - Track namespace exit
- `getCurrentNamespacePath()` - Get full namespace path (e.g., "Outer__Inner")
- `prefixWithNamespace()` - Add namespace prefix to identifier

**All handlers extensions:**
- Update name generation to include namespace prefix
- Example: `FunctionHandler` generates `Namespace_functionName` instead of `functionName`

### AST Nodes
- `NamespaceDecl` - Namespace declarations
- `UsingDirectiveDecl` - Using directives

### Dependencies
**All previous phases** - Namespaces can contain any declaration

### Test Strategy
**Unit Tests (25+ tests):**
- Simple namespace
- Nested namespaces
- Using directive
- Anonymous namespace
- Name collision resolution

**Integration Tests (15-20 tests):**
- Functions in namespaces
- Classes in namespaces
- Cross-namespace references

**E2E Tests (5-10 tests):**
- Complete programs with namespaces
- Library-style code organization

### Verification Criteria
- [ ] All unit tests pass
- [ ] Namespace names correctly prefixed
- [ ] Using directives resolved
- [ ] Anonymous namespaces become static
- [ ] 100% coverage for namespace handling

### Example Translations

**Example 1: Simple Namespace**
```cpp
// C++ Input
namespace Utils {
    int square(int x) {
        return x * x;
    }
}

int main() {
    return Utils::square(5);
}

// C Output
int Utils_square(int x) {
    return x * x;
}

int main(void) {
    return Utils_square(5);
}
```

**Example 2: Nested Namespace**
```cpp
// C++ Input
namespace Company {
    namespace Product {
        class Feature {
        public:
            void run() {}
        };
    }
}

// C Output
struct Company_Product_Feature {
};

void Company_Product_Feature_run(struct Company_Product_Feature* this) {
}
```

**Example 3: Using Directive**
```cpp
// C++ Input
namespace Math {
    int add(int a, int b) { return a + b; }
}

using namespace Math;

int test() {
    return add(1, 2);
}

// C Output
int Math_add(int a, int b) {
    return a + b;
}

int test(void) {
    return Math_add(1, 2);  // Resolved at translation time
}
```

**Example 4: Anonymous Namespace**
```cpp
// C++ Input
namespace {
    int internalHelper() {
        return 42;
    }
}

int publicFunction() {
    return internalHelper();
}

// C Output
static int internalHelper(void) {
    return 42;
}

int publicFunction(void) {
    return internalHelper();
}
```

**Example 5: Namespace with Classes**
```cpp
// C++ Input
namespace Graphics {
    class Point {
        int x, y;
    public:
        Point(int x, int y) : x(x), y(y) {}
        int getX() { return x; }
    };
}

// C Output
struct Graphics_Point {
    int x;
    int y;
};

void Graphics_Point_init(struct Graphics_Point* this, int x, int y) {
    this->x = x;
    this->y = y;
}

int Graphics_Point_getX(struct Graphics_Point* this) {
    return this->x;
}
```

### Estimated Effort
**Handler Implementation:**
- NamespaceHandler: 200-300 LOC, 3-4 hours
- All handler extensions: +150-200 LOC, 3-4 hours

**Testing:**
- Unit tests: 350-450 LOC, 3-4 hours
- Integration tests: 200-250 LOC, 2-3 hours
- E2E tests: 150-200 LOC, 1-2 hours

**Total:** 1050-1400 LOC, 12-17 hours (~1.5-2 days)

---

## Summary

### Total Implementation Effort

**LOC Estimates:**
- Phase 1: 2000-2700 LOC
- Phase 2: 1350-1900 LOC
- Phase 3: 950-1250 LOC
- Phase 4: 1000-1350 LOC
- Phase 5: 1300-1650 LOC
- Phase 6: 1950-2600 LOC
- Phase 7: 1250-1600 LOC
- Phase 8: 900-1150 LOC
- Phase 9: 1550-1950 LOC
- Phase 10: 2000-2600 LOC
- Phase 11: 2200-2950 LOC
- Phase 12: 1050-1400 LOC

**Total: 17,500-22,100 LOC**

**Time Estimates:**
- Phase 1: 21-29 hours (~3-4 days)
- Phase 2: 14-19 hours (~2-3 days)
- Phase 3: 10-15 hours (~1-2 days)
- Phase 4: 11-16 hours (~1.5-2 days)
- Phase 5: 15-21 hours (~2-3 days)
- Phase 6: 24-33 hours (~3-4 days)
- Phase 7: 14-19 hours (~2-3 days)
- Phase 8: 10-15 hours (~1-2 days)
- Phase 9: 19-26 hours (~2.5-3.5 days)
- Phase 10: 25-33 hours (~3-4 days)
- Phase 11: 29-38 hours (~4-5 days)
- Phase 12: 12-17 hours (~1.5-2 days)

**Total: 204-281 hours (~26-35 working days, ~5-7 weeks)**

### Complexity Progression

**Simple (Complexity 1):** Phases 1-3
- Direct C mapping, no transformations
- Establishes pipeline infrastructure
- ~4,300-5,850 LOC, ~45-63 hours

**Intermediate (Complexity 2):** Phases 4-5, 8
- Simple transformations (references → pointers, scoped enums)
- ~3,200-4,150 LOC, ~36-52 hours

**Moderate (Complexity 3):** Phases 6-7, 12
- Class/method transformations, namespaces
- ~4,250-5,600 LOC, ~50-69 hours

**Advanced (Complexity 4):** Phase 9
- Inheritance via composition
- ~1,550-1,950 LOC, ~19-26 hours

**Complex (Complexity 5):** Phases 10-11
- Templates and virtual methods
- ~4,200-5,550 LOC, ~54-71 hours

### Phase Dependencies

```
Phase 1 (Foundation)
    ├─→ Phase 2 (Control Flow)
    ├─→ Phase 3 (Global Variables)
    └─→ Phase 8 (Enums)

Phase 1 + Phase 3
    └─→ Phase 4 (Structs)
        └─→ Phase 5 (Pointers & References)
            └─→ Phase 6 (Classes)
                ├─→ Phase 7 (Method Calls)
                │   └─→ Phase 9 (Inheritance)
                │       └─→ Phase 11 (Virtual Methods)
                └─→ Phase 10 (Templates)

All Phases
    └─→ Phase 12 (Namespaces)
```

### Parallelization Opportunities

**Can parallelize:**
- Phase 2, 3, 8 (after Phase 1)
- Phase 10 and Phase 7 (after Phase 6)

**Must be sequential:**
- Phase 1 → Phase 6 → Phase 9 → Phase 11 (class transformation pipeline)
- Phase 6 → Phase 7 → Phase 9 (method transformation pipeline)

### Verification Gates

**After Phase 3:**
- Basic C functionality complete
- Can transpile procedural C++ programs
- Milestone: Simple programs work end-to-end

**After Phase 8:**
- Most direct-mapping features complete
- Can transpile C-style C++ programs
- Milestone: C compatibility verified

**After Phase 9:**
- Object-oriented features (except virtual) complete
- Can transpile class-based programs
- Milestone: OOP programs work

**After Phase 12:**
- All features complete
- Full C++ subset supported
- Milestone: Release 1.0
