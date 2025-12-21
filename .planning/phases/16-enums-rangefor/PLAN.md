# Phase 16 Plan: Enums & Range-For Loops (v2.9.0)

**Phase**: 16 of 17
**Roadmap**: `../../ROADMAP.md`
**Brief**: `../../BRIEF.md`
**Target Version**: v2.9.0
**Status**: PENDING
**Priority**: HIGH-VALUE (Tier 2 - Core language features)
**Prerequisite**: Phase 14 (Operator Overloading recommended for iterator protocol)

## Phase Goal

Implement enum translation for scoped and unscoped enums, and expand range-based for loop translation from basic nesting tracking to full iterator protocol expansion with proper container and array iteration support.

## Business Value

Enums and range-for loops are fundamental C++ language features:
- Enums provide type-safe enumeration and namespace scoping (scoped enums)
- Range-for loops simplify iteration over arrays and containers
- Critical for modern C++ codebases using containers and ranged iteration
- Proper scoping prevents enum name collisions in C translation

**Impact**: Without enum and range-for support, transpiled C++ cannot execute programs using modern iteration patterns or scoped enumerations—common in professional C++ codebases.

## Deliverables

### Source Code
- [ ] Implement `CppToCVisitor::VisitEnumDecl(EnumDecl *D)` visitor method
- [ ] Implement enum value translation (scoped and unscoped)
- [ ] Expand `CppToCVisitor::VisitCXXForRangeStmt(CXXForRangeStmt *S)` (currently only tracks nesting)
- [ ] Iterator protocol expansion (begin(), end(), operator++, operator*)
- [ ] Enum underlying type handling (C++11 feature)
- [ ] Array vs. container iteration detection

### Tests
- [ ] `tests/EnumRangeForIntegrationTest.cpp` (12+ tests)
  - Unscoped enum declaration and value access
  - Scoped enum (enum class) declaration and namespaced access
  - Enum with underlying type (int8_t, uint32_t, etc.)
  - Enum value casting and compatibility
  - Range-for on C array (int arr[10])
  - Range-for on std::vector<T>
  - Range-for on std::map<K, V>
  - Range-for with auto type deduction
  - Range-for with const auto& reference
  - Range-for nested loops (loops within loops)
  - Range-for with break/continue flow control
  - Enum + range-for integration (iterating enum-like containers)

### CLI Integration
- [ ] Add `--enum-translation={off,on}` flag (default: on)
- [ ] Add `--range-for-expansion={off,on}` flag (default: on)

### Documentation
- [ ] Update `docs/CHANGELOG.md` for v2.9.0
- [ ] Update `README.md` with enum and range-for features
- [ ] Update `website/src/pages/features.astro`
- [ ] Create `docs/examples/enum-range-for.md` with C++ → C translation examples
- [ ] Document scoped enum name mangling strategy

### Release
- [ ] Git-flow release v2.9.0
- [ ] Tag on GitHub with release notes

## Technical Design

### Architecture Overview

Enum and range-for translation uses a two-part strategy:

```
┌─────────────────────────────────────────────────────────────────┐
│ Enum & Range-For Translation Architecture                       │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  Part 1: Enum Translation                                      │
│  ═════════════════════════════════════════════════════════     │
│  EnumDecl (C++) → C enum declaration                           │
│     ↓                                                           │
│  [Determine scoped vs. unscoped]                              │
│     ↓                                                           │
│  [Get underlying type]                                         │
│     ↓                                                           │
│  [Generate enum values with prefix (scoped) or direct]        │
│     ↓                                                           │
│  C enum (unscoped) or prefixed C enum (scoped)               │
│                                                                 │
│  Part 2: Range-For Translation                                │
│  ═════════════════════════════════════════════════════════     │
│  CXXForRangeStmt (C++) → Traditional for loop with iterators  │
│     ↓                                                           │
│  [Determine container type (array vs. container)]             │
│     ↓                                                           │
│  [Call begin()/end() or use direct array indexing]            │
│     ↓                                                           │
│  [Expand operator++ and operator*]                            │
│     ↓                                                           │
│  Traditional for loop: for (init; cond; incr)                 │
│                                                                 │
└─────────────────────────────────────────────────────────────────┘
```

### Part 1: Enum Translation

#### Unscoped Enums

**C++**:
```cpp
enum Color {
  RED = 0,
  GREEN = 1,
  BLUE = 2
};

Color c = RED;
int value = GREEN;
```

**C** (Generated):
```c
enum Color {
  RED = 0,
  GREEN = 1,
  BLUE = 2
};

enum Color c = RED;
int value = GREEN;
```

**Translation Steps**:
1. Detect enum is unscoped (not enum class)
2. Generate C enum directly with same name
3. Values are directly accessible without prefix
4. Implicit conversion to underlying type (int by default)

#### Scoped Enums (enum class)

**C++**:
```cpp
enum class Status : unsigned char {
  IDLE = 0,
  RUNNING = 1,
  STOPPED = 2
};

Status s = Status::IDLE;
unsigned char val = static_cast<unsigned char>(Status::RUNNING);
```

**C** (Generated):
```c
// Underlying type: unsigned char
enum Status_enum {
  Status_IDLE = 0,
  Status_RUNNING = 1,
  Status_STOPPED = 2
};
typedef unsigned char Status;  // Alias for underlying type

// Access with prefix
enum Status_enum s = Status_IDLE;
unsigned char val = Status_RUNNING;
```

**Translation Steps**:
1. Detect enum is scoped (enum class)
2. Generate C enum with prefixed names: `EnumName_VALUE`
3. Create typedef for underlying type
4. Use qualified access `Status_IDLE` instead of `Status::IDLE`
5. Handle implicit casting to underlying type

#### Enum with Underlying Type

**C++**:
```cpp
enum class Priority : int8_t {
  LOW = -1,
  NORMAL = 0,
  HIGH = 1
};
```

**C** (Generated):
```c
#include <stdint.h>

enum Priority_enum {
  Priority_LOW = -1,
  Priority_NORMAL = 0,
  Priority_HIGH = 1
};
typedef int8_t Priority;
```

**Translation Steps**:
1. Extract underlying type from C++11 `enum class Type : UnderlyingType`
2. Include necessary header for type (stdint.h for fixed-size types)
3. Use typedef to match C++ semantics

### Part 2: Range-For Translation

#### Range-For on C Array

**C++**:
```cpp
void process_array() {
  int arr[5] = {1, 2, 3, 4, 5};
  for (int x : arr) {
    printf("%d\n", x);
  }
}
```

**C** (Generated):
```c
void process_array() {
  int arr[5] = {1, 2, 3, 4, 5};

  // Traditional for loop with array indexing
  for (int i = 0; i < 5; i++) {
    int x = arr[i];
    printf("%d\n", x);
  }
}
```

**Translation Steps**:
1. Detect container is C array (from type: `int arr[5]`)
2. Generate array size constant or use `sizeof(arr) / sizeof(arr[0])`
3. Create loop counter variable (auto-generated name)
4. Generate traditional for loop: `for (int i = 0; i < size; i++)`
5. Access array element: `int x = arr[i]`

#### Range-For on std::vector

**C++**:
```cpp
void process_vector() {
  std::vector<std::string> items = {"a", "b", "c"};
  for (const auto& item : items) {
    printf("%s\n", item.c_str());
  }
}
```

**C** (Generated):
```c
void process_vector() {
  struct std_vector__std_string items;
  std_vector__std_string__ctor(&items);
  // ... push items a, b, c ...

  // Iterator-based loop
  struct std_vector__std_string__iterator __iter_begin = std_vector__std_string__begin(&items);
  struct std_vector__std_string__iterator __iter_end = std_vector__std_string__end(&items);

  for (; !std_vector__std_string__iterator__eq(&__iter_begin, &__iter_end);
       std_vector__std_string__iterator__inc(&__iter_begin)) {
    const struct std_string *item = std_vector__std_string__iterator__deref(&__iter_begin);
    printf("%s\n", std_string__c_str((struct std_string*)item));
  }

  std_vector__std_string__dtor(&items);
}
```

**Translation Steps**:
1. Detect container is std::vector<T>
2. Generate iterator initialization: `begin()` and `end()`
3. Create loop condition: iterate until end iterator reached
4. Use operator++ to advance iterator
5. Use operator* to dereference value
6. Handle reference vs. copy semantics (const auto& vs. auto)

#### Range-For on std::map

**C++**:
```cpp
void process_map() {
  std::map<std::string, int> counts;
  // ... populate counts ...

  for (const auto& [key, val] : counts) {
    printf("%s: %d\n", key.c_str(), val);
  }
}
```

**C** (Generated):
```c
void process_map() {
  struct std_map__std_string__int counts;
  std_map__std_string__int__ctor(&counts);
  // ... populate counts ...

  // Iterator-based loop
  struct std_map__std_string__int__iterator __iter_begin = std_map__std_string__int__begin(&counts);
  struct std_map__std_string__int__iterator __iter_end = std_map__std_string__int__end(&counts);

  for (; !std_map__std_string__int__iterator__eq(&__iter_begin, &__iter_end);
       std_map__std_string__int__iterator__inc(&__iter_begin)) {
    // Pair deref: first = key, second = value
    const struct std_pair__std_string__int *__pair =
      (struct std_pair__std_string__int*)std_map__std_string__int__iterator__deref(&__iter_begin);
    const struct std_string *key = &__pair->first;
    const int *val = &__pair->second;

    printf("%s: %d\n", std_string__c_str((struct std_string*)key), *val);
  }

  std_map__std_string__int__dtor(&counts);
}
```

**Translation Steps**:
1. Detect container is std::map<K, V>
2. Generate iterator: `begin()` and `end()`
3. Create loop structure similar to vector
4. Handle pair destructuring: `[key, val] → pair.first, pair.second`
5. Dereference iterators to get pair structure

#### Range-For with Auto Type Deduction

**C++**:
```cpp
void with_auto() {
  std::vector<double> values = {1.1, 2.2, 3.3};
  for (auto x : values) {
    printf("%f\n", x);
  }
}
```

**C** (Generated):
```c
void with_auto() {
  struct std_vector__double values;
  std_vector__double__ctor(&values);
  // ... push items ...

  // Type deduction: auto x → double x
  struct std_vector__double__iterator __iter = std_vector__double__begin(&values);
  struct std_vector__double__iterator __iter_end = std_vector__double__end(&values);

  for (; !std_vector__double__iterator__eq(&__iter, &__iter_end);
       std_vector__double__iterator__inc(&__iter)) {
    double x = *std_vector__double__iterator__deref(&__iter);
    printf("%f\n", x);
  }

  std_vector__double__dtor(&values);
}
```

**Translation Steps**:
1. Analyze container element type
2. Deduce loop variable type from container (std::vector<double> → double)
3. Generate loop variable with deduced type
4. Rest is same as iterator expansion

#### Range-For Nested Loops

**C++**:
```cpp
void nested_loops() {
  std::vector<std::vector<int>> matrix = {{1, 2}, {3, 4}};

  for (const auto& row : matrix) {
    for (int val : row) {
      printf("%d ", val);
    }
    printf("\n");
  }
}
```

**C** (Generated):
```c
void nested_loops() {
  struct std_vector__std_vector__int matrix;
  // ... init and populate ...

  // Outer loop
  struct std_vector__std_vector__int__iterator __iter_outer =
    std_vector__std_vector__int__begin(&matrix);
  struct std_vector__std_vector__int__iterator __iter_outer_end =
    std_vector__std_vector__int__end(&matrix);

  for (; !std_vector__std_vector__int__iterator__eq(&__iter_outer, &__iter_outer_end);
       std_vector__std_vector__int__iterator__inc(&__iter_outer)) {
    const struct std_vector__int *row =
      (struct std_vector__int*)std_vector__std_vector__int__iterator__deref(&__iter_outer);

    // Inner loop (unique iterator names)
    struct std_vector__int__iterator __iter_inner = std_vector__int__begin((struct std_vector__int*)row);
    struct std_vector__int__iterator __iter_inner_end = std_vector__int__end((struct std_vector__int*)row);

    for (; !std_vector__int__iterator__eq(&__iter_inner, &__iter_inner_end);
         std_vector__int__iterator__inc(&__iter_inner)) {
      int val = *std_vector__int__iterator__deref(&__iter_inner);
      printf("%d ", val);
    }
    printf("\n");
  }

  std_vector__std_vector__int__dtor(&matrix);
}
```

**Translation Steps**:
1. Generate unique iterator variable names for each nesting level
2. Use depth counter: `__iter_level0`, `__iter_level1`, etc.
3. Properly scope and initialize inner loop iterators
4. Maintain separate deref/inc calls per level

#### Range-For with Break/Continue

**C++**:
```cpp
void with_control_flow() {
  std::vector<int> nums = {1, 2, 3, 4, 5};

  for (int x : nums) {
    if (x == 3) continue;
    if (x == 5) break;
    printf("%d\n", x);
  }
}
```

**C** (Generated):
```c
void with_control_flow() {
  struct std_vector__int nums;
  std_vector__int__ctor(&nums);
  // ... push items ...

  struct std_vector__int__iterator __iter = std_vector__int__begin(&nums);
  struct std_vector__int__iterator __iter_end = std_vector__int__end(&nums);

  for (; !std_vector__int__iterator__eq(&__iter, &__iter_end);
       std_vector__int__iterator__inc(&__iter)) {
    int x = *std_vector__int__iterator__deref(&__iter);

    if (x == 3) continue;  // Works directly: advances to next iteration
    if (x == 5) break;     // Works directly: exits loop
    printf("%d\n", x);
  }

  std_vector__int__dtor(&nums);
}
```

**Translation Steps**:
1. Break/continue work naturally with traditional for loops
2. No special handling needed (C semantics match C++)
3. Ensure proper cleanup on break (destructors if needed)

### Part 3: Enum + Range-For Integration

**C++**:
```cpp
enum class LogLevel : unsigned char {
  DEBUG = 0,
  INFO = 1,
  WARNING = 2,
  ERROR = 3
};

void process_logs(const std::vector<LogLevel>& levels) {
  for (auto level : levels) {
    switch(level) {
      case LogLevel::DEBUG:
        printf("DEBUG\n");
        break;
      case LogLevel::INFO:
        printf("INFO\n");
        break;
      default:
        printf("OTHER\n");
    }
  }
}
```

**C** (Generated):
```c
enum LogLevel_enum {
  LogLevel_DEBUG = 0,
  LogLevel_INFO = 1,
  LogLevel_WARNING = 2,
  LogLevel_ERROR = 3
};
typedef unsigned char LogLevel;

void process_logs(const struct std_vector__unsigned_char *levels) {
  struct std_vector__unsigned_char__iterator __iter = std_vector__unsigned_char__begin((struct std_vector__unsigned_char*)levels);
  struct std_vector__unsigned_char__iterator __iter_end = std_vector__unsigned_char__end((struct std_vector__unsigned_char*)levels);

  for (; !std_vector__unsigned_char__iterator__eq(&__iter, &__iter_end);
       std_vector__unsigned_char__iterator__inc(&__iter)) {
    unsigned char level = *std_vector__unsigned_char__iterator__deref(&__iter);

    switch(level) {
      case LogLevel_DEBUG:
        printf("DEBUG\n");
        break;
      case LogLevel_INFO:
        printf("INFO\n");
        break;
      default:
        printf("OTHER\n");
    }
  }

  std_vector__unsigned_char__dtor((struct std_vector__unsigned_char*)levels);
}
```

**Translation Steps**:
1. Translate enum to prefixed C enum (enum class → LogLevel_DEBUG, etc.)
2. Translate vector range-for to iterator loop
3. Use enum values in switch statements naturally
4. Type system ensures consistency (LogLevel typedef)

### Visitor Method Implementation Strategy

#### VisitEnumDecl Implementation

```cpp
bool CppToCVisitor::VisitEnumDecl(EnumDecl *D) {
  std::string enumCode;

  // 1. Determine if scoped (enum class) or unscoped (enum)
  bool isScoped = D->isScoped();
  std::string enumName = D->getNameAsString();

  // 2. Get underlying type (C++11 feature)
  QualType underlyingType = D->getIntegerType();
  std::string underlyingTypeStr = underlyingType.getAsString();

  // 3. Generate enum declaration
  if (isScoped) {
    // Scoped enum: create enum with prefixed values
    enumCode += "enum " + enumName + "_enum {\n";

    for (auto enumerator : D->enumerators()) {
      std::string enumValue = enumName + "_" + enumerator->getNameAsString();
      enumCode += "  " + enumValue + " = " +
                  enumerator->getInitVal().toString(10) + ",\n";
    }

    enumCode += "};\n";

    // Add typedef for underlying type
    enumCode += "typedef " + underlyingTypeStr + " " + enumName + ";\n";
  } else {
    // Unscoped enum: create C enum directly
    enumCode += "enum " + enumName + " {\n";

    for (auto enumerator : D->enumerators()) {
      enumCode += "  " + enumerator->getNameAsString() + " = " +
                  enumerator->getInitVal().toString(10) + ",\n";
    }

    enumCode += "};\n";
  }

  // 4. Store in output
  currentGlobalCode += enumCode;

  return true;  // We've handled this declaration
}
```

#### VisitCXXForRangeStmt Expansion

```cpp
bool CppToCVisitor::VisitCXXForRangeStmt(CXXForRangeStmt *S) {
  std::string loopCode;

  // 1. Get range expression (container or array)
  Expr *rangeExpr = S->getRangeInit();
  QualType rangeType = rangeExpr->getType();

  // 2. Determine container type
  bool isArray = rangeType->isArrayType();
  bool isVector = isStdVector(rangeType);
  bool isMap = isStdMap(rangeType);

  // 3. Generate iterator initialization
  std::string iterName = "__iter_" + std::to_string(forRangeCounter++);
  std::string iterEndName = "__iter_end_" + std::to_string(forRangeCounter);

  if (isArray) {
    // Array: use direct indexing
    loopCode += generateArrayLoop(S, iterName, rangeExpr, rangeType);
  } else if (isVector) {
    // Vector: use begin/end iterators
    loopCode += generateVectorLoop(S, iterName, iterEndName, rangeExpr, rangeType);
  } else if (isMap) {
    // Map: use begin/end iterators with pair handling
    loopCode += generateMapLoop(S, iterName, iterEndName, rangeExpr, rangeType);
  }

  // 4. Store in output
  currentFunctionCode += loopCode;

  return true;  // Prevent default traversal
}

// Helper: Generate array-based loop
std::string generateArrayLoop(CXXForRangeStmt *S, const std::string& idxVar,
                              Expr *rangeExpr, QualType rangeType) {
  std::string code;

  // Get array size
  const ArrayType *arrType = rangeType->getAsArrayTypeUnsafe();
  size_t arraySize = getArraySize(arrType);

  // Get element type
  QualType elemType = arrType->getElementType();

  // Generate loop
  code += "for (int " + idxVar + " = 0; " + idxVar + " < " +
          std::to_string(arraySize) + "; " + idxVar + "++) {\n";

  // Variable declaration and assignment
  std::string varName = S->getLoopVariable()->getNameAsString();
  code += "  " + elemType.getAsString() + " " + varName + " = " +
          rangeExpr->getSourceRange().getAsString() + "[" + idxVar + "];\n";

  // Body
  code += getStatementCode(S->getBody());
  code += "}\n";

  return code;
}

// Helper: Generate vector-based iterator loop
std::string generateVectorLoop(CXXForRangeStmt *S, const std::string& iterName,
                               const std::string& iterEndName, Expr *rangeExpr,
                               QualType rangeType) {
  std::string code;

  // Extract element type from std::vector<T>
  QualType elemType = getVectorElementType(rangeType);

  // Generate begin/end initialization
  code += getIteratorInitCode(iterName, iterEndName, rangeExpr, "vector");

  // Generate for loop
  code += "for (; !" + getIteratorEqCode(iterName, iterEndName, "vector") + "; " +
          getIteratorIncCode(iterName, "vector") + ") {\n";

  // Variable declaration and dereference
  std::string varName = S->getLoopVariable()->getNameAsString();
  code += "  " + elemType.getAsString() + " " + varName + " = " +
          getIteratorDerefCode(iterName, elemType, "vector") + ";\n";

  // Body
  code += getStatementCode(S->getBody());
  code += "}\n";

  return code;
}
```

### Key Challenges & Solutions

#### Challenge 1: Scoped Enum Name Scoping in C

**Problem**: C doesn't have enum class (scoped enums). Enum values are always global.

**Solution**:
- Generate prefixed enum values: `EnumName_VALUE`
- Store underlying type in typedef
- Transform references `Status::IDLE` → `Status_IDLE`
- Ensure no namespace pollution

#### Challenge 2: Underlying Type Handling (C++11)

**Problem**: C++11 allows `enum class Type : int8_t`, but C enums don't have explicit underlying types.

**Solution**:
- Extract underlying type from AST
- Verify it's available (include stdint.h if needed)
- Generate typedef for compatibility
- Cast values if necessary to match underlying type

#### Challenge 3: Array vs. Container Differentiation

**Problem**: Range-for works on both arrays and containers, with different semantics.

**Solution**:
- Detect array type: `isArrayType()` on QualType
- Detect std::vector/map: match against standard library types
- Use direct indexing for arrays
- Use begin/end iterators for containers

#### Challenge 4: Iterator Protocol Expansion

**Problem**: C doesn't have operators. Must expand operator calls manually.

**Solution**:
- Generate `begin()` and `end()` calls as function calls
- Expand `operator++` as function call: `iterator__inc()`
- Expand `operator*` as function call: `iterator__deref()`
- Expand `operator==` as function call: `iterator__eq()`

#### Challenge 5: Type Deduction with Auto

**Problem**: `auto x : container` requires type deduction from container element type.

**Solution**:
- Analyze container template parameters (std::vector<T>)
- Extract T as the loop variable type
- Generate declaration with concrete type
- Handle reference semantics (const auto& → const T*)

#### Challenge 6: Pair Destructuring in Map Iteration

**Problem**: `for (const auto& [key, val] : map)` requires unpacking pair structure.

**Solution**:
- Detect structured binding pattern
- Generate pair dereference code
- Access pair.first and pair.second
- Create aliases/variables for key and val

### Integration Points

1. **CppToCVisitor**: Add `VisitEnumDecl` and expand `VisitCXXForRangeStmt` visitor methods
2. **Type Analysis**: Integrate container type detection (vector, map, array)
3. **Iterator Protocol**: Call begin/end and expand operator overloads
4. **Code Generation**: Generate proper C loop and iterator advancement
5. **Cleanup**: Ensure proper destructor calls on loop exit (especially break)

### Test Plan (12+ Tests)

#### Basic Enum (3 tests)
1. **UnscopedEnumDeclaration**: Declare and access unscoped enum values
2. **ScopedEnumDeclaration**: Declare enum class with prefixed names
3. **EnumWithUnderlyingType**: Enum with explicit underlying type (int8_t, uint32_t)

#### Enum Values & Casting (2 tests)
4. **EnumValueAccess**: Access enum values in expressions
5. **EnumCasting**: Explicit and implicit casting between enum and underlying type

#### Range-For on Arrays (2 tests)
6. **RangeForSimpleArray**: Iterate C array with range-for
7. **RangeForMultidimensionalArray**: Range-for on 2D array (matrix)

#### Range-For on Containers (3 tests)
8. **RangeForVector**: Iterate std::vector with range-for
9. **RangeForMap**: Iterate std::map with structured binding
10. **RangeForWithAutoDeduction**: Use auto for type deduction

#### Advanced Range-For (2 tests)
11. **RangeForNestedLoops**: Nested range-for with unique iterator names
12. **RangeForWithBreakContinue**: Break and continue in range-for body

### Verification Criteria

- [ ] **Functional**: All 12+ tests passing (100%)
- [ ] **Scoped Enums**: No namespace pollution from prefixed names
- [ ] **Underlying Types**: Correct type deduced and applied
- [ ] **Array Iteration**: Direct indexing used for arrays
- [ ] **Container Iteration**: begin/end iterators used for containers
- [ ] **Iterator Expansion**: Operator calls properly expanded to function calls
- [ ] **Type Safety**: Type deduction (auto) works correctly
- [ ] **Linting**: Zero linting errors (clang-tidy, cppcheck)
- [ ] **Code Review**: Separate review by another agent

## Key Features

1. **Scoped Enum Translation**: Enum class → prefixed C enum with typedef
2. **Unscoped Enum Translation**: Enum → direct C enum (no prefix)
3. **Underlying Type Support**: C++11 `enum class Type : IntType` → C typedef
4. **Array Iteration**: Direct indexing for C arrays in range-for
5. **Container Iteration**: begin/end iterator protocol for std::vector, std::map
6. **Iterator Protocol Expansion**: operator++, operator*, operator== → function calls
7. **Type Deduction**: Auto type deduction from container element type
8. **Nested Range-For**: Multiple levels of iteration with unique iterator names
9. **Structured Binding**: Pair destructuring in map iteration
10. **Control Flow**: Break/continue work naturally in expanded loops

## Dependencies

- **Synergy with Phase 14** (Operator Overloading): Iterator protocol relies on operator expansion
- **No hard dependencies**: Can run parallel with other phases
- **Infrastructure present**: Iterator protocol already partially implemented in Phase 14

## Implementation Milestones

### Milestone 1: Enum Translation Scaffolding (20% effort)
- [ ] Add `VisitEnumDecl` method stub to CppToCVisitor
- [ ] Implement unscoped enum translation
- [ ] Implement scoped enum translation with prefixed names
- [ ] Handle underlying type extraction
- [ ] Verify project builds without errors
- [ ] Basic enum tests passing (2/3)

### Milestone 2: Range-For Array Translation (25% effort)
- [ ] Expand `VisitCXXForRangeStmt` for array detection
- [ ] Implement direct indexing loop generation
- [ ] Handle array size calculation
- [ ] Generate proper loop variable declaration
- [ ] Array iteration tests passing (2/2)

### Milestone 3: Range-For Container Translation (30% effort)
- [ ] Implement vector iterator protocol expansion
- [ ] Implement map iterator protocol with pair handling
- [ ] Implement type deduction (auto) for loop variables
- [ ] Handle structured binding for map iteration
- [ ] Container iteration tests passing (5/5)

### Milestone 4: Advanced Features & Integration (15% effort)
- [ ] Nested range-for with unique iterator names
- [ ] Break/continue flow control integration
- [ ] Enum + range-for integration testing
- [ ] Reference semantics (const auto&)
- [ ] All advanced tests passing (2/2)
- [ ] Code review and linting

### Milestone 5: Optimization & Documentation (10% effort)
- [ ] Performance optimization (iterator caching)
- [ ] Documentation and examples
- [ ] CLI integration (flags for enum/range-for)
- [ ] CHANGELOG and README updates
- [ ] Git-flow release v2.9.0

## Success Criteria Summary

| Criteria | Target | Status |
|----------|--------|--------|
| Tests Passing | 12+/12 (100%) | ⏳ PENDING |
| Scoped Enums | No namespace pollution | ⏳ PENDING |
| Underlying Types | Correct type application | ⏳ PENDING |
| Array Iteration | Direct indexing used | ⏳ PENDING |
| Container Iteration | Iterator protocol expanded | ⏳ PENDING |
| Type Deduction | Auto works correctly | ⏳ PENDING |
| Linting Errors | 0 errors/warnings | ⏳ PENDING |
| Code Review | Approved by separate review | ⏳ PENDING |

## Next Steps

1. **Setup**: Verify Phase 14 iterator infrastructure exists
2. **Implement**: Follow milestones for enum and range-for translation
3. **Test**: Run test suite after each milestone
4. **Document**: Write examples and update documentation
5. **Review**: Code review for quality assurance
6. **Release**: Execute git-flow release v2.9.0
