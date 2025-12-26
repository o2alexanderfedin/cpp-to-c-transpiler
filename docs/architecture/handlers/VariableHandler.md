# VariableHandler Specification

## Responsibility

The VariableHandler is responsible for translating C++ variable declarations into their C equivalents. This includes global variables, local variables, function parameters, static variables, and const variables. It handles type translation, initialization expressions, and storage class specifiers.

## AST Nodes Processed

- **VarDecl**: Variable declarations (global, local, static, member variables)
- **ParmVarDecl**: Function parameter declarations
- **FieldDecl**: Handled separately by ClassToStructTranslator (not by this handler)

## Translation Strategy

### Core Mapping
C++ variables map to C variables with these transformations:
- Variable name → Same name (unless name conflicts)
- Type → Translated type (references become pointers)
- Initialization → Translated initialization expression
- Storage class → Preserved or adjusted for C

### Key Transformations
1. **References to Pointers**: `int& x` → `int* x`
2. **Bool to Int**: `bool flag` → `int flag` (or `_Bool` in C99)
3. **Const Preservation**: Keep const qualifiers
4. **Initialization Translation**: C++ initializers → C initializers
5. **Storage Classes**: static, extern preserved; thread_local not supported

## Dependencies

- **TypeTranslator**: To translate C++ types to C types
- **ExpressionHandler**: To translate initialization expressions
- **FileOriginFilter**: To determine variable placement (header vs implementation)

## Algorithm

### For VarDecl (Local/Global Variables)

#### Step 1: Validate Variable
```
if (VD->isStaticDataMember())
    return; // Handled by ClassToStructTranslator

if (VD->isConstexpr())
    // Convert to #define or const static

if (VD->getType()->isReferenceType() && !VD->hasInit())
    report_error("Uninitialized reference");
```

#### Step 2: Translate Type
```
QualType varType = VD->getType();
QualType C_type;

if (varType->isReferenceType()) {
    // References must be initialized and become pointers
    QualType pointeeType = varType.getNonReferenceType();
    C_type = context.getPointerType(pointeeType);
} else {
    C_type = TypeTranslator->translate(varType);
}
```

#### Step 3: Create C Variable Declaration
```
C_VarDecl = new VarDecl(
    C_type,
    VD->getNameAsString(),
    VD->getStorageClass()
);
```

#### Step 4: Translate Initialization
```
if (VD->hasInit()) {
    Expr* initExpr = VD->getInit();
    Expr* C_initExpr;

    if (varType->isReferenceType()) {
        // Reference initialization: get address of initializer
        if (initExpr is addressable) {
            C_initExpr = createAddressOf(
                ExpressionHandler->translateExpr(initExpr)
            );
        }
    } else {
        C_initExpr = ExpressionHandler->translateExpr(initExpr);
    }

    C_VarDecl->setInit(C_initExpr);
}
```

#### Step 5: Add to Translation Unit
```
if (VD->isFileScope() || VD->isStaticLocal()) {
    if (shouldGoInHeader(VD)) {
        C_TU->addHeaderDeclaration(C_VarDecl);
    } else {
        C_TU->addImplementationDeclaration(C_VarDecl);
    }
}
// Local variables are added to their containing function/block
```

### For ParmVarDecl (Function Parameters)

#### Step 1: Translate Parameter Type
```
QualType paramType = PVD->getType();
QualType C_type;

if (paramType->isReferenceType()) {
    C_type = context.getPointerType(paramType.getNonReferenceType());
} else {
    C_type = TypeTranslator->translate(paramType);
}
```

#### Step 2: Create C Parameter Declaration
```
C_ParmVarDecl = new ParmVarDecl(
    C_type,
    PVD->getNameAsString()
);

// Note: Parameters don't have storage class or initializers
```

## File Organization Rules

### Header File (.h)
- `extern` global variables (declarations only)
- `static const` variables with compile-time values
- `#define` for constexpr values

### Implementation File (.c)
- Global variable definitions
- Static global variables
- Local variables (in function bodies)

### Decision Logic
```
bool shouldGoInHeader(VarDecl* VD) {
    if (VD->isConstexpr())
        return true; // As #define

    if (VD->getStorageClass() == SC_Static)
        return false; // Static is internal linkage

    if (VD->getType().isConstQualified() && VD->hasInit())
        if (isCompileTimeConstant(VD->getInit()))
            return true; // Const compile-time constants

    // Extern declarations go in header, definitions in .c
    return true; // Declaration only
}
```

## Examples

### Example 1: Simple Local Variable

**C++ Input:**
```cpp
void foo() {
    int x = 42;
    x = x + 1;
}
```

**C Output:**
```c
void foo() {
    int x = 42;
    x = x + 1;
}
```

### Example 2: Reference Variable

**C++ Input:**
```cpp
void bar() {
    int x = 10;
    int& ref = x;
    ref = 20;
}
```

**C Output:**
```c
void bar() {
    int x = 10;
    int* ref = &x;
    *ref = 20;
}
```

### Example 3: Const Reference Parameter

**C++ Input:**
```cpp
void print(const int& value) {
    printf("%d\n", value);
}
```

**C Output:**
```c
void print(const int* value) {
    printf("%d\n", *value);
}
```

### Example 4: Global Variable

**C++ Input (header):**
```cpp
extern int globalCounter;
```

**C++ Input (implementation):**
```cpp
int globalCounter = 0;
```

**C Output (header):**
```c
extern int globalCounter;
```

**C Output (implementation):**
```c
int globalCounter = 0;
```

### Example 5: Static Variable

**C++ Input:**
```cpp
static int fileLocalVar = 100;

void increment() {
    static int counter = 0;
    counter++;
}
```

**C Output (implementation):**
```c
static int fileLocalVar = 100;

void increment() {
    static int counter = 0;
    counter++;
}
```

### Example 6: Const Variables

**C++ Input:**
```cpp
const int MAX_SIZE = 1024;
const char* MESSAGE = "Hello";
```

**C Output (header):**
```c
#define MAX_SIZE 1024
extern const char* MESSAGE;
```

**C Output (implementation):**
```c
const char* MESSAGE = "Hello";
```

### Example 7: Multiple Declarations

**C++ Input:**
```cpp
void process() {
    int a = 1, b = 2, c = 3;
}
```

**C Output:**
```c
void process() {
    int a = 1;
    int b = 2;
    int c = 3;
}
```

Note: Multiple declarations are split into separate VarDecls.

### Example 8: Array Variable

**C++ Input:**
```cpp
void arrays() {
    int numbers[10];
    int matrix[3][3] = {{1, 2, 3}, {4, 5, 6}, {7, 8, 9}};
}
```

**C Output:**
```c
void arrays() {
    int numbers[10];
    int matrix[3][3] = {{1, 2, 3}, {4, 5, 6}, {7, 8, 9}};
}
```

### Example 9: Pointer Variables

**C++ Input:**
```cpp
void pointers() {
    int* ptr = nullptr;
    int value = 42;
    ptr = &value;
}
```

**C Output:**
```c
void pointers() {
    int* ptr = NULL;
    int value = 42;
    ptr = &value;
}
```

## Test Cases

### Unit Tests

1. **test_simple_local_variable**
   - Input: `int x;`
   - Expected: C VarDecl with type int, name "x", no initializer

2. **test_initialized_variable**
   - Input: `int x = 42;`
   - Expected: C VarDecl with IntegerLiteral initializer

3. **test_reference_variable**
   - Input: `int x = 10; int& ref = x;`
   - Expected: C VarDecl with type `int*`, initializer is AddressOf operator

4. **test_const_variable**
   - Input: `const int x = 100;`
   - Expected: C VarDecl with const qualifier preserved

5. **test_static_variable**
   - Input: `static int x = 5;`
   - Expected: C VarDecl with SC_Static storage class

6. **test_extern_variable**
   - Input: `extern int x;`
   - Expected: C VarDecl with SC_Extern storage class

7. **test_pointer_variable**
   - Input: `int* ptr = nullptr;`
   - Expected: C VarDecl with type `int*`, initializer NULL

8. **test_array_variable**
   - Input: `int arr[10];`
   - Expected: C VarDecl with array type

9. **test_initialized_array**
   - Input: `int arr[] = {1, 2, 3};`
   - Expected: C VarDecl with InitListExpr

10. **test_parameter_declaration**
    - Input: `void foo(int x, float y);`
    - Expected: Two C ParmVarDecls

11. **test_reference_parameter**
    - Input: `void foo(int& x);`
    - Expected: C ParmVarDecl with type `int*`

12. **test_const_reference_parameter**
    - Input: `void foo(const int& x);`
    - Expected: C ParmVarDecl with type `const int*`

### Integration Tests

1. **test_variable_usage_after_declaration**
   - Input: `int x = 5; x = x + 1;`
   - Expected: Variable declaration followed by assignment

2. **test_reference_modifications**
   - Input: `int x = 10; int& ref = x; ref = 20;`
   - Expected: Pointer declaration with address-of, dereference in assignment

3. **test_global_and_local_same_name**
   - Input: Global `int x` and local `int x` in function
   - Expected: Both translated, local shadows global

4. **test_static_local_persistence**
   - Input: Static local variable in function
   - Expected: C static variable maintains state

### Edge Cases

1. **test_uninitialized_const**
   - Input: `const int x;`
   - Expected: Warning or error (undefined behavior in C++)

2. **test_uninitialized_reference**
   - Input: `int& ref;`
   - Expected: Error (references must be initialized)

3. **test_array_of_pointers**
   - Input: `int* arr[10];`
   - Expected: Array type correctly preserved

4. **test_pointer_to_array**
   - Input: `int (*ptr)[10];`
   - Expected: Pointer-to-array type preserved

5. **test_multidimensional_array**
   - Input: `int matrix[3][4][5];`
   - Expected: Multidimensional array type preserved

6. **test_volatile_variable**
   - Input: `volatile int flag = 0;`
   - Expected: Volatile qualifier preserved

7. **test_const_pointer_vs_pointer_to_const**
   - Input: `int* const ptr1 = ...; const int* ptr2 = ...;`
   - Expected: Const placement preserved correctly

### Error Cases

1. **test_constexpr_complex_expression**
   - Input: `constexpr int x = someComplexFunction();`
   - Expected: Error or fallback to const (constexpr requires compile-time)

2. **test_thread_local_not_supported**
   - Input: `thread_local int x;`
   - Expected: Error or warning about unsupported feature

3. **test_auto_keyword**
   - Input: `auto x = 42;`
   - Expected: Type deduced by Clang, translated to concrete type

## Implementation Notes

### Reference Initialization

When translating reference variables:
```cpp
// C++: int& ref = x;
// C: int* ref = &x;

Expr* C_init;
if (original type is reference) {
    if (initializer is already an lvalue) {
        C_init = UnaryOperator::CreateAddressOf(
            ExpressionHandler->translateExpr(init)
        );
    } else {
        // Error: cannot take address of rvalue
    }
}
```

### Reference Usage

When a reference variable is used in expressions:
```cpp
// C++: ref = 10;
// C: *ref = 10;

// This is handled by ExpressionHandler, not VariableHandler
// When translating DeclRefExpr to a reference variable,
// ExpressionHandler adds dereference operator
```

### Storage Class Translation

```cpp
StorageClass translateStorageClass(StorageClass SC) {
    switch (SC) {
        case SC_None: return SC_None;
        case SC_Extern: return SC_Extern;
        case SC_Static: return SC_Static;
        case SC_Auto: return SC_None; // Auto is default in C
        case SC_Register: return SC_Register;
        default: return SC_None;
    }
}
```

### Constexpr Handling

```cpp
if (VD->isConstexpr()) {
    if (isCompileTimeConstant(VD->getInit())) {
        // Generate #define instead
        generateMacro(VD->getName(), evaluateConstant(VD->getInit()));
    } else {
        // Fallback to const static
        VD->setConstexpr(false);
        VD->addConst();
    }
}
```

### Array Initialization

C++ allows omitting array size with initializer:
```cpp
// C++: int arr[] = {1, 2, 3};
// C: int arr[3] = {1, 2, 3}; // Size can be explicit or implicit

// Clang fills in the array size, so we can just use VD->getType()
```

### Nullptr Translation

```cpp
// C++: int* ptr = nullptr;
// C: int* ptr = NULL;

// Handled by ExpressionHandler when translating CXXNullPtrLiteralExpr
```

## Special Considerations

### Global Variable Initialization Order

C++ guarantees initialization order within a translation unit. C has similar rules, but:
- Static variables initialized to zero by default
- Dynamic initialization happens at runtime
- Order within TU is guaranteed, across TUs is not

### Static Local Variables

```cpp
void foo() {
    static int counter = 0; // Initialized once
    counter++;
}
```

In C, this works the same way - static locals are initialized once.

### Const Global Variables

In C++, const global variables have internal linkage by default.
In C, they have external linkage.

```cpp
// C++: const int x = 10; // Internal linkage
// C: const int x = 10; // External linkage!

// To match C++ behavior, add static:
// C: static const int x = 10;
```

Decision: Add `static` to const global variables unless explicitly `extern`.

## Future Enhancements

### Phase 2: User-Defined Types
- Handle struct/class member variables (FieldDecl)
- Translate member variable initialization

### Phase 3: Advanced Initialization
- Aggregate initialization
- Designated initializers (C99 feature, also in C++20)
- List initialization

### Phase 4: Thread-Local Storage
- If needed, use C11 `_Thread_local` or platform-specific extensions
- Thread-local variables are complex and may require runtime support

### Phase 5: Inline Variables (C++17)
- C++17 allows inline variables
- Translate to static inline or use header guards

## Related Handlers

- **FunctionHandler**: Functions contain local variable declarations
- **ExpressionHandler**: Translates initialization expressions and variable uses
- **StatementHandler**: Handles DeclStmt which contains VarDecls
- **TypeTranslator**: Translates all variable types
- **ClassToStructTranslator**: Handles member variables (FieldDecl)
