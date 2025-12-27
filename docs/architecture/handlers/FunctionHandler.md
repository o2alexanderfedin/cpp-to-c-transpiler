# FunctionHandler Specification

## Responsibility

The FunctionHandler is responsible for translating C++ function declarations and definitions into their C equivalents. It handles plain functions (not methods) and manages the translation of function signatures, parameter lists, return types, and function bodies.

## AST Nodes Processed

- **FunctionDecl**: C++ function declarations and definitions
  - Includes free functions
  - Excludes methods (handled by MethodToFunctionTranslator)
  - Excludes constructors/destructors (handled by specialized handlers)

## Translation Strategy

### Core Mapping
C++ functions map directly to C functions with the same signature structure:
- Function name → Same name (with potential prefix for namespaces in later phases)
- Return type → Translated return type (handle C++ specific types)
- Parameters → Translated parameter list
- Function body → Translated statements

### Key Transformations
1. **References to Pointers**: C++ reference parameters become C pointers
2. **Type Translation**: C++ types (bool, string, etc.) map to C types (int, char*, etc.)
3. **Default Parameters**: NOT SUPPORTED - must be handled at call site or rejected
4. **Inline Functions**: Translate to `static inline` in C
5. **Const Qualifiers**: Preserve const correctness

## Dependencies

- **TypeTranslator**: To translate C++ types to C types
- **ExpressionHandler**: To translate expressions in function body
- **StatementHandler**: To translate statements in function body
- **FileOriginFilter**: To determine if function belongs to current file

## Algorithm

### Step 1: Validate Function
```
if (FD->isDeleted() || FD->isDefaulted())
    return; // Skip compiler-generated functions

if (FD->isCXXClassMember())
    return; // Handled by MethodToFunctionTranslator

if (hasDefaultParameters(FD))
    report_error("Default parameters not supported");
```

### Step 2: Create C Function Declaration
```
C_FunctionDecl = new FunctionDecl();
C_FunctionDecl->setName(FD->getNameAsString());
C_FunctionDecl->setReturnType(translateType(FD->getReturnType()));

// Handle inline
if (FD->isInlineSpecified())
    C_FunctionDecl->setStorageClass(SC_Static);
    C_FunctionDecl->setInlineSpecified(true);
```

### Step 3: Translate Parameters
```
for (ParmVarDecl* param : FD->parameters()) {
    QualType paramType = param->getType();

    // Convert references to pointers
    if (paramType->isReferenceType()) {
        paramType = context.getPointerType(paramType.getNonReferenceType());
    }

    C_ParmVarDecl = new ParmVarDecl(
        translateType(paramType),
        param->getNameAsString()
    );

    C_FunctionDecl->addParameter(C_ParmVarDecl);
}
```

### Step 4: Translate Function Body (if definition)
```
if (FD->hasBody()) {
    Stmt* body = FD->getBody();
    Stmt* C_body = StatementHandler->translateStmt(body);
    C_FunctionDecl->setBody(C_body);
}
```

### Step 5: Add to Translation Unit
```
if (shouldGenerateDeclaration(FD)) {
    C_TU->addHeaderDeclaration(C_FunctionDecl->clone(DeclOnly));
}

if (shouldGenerateDefinition(FD)) {
    C_TU->addImplementationDeclaration(C_FunctionDecl);
}
```

## File Organization Rules

### Header File (.h)
- Function declarations (prototypes)
- Inline function definitions (must be in header)
- Static functions: NO (local to translation unit)

### Implementation File (.c)
- Function definitions
- Static function declarations and definitions

### Decision Logic
```
bool shouldGenerateDeclaration(FunctionDecl* FD) {
    if (FD->getStorageClass() == SC_Static)
        return false; // Static functions don't go in header

    if (FD->isInlineSpecified() && FD->hasBody())
        return true; // Inline definitions go in header

    return true; // All other functions need declaration
}

bool shouldGenerateDefinition(FunctionDecl* FD) {
    if (!FD->hasBody())
        return false; // No body to generate

    if (FD->isInlineSpecified())
        return false; // Already in header

    return true;
}
```

## Examples

### Example 1: Simple Function

**C++ Input:**
```cpp
int add(int a, int b) {
    return a + b;
}
```

**C Output (header):**
```c
int add(int a, int b);
```

**C Output (implementation):**
```c
int add(int a, int b) {
    return a + b;
}
```

### Example 2: Function with Reference Parameters

**C++ Input:**
```cpp
void swap(int& a, int& b) {
    int temp = a;
    a = b;
    b = temp;
}
```

**C Output (header):**
```c
void swap(int* a, int* b);
```

**C Output (implementation):**
```c
void swap(int* a, int* b) {
    int temp = *a;
    *a = *b;
    *b = temp;
}
```

### Example 3: Inline Function

**C++ Input:**
```cpp
inline int max(int a, int b) {
    return (a > b) ? a : b;
}
```

**C Output (header):**
```c
static inline int max(int a, int b) {
    return (a > b) ? a : b;
}
```

**C Output (implementation):**
```c
// Nothing - inline functions are in header only
```

### Example 4: Static Function

**C++ Input:**
```cpp
static int helper(int x) {
    return x * 2;
}
```

**C Output (header):**
```c
// Nothing - static functions are not exported
```

**C Output (implementation):**
```c
static int helper(int x) {
    return x * 2;
}
```

### Example 5: Function with Const Parameters

**C++ Input:**
```cpp
int strlen_custom(const char* str) {
    int len = 0;
    while (str[len] != '\0') {
        len++;
    }
    return len;
}
```

**C Output (header):**
```c
int strlen_custom(const char* str);
```

**C Output (implementation):**
```c
int strlen_custom(const char* str) {
    int len = 0;
    while (str[len] != '\0') {
        len++;
    }
    return len;
}
```

## Test Cases

### Unit Tests

1. **test_simple_function_declaration**
   - Input: `int foo();`
   - Expected: C FunctionDecl with name "foo", return type int, no parameters

2. **test_simple_function_definition**
   - Input: `int foo() { return 42; }`
   - Expected: C FunctionDecl with body containing ReturnStmt

3. **test_function_with_parameters**
   - Input: `void bar(int x, float y);`
   - Expected: C FunctionDecl with two ParmVarDecls

4. **test_function_with_reference_parameter**
   - Input: `void modify(int& x);`
   - Expected: C FunctionDecl with ParmVarDecl of type `int*`

5. **test_inline_function**
   - Input: `inline int square(int x) { return x * x; }`
   - Expected: C FunctionDecl with inline and static storage class

6. **test_static_function**
   - Input: `static void internal() {}`
   - Expected: C FunctionDecl with static storage class

7. **test_const_reference_parameter**
   - Input: `void print(const int& x);`
   - Expected: C FunctionDecl with ParmVarDecl of type `const int*`

8. **test_multiple_parameters_mixed**
   - Input: `void complex(int x, int& y, const int& z, int* w);`
   - Expected: C FunctionDecl with correct pointer translations

### Integration Tests

1. **test_function_calls_another_function**
   - Input: Two functions where one calls the other
   - Expected: Both functions translated, call expression correct

2. **test_recursive_function**
   - Input: Function that calls itself
   - Expected: Correct C recursive function

3. **test_forward_declaration**
   - Input: Function declaration followed by definition
   - Expected: Both translated correctly to header/implementation

### Edge Cases

1. **test_empty_function_body**
   - Input: `void noop() {}`
   - Expected: Empty CompoundStmt in body

2. **test_variadic_function**
   - Input: `void printf_like(const char* fmt, ...);`
   - Expected: Variadic preserved in C

3. **test_function_returning_pointer**
   - Input: `int* allocate(int size);`
   - Expected: Return type correctly translated

4. **test_function_with_array_parameter**
   - Input: `void process(int arr[], int size);`
   - Expected: Array decay to pointer preserved

5. **test_function_with_function_pointer_parameter**
   - Input: `void callback(void (*fn)(int));`
   - Expected: Function pointer type preserved

### Error Cases

1. **test_default_parameter_rejection**
   - Input: `void foo(int x = 42);`
   - Expected: Error or warning about unsupported feature

2. **test_deleted_function_skipped**
   - Input: `void foo() = delete;`
   - Expected: Function not translated

3. **test_defaulted_function_skipped**
   - Input: `void foo() = default;` (in context where applicable)
   - Expected: Function not translated

## Implementation Notes

### Reference to Pointer Translation

When translating reference parameters:
1. Check if parameter type is a reference: `paramType->isReferenceType()`
2. Get non-reference type: `paramType.getNonReferenceType()`
3. Create pointer type: `context.getPointerType(nonRefType)`
4. Preserve const qualifiers from original reference

### Type Translation

Delegate all type translation to TypeTranslator:
- Basic types: `int`, `float`, `double`, `char` → same
- `bool` → `int` or `_Bool` (C99)
- References → pointers
- Complex types → handled by TypeTranslator

### Storage Class Handling

```cpp
StorageClass getStorageClass(FunctionDecl* FD) {
    if (FD->isInlineSpecified())
        return SC_Static; // inline functions are static in C

    if (FD->getStorageClass() == SC_Static)
        return SC_Static;

    return SC_None; // External linkage
}
```

### Body Translation

Delegate to StatementHandler - don't attempt to translate statements directly:
```cpp
Stmt* C_body = StatementHandler->translateStmt(FD->getBody());
```

## Future Enhancements

### Phase 2: Namespaces
- Add namespace prefix to function names
- Example: `namespace Math { int add(...) }` → `int Math_add(...)`

### Phase 3: Function Overloading
- Name mangling for overloaded functions
- Example: `int foo(int)` and `float foo(float)` → `int foo_i(int)` and `float foo_f(float)`

### Phase 4: Template Functions
- Monomorphization handled by TemplateMonomorphizer
- Generate C functions for each instantiation

### Phase 5: Exception Specifications
- Translate `noexcept` to comments or error codes
- Handle exception specifications (ignored in C)

## Related Handlers

- **MethodToFunctionTranslator**: Handles class member functions
- **ConstructorHandler**: Handles constructor translation
- **DestructorHandler**: Handles destructor translation
- **StatementHandler**: Translates function bodies
- **ExpressionHandler**: Translates expressions within statements
- **TypeTranslator**: Translates all C++ types to C types
