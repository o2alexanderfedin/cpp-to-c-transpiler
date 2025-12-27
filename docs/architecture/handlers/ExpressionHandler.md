# ExpressionHandler Specification

## Responsibility

The ExpressionHandler is responsible for translating C++ expressions into their C equivalents. This includes arithmetic operations, logical operations, function calls, variable references, literals, casts, and member access. It handles the translation of expression trees recursively, preserving semantics while adapting C++ specific features to C.

## AST Nodes Processed

### Binary and Unary Operations
- **BinaryOperator**: Arithmetic (+, -, *, /, %), comparison (==, !=, <, >, <=, >=), logical (&&, ||), bitwise (&, |, ^, <<, >>), assignment (=, +=, -=, etc.)
- **UnaryOperator**: Prefix/postfix increment/decrement (++, --), address-of (&), dereference (*), logical not (!), bitwise not (~), unary plus/minus (+, -)
- **ConditionalOperator**: Ternary operator (? :)

### Literals
- **IntegerLiteral**: Integer constants (42, 0xFF, 0b1010)
- **FloatingLiteral**: Floating-point constants (3.14, 1.0e10)
- **StringLiteral**: String constants ("hello")
- **CharacterLiteral**: Character constants ('a', '\n')
- **CXXBoolLiteralExpr**: Boolean literals (true, false)
- **CXXNullPtrLiteralExpr**: Null pointer literal (nullptr)

### References and Calls
- **DeclRefExpr**: Variable/function references
- **CallExpr**: Function calls
- **MemberExpr**: Member access (obj.member, ptr->member) - for plain data members
- **ArraySubscriptExpr**: Array indexing (arr[i])

### Casts and Conversions
- **ImplicitCastExpr**: Compiler-inserted casts
- **CStyleCastExpr**: C-style casts ((int)x)
- **CXXStaticCastExpr**: static_cast
- **CXXReinterpretCastExpr**: reinterpret_cast
- **CXXConstCastExpr**: const_cast

### Other Expressions
- **ParenExpr**: Parenthesized expressions
- **InitListExpr**: Initializer lists {1, 2, 3}
- **UnaryExprOrTypeTraitExpr**: sizeof, alignof

## Translation Strategy

### Core Principle
Most C++ expressions translate directly to C expressions with the same syntax. The key challenges are:
1. **Reference handling**: Dereference references when used, take address when initialized
2. **Type-specific translations**: bool → int, nullptr → NULL
3. **Member access**: May need transformation for methods (handled separately)
4. **Operator overloading**: Not in Phase 1, error for now

### Key Transformations

1. **Boolean Literals**
   - `true` → `1`
   - `false` → `0`

2. **Null Pointer**
   - `nullptr` → `NULL`

3. **Reference Variables**
   - When used as rvalue: auto-dereference
   - When used as lvalue in assignment: auto-dereference
   - When initialized: take address of initializer

4. **Casts**
   - `static_cast<T>(expr)` → `(T)(expr)`
   - `reinterpret_cast<T>(expr)` → `(T)(expr)`
   - `const_cast<T>(expr)` → `(T)(expr)`

## Dependencies

- **TypeTranslator**: To translate types in casts
- **VariableHandler**: To understand variable types (especially references)
- **FunctionHandler**: To understand function signatures for call translation

## Algorithm

### Main Translation Entry Point

```cpp
Expr* translateExpr(Expr* E) {
    if (!E) return nullptr;

    // Strip implicit nodes if needed
    E = E->IgnoreImplicit(); // or handle ImplicitCastExpr explicitly

    switch (E->getStmtClass()) {
        case Stmt::IntegerLiteralClass:
            return translateIntegerLiteral(cast<IntegerLiteral>(E));
        case Stmt::FloatingLiteralClass:
            return translateFloatingLiteral(cast<FloatingLiteral>(E));
        case Stmt::StringLiteralClass:
            return translateStringLiteral(cast<StringLiteral>(E));
        case Stmt::CharacterLiteralClass:
            return translateCharacterLiteral(cast<CharacterLiteral>(E));
        case Stmt::CXXBoolLiteralExprClass:
            return translateBoolLiteral(cast<CXXBoolLiteralExpr>(E));
        case Stmt::CXXNullPtrLiteralExprClass:
            return translateNullPtr(cast<CXXNullPtrLiteralExpr>(E));
        case Stmt::DeclRefExprClass:
            return translateDeclRefExpr(cast<DeclRefExpr>(E));
        case Stmt::BinaryOperatorClass:
            return translateBinaryOperator(cast<BinaryOperator>(E));
        case Stmt::UnaryOperatorClass:
            return translateUnaryOperator(cast<UnaryOperator>(E));
        case Stmt::CallExprClass:
            return translateCallExpr(cast<CallExpr>(E));
        case Stmt::MemberExprClass:
            return translateMemberExpr(cast<MemberExpr>(E));
        case Stmt::ArraySubscriptExprClass:
            return translateArraySubscript(cast<ArraySubscriptExpr>(E));
        case Stmt::ImplicitCastExprClass:
            return translateImplicitCast(cast<ImplicitCastExpr>(E));
        case Stmt::CStyleCastExprClass:
            return translateCStyleCast(cast<CStyleCastExpr>(E));
        case Stmt::CXXStaticCastExprClass:
            return translateStaticCast(cast<CXXStaticCastExpr>(E));
        case Stmt::ParenExprClass:
            return translateParenExpr(cast<ParenExpr>(E));
        case Stmt::InitListExprClass:
            return translateInitListExpr(cast<InitListExpr>(E));
        case Stmt::ConditionalOperatorClass:
            return translateConditionalOperator(cast<ConditionalOperator>(E));
        case Stmt::UnaryExprOrTypeTraitExprClass:
            return translateSizeofExpr(cast<UnaryExprOrTypeTraitExpr>(E));
        default:
            report_error("Unsupported expression type");
            return nullptr;
    }
}
```

### Specific Translation Functions

#### Literals

```cpp
Expr* translateIntegerLiteral(IntegerLiteral* IL) {
    // Direct translation
    return new IntegerLiteral(
        IL->getValue(),
        IL->getType(),
        IL->getLocation()
    );
}

Expr* translateBoolLiteral(CXXBoolLiteralExpr* BL) {
    // true → 1, false → 0
    return new IntegerLiteral(
        BL->getValue() ? 1 : 0,
        context.IntTy,
        BL->getLocation()
    );
}

Expr* translateNullPtr(CXXNullPtrLiteralExpr* NP) {
    // nullptr → NULL (represented as integer 0 cast to void*)
    return createNullPointer(context);
}
```

#### Binary Operators

```cpp
Expr* translateBinaryOperator(BinaryOperator* BO) {
    Expr* LHS = translateExpr(BO->getLHS());
    Expr* RHS = translateExpr(BO->getRHS());

    // Handle reference operands
    LHS = handleReferenceExpr(LHS, BO->getLHS()->getType());
    RHS = handleReferenceExpr(RHS, BO->getRHS()->getType());

    return new BinaryOperator(
        LHS,
        RHS,
        BO->getOpcode(),
        BO->getType(),
        BO->getValueKind(),
        BO->getObjectKind(),
        BO->getOperatorLoc()
    );
}
```

#### Unary Operators

```cpp
Expr* translateUnaryOperator(UnaryOperator* UO) {
    Expr* subExpr = translateExpr(UO->getSubExpr());

    // Special handling for address-of and dereference with references
    if (UO->getOpcode() == UO_AddrOf) {
        // Taking address of reference: skip the auto-dereference
        subExpr = translateExprRaw(UO->getSubExpr());
    } else if (UO->getOpcode() == UO_Deref) {
        // Dereferencing: handle reference types
        subExpr = handleReferenceExpr(subExpr, UO->getSubExpr()->getType());
    }

    return new UnaryOperator(
        subExpr,
        UO->getOpcode(),
        UO->getType(),
        UO->getValueKind(),
        UO->getObjectKind(),
        UO->getOperatorLoc()
    );
}
```

#### DeclRefExpr (Variable References)

```cpp
Expr* translateDeclRefExpr(DeclRefExpr* DRE) {
    ValueDecl* decl = DRE->getDecl();

    // Find the translated C declaration
    ValueDecl* C_decl = findTranslatedDecl(decl);

    Expr* result = new DeclRefExpr(
        C_decl,
        false, // refersToEnclosingVariableOrCapture
        C_decl->getType(),
        DRE->getValueKind(),
        DRE->getLocation()
    );

    // Auto-dereference if this is a reference variable being used
    if (decl->getType()->isReferenceType()) {
        result = createDereference(result);
    }

    return result;
}
```

#### CallExpr (Function Calls)

```cpp
Expr* translateCallExpr(CallExpr* CE) {
    // Translate callee (function being called)
    Expr* callee = translateExpr(CE->getCallee());

    // Translate arguments
    std::vector<Expr*> C_args;
    for (unsigned i = 0; i < CE->getNumArgs(); ++i) {
        Expr* arg = translateExpr(CE->getArg(i));

        // Check if parameter is a reference
        if (FunctionDecl* FD = CE->getDirectCallee()) {
            if (i < FD->getNumParams()) {
                QualType paramType = FD->getParamDecl(i)->getType();
                if (paramType->isReferenceType()) {
                    // Pass address of argument
                    arg = createAddressOf(arg);
                }
            }
        }

        C_args.push_back(arg);
    }

    return new CallExpr(
        context,
        callee,
        C_args,
        CE->getType(),
        CE->getValueKind(),
        CE->getRParenLoc()
    );
}
```

#### MemberExpr (Member Access)

```cpp
Expr* translateMemberExpr(MemberExpr* ME) {
    Expr* base = translateExpr(ME->getBase());
    ValueDecl* member = ME->getMemberDecl();

    // For Phase 1, only handle plain data members
    if (isa<FieldDecl>(member)) {
        FieldDecl* field = cast<FieldDecl>(member);
        FieldDecl* C_field = findTranslatedField(field);

        return new MemberExpr(
            base,
            ME->isArrow(),
            ME->getOperatorLoc(),
            C_field,
            ME->getMemberLoc(),
            C_field->getType(),
            ME->getValueKind(),
            ME->getObjectKind()
        );
    }

    // Method calls handled by MethodToFunctionTranslator
    report_error("Method calls not handled in Phase 1");
    return nullptr;
}
```

#### Casts

```cpp
Expr* translateImplicitCast(ImplicitCastExpr* ICE) {
    Expr* subExpr = translateExpr(ICE->getSubExpr());
    QualType targetType = TypeTranslator->translate(ICE->getType());

    // Some implicit casts can be omitted, others need explicit cast
    switch (ICE->getCastKind()) {
        case CK_LValueToRValue:
        case CK_NoOp:
        case CK_ArrayToPointerDecay:
        case CK_FunctionToPointerDecay:
            return subExpr; // No explicit cast needed

        case CK_IntegralCast:
        case CK_IntegralToFloating:
        case CK_FloatingToIntegral:
        case CK_FloatingCast:
            // Create explicit cast in C
            return createCStyleCast(targetType, subExpr);

        default:
            return subExpr;
    }
}

Expr* translateCStyleCast(CStyleCastExpr* CCE) {
    Expr* subExpr = translateExpr(CCE->getSubExpr());
    QualType targetType = TypeTranslator->translate(CCE->getType());

    return createCStyleCast(targetType, subExpr);
}

Expr* translateStaticCast(CXXStaticCastExpr* SCE) {
    Expr* subExpr = translateExpr(SCE->getSubExpr());
    QualType targetType = TypeTranslator->translate(SCE->getType());

    // static_cast becomes C-style cast
    return createCStyleCast(targetType, subExpr);
}
```

## Reference Handling

The most complex aspect of expression translation is handling references correctly.

### Reference Variable Declaration
```cpp
// C++: int x = 10; int& ref = x;
// C: int x = 10; int* ref = &x;
```

### Reference Variable Usage (RValue)
```cpp
// C++: int y = ref; // ref is int&
// C: int y = *ref; // ref is int*
```

### Reference Variable Usage (LValue)
```cpp
// C++: ref = 20; // ref is int&
// C: *ref = 20; // ref is int*
```

### Reference Parameter Passing
```cpp
// C++: void foo(int& x); foo(y);
// C: void foo(int* x); foo(&y);
```

### Algorithm for Reference Handling

```cpp
Expr* handleReferenceExpr(Expr* E, QualType originalType) {
    if (originalType->isReferenceType()) {
        // This expression represents a reference variable
        // It's already a pointer in C AST, but we need to dereference it
        if (needsDereference(E)) {
            return createDereference(E);
        }
    }
    return E;
}

bool needsDereference(Expr* E) {
    // Don't dereference if:
    // - Taking address: &ref → just use ref (which is already a pointer)
    // - Passing to reference parameter: handled in CallExpr
    // - Initializing another reference: handled in VarDecl

    // Check parent context...
    return true; // Default: dereference
}
```

## Examples

### Example 1: Arithmetic Expression

**C++ Input:**
```cpp
int calculate(int a, int b) {
    return (a + b) * 2 - b / 2;
}
```

**C Output:**
```c
int calculate(int a, int b) {
    return (a + b) * 2 - b / 2;
}
```

### Example 2: Boolean Expression

**C++ Input:**
```cpp
bool isValid(int x) {
    return x >= 0 && x <= 100;
}
```

**C Output:**
```c
int isValid(int x) {
    return x >= 0 && x <= 100;
}
```

### Example 3: Pointer and Reference

**C++ Input:**
```cpp
void swap(int& a, int& b) {
    int temp = a;
    a = b;
    b = temp;
}
```

**C Output:**
```c
void swap(int* a, int* b) {
    int temp = *a;
    *a = *b;
    *b = temp;
}
```

### Example 4: Function Call with References

**C++ Input:**
```cpp
void increment(int& x) {
    x++;
}

void test() {
    int val = 5;
    increment(val);
}
```

**C Output:**
```c
void increment(int* x) {
    (*x)++;
}

void test() {
    int val = 5;
    increment(&val);
}
```

### Example 5: Type Casting

**C++ Input:**
```cpp
float convert(int x) {
    return static_cast<float>(x) / 2.0f;
}
```

**C Output:**
```c
float convert(int x) {
    return (float)(x) / 2.0f;
}
```

### Example 6: Null Pointer

**C++ Input:**
```cpp
int* getPointer(bool create) {
    if (create)
        return new int(42);
    return nullptr;
}
```

**C Output:**
```c
int* getPointer(int create) {
    if (create)
        return (int*)malloc(sizeof(int)); // new handled elsewhere
    return NULL;
}
```

### Example 7: Array Subscript

**C++ Input:**
```cpp
int sum(int arr[], int size) {
    int total = 0;
    for (int i = 0; i < size; i++) {
        total += arr[i];
    }
    return total;
}
```

**C Output:**
```c
int sum(int arr[], int size) {
    int total = 0;
    for (int i = 0; i < size; i++) {
        total += arr[i];
    }
    return total;
}
```

### Example 8: Ternary Operator

**C++ Input:**
```cpp
int max(int a, int b) {
    return (a > b) ? a : b;
}
```

**C Output:**
```c
int max(int a, int b) {
    return (a > b) ? a : b;
}
```

### Example 9: Sizeof Operator

**C++ Input:**
```cpp
size_t getSize() {
    return sizeof(int) + sizeof(float);
}
```

**C Output:**
```c
size_t getSize() {
    return sizeof(int) + sizeof(float);
}
```

### Example 10: Member Access

**C++ Input:**
```cpp
struct Point {
    int x, y;
};

int getX(Point* p) {
    return p->x;
}

int getY(Point p) {
    return p.y;
}
```

**C Output:**
```c
struct Point {
    int x, y;
};

int getX(struct Point* p) {
    return p->x;
}

int getY(struct Point p) {
    return p.y;
}
```

## Test Cases

### Unit Tests

1. **test_integer_literal**
   - Input: `42`
   - Expected: IntegerLiteral with value 42

2. **test_boolean_literal_true**
   - Input: `true`
   - Expected: IntegerLiteral with value 1

3. **test_boolean_literal_false**
   - Input: `false`
   - Expected: IntegerLiteral with value 0

4. **test_nullptr_literal**
   - Input: `nullptr`
   - Expected: NULL representation

5. **test_simple_addition**
   - Input: `a + b`
   - Expected: BinaryOperator with BO_Add

6. **test_compound_expression**
   - Input: `(a + b) * c`
   - Expected: BinaryOperator tree with correct precedence

7. **test_reference_variable_read**
   - Input: `int& ref = x; int y = ref;`
   - Expected: Dereference of ref pointer

8. **test_reference_variable_write**
   - Input: `int& ref = x; ref = 10;`
   - Expected: Dereference on LHS of assignment

9. **test_function_call_no_args**
   - Input: `foo()`
   - Expected: CallExpr with no arguments

10. **test_function_call_with_args**
    - Input: `add(1, 2)`
    - Expected: CallExpr with two IntegerLiteral arguments

11. **test_function_call_ref_param**
    - Input: `modify(x)` where `modify(int& a)`
    - Expected: CallExpr with address-of argument

12. **test_array_subscript**
    - Input: `arr[5]`
    - Expected: ArraySubscriptExpr

13. **test_member_access_arrow**
    - Input: `ptr->field`
    - Expected: MemberExpr with isArrow=true

14. **test_member_access_dot**
    - Input: `obj.field`
    - Expected: MemberExpr with isArrow=false

15. **test_static_cast**
    - Input: `static_cast<int>(3.14)`
    - Expected: CStyleCastExpr to int

16. **test_ternary_operator**
    - Input: `x > 0 ? x : -x`
    - Expected: ConditionalOperator

17. **test_sizeof_type**
    - Input: `sizeof(int)`
    - Expected: UnaryExprOrTypeTraitExpr

18. **test_sizeof_expr**
    - Input: `sizeof(x)`
    - Expected: UnaryExprOrTypeTraitExpr

### Integration Tests

1. **test_complex_arithmetic**
   - Input: `(a + b * c) / (d - e)`
   - Expected: Correct operator precedence preserved

2. **test_logical_and_comparison**
   - Input: `x > 0 && y < 100`
   - Expected: Logical AND of two comparisons

3. **test_nested_function_calls**
   - Input: `foo(bar(x), baz(y))`
   - Expected: CallExpr with CallExpr arguments

4. **test_reference_chain**
   - Input: `int& ref1 = x; int& ref2 = ref1; int y = ref2;`
   - Expected: Correct dereferences

### Edge Cases

1. **test_empty_string_literal**
   - Input: `""`
   - Expected: StringLiteral with length 0

2. **test_escape_sequences**
   - Input: `"hello\nworld\t!"`
   - Expected: StringLiteral with escape sequences preserved

3. **test_prefix_increment**
   - Input: `++x`
   - Expected: UnaryOperator with UO_PreInc

4. **test_postfix_increment**
   - Input: `x++`
   - Expected: UnaryOperator with UO_PostInc

5. **test_address_of_reference**
   - Input: `int& ref = x; int* ptr = &ref;`
   - Expected: No double-address-of, ptr = ref (already pointer)

6. **test_dereference_pointer_to_reference**
   - Input: Complex pointer/reference combinations
   - Expected: Correct pointer arithmetic

7. **test_comma_operator**
   - Input: `x = (a++, b++, c)`
   - Expected: Comma operator preserved

## Implementation Notes

### Expression Context Tracking

To handle references correctly, we need to track expression context:
- **RValue context**: Reading a value → dereference reference
- **LValue context**: Modifying a value → dereference reference
- **Address-of context**: Taking address → no dereference
- **Reference parameter**: Passing argument → take address

```cpp
enum ExprContext {
    EC_RValue,
    EC_LValue,
    EC_AddressOf,
    EC_RefParam
};

Expr* translateExpr(Expr* E, ExprContext context = EC_RValue);
```

### Implicit Cast Handling

Clang inserts many implicit casts. We can:
1. **Preserve them**: Translate each ImplicitCastExpr
2. **Strip them**: Use `IgnoreImplicit()` and rely on C compiler
3. **Selective**: Strip no-op casts, preserve type-changing casts

Recommendation: Selective approach for cleaner C code.

### Operator Precedence

C and C++ have the same operator precedence, so we can preserve the expression tree structure directly.

### Short-Circuit Evaluation

`&&` and `||` operators have short-circuit semantics in both C and C++, so direct translation is correct.

## Future Enhancements

### Phase 2: Operator Overloading
- Translate operator calls to function calls
- Example: `a + b` → `operator_add(&a, &b)` if operator+ is overloaded

### Phase 3: Lambda Expressions
- Translate lambdas to function pointers + structs for captures

### Phase 4: Range-Based For
- Translate to traditional for loops with iterators

### Phase 5: Smart Pointers
- Translate unique_ptr/shared_ptr operations to manual memory management

## Related Handlers

- **FunctionHandler**: Contains expressions in function bodies
- **VariableHandler**: Variable declarations have initialization expressions
- **StatementHandler**: Statements contain expressions (DeclStmt, ReturnStmt, etc.)
- **TypeTranslator**: Translates types used in casts
- **MethodToFunctionTranslator**: Handles method call expressions
