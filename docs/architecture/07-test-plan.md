# Comprehensive Test Plan

## Overview

This document defines the complete testing strategy for all 12 implementation phases. Every handler method, feature, and integration point has corresponding tests.

**Testing Philosophy:**
- Test-Driven Development (TDD): Write tests before implementation
- 100% coverage for handlers
- Testing pyramid: Many unit tests, fewer integration tests, few E2E tests
- Each test is surgical and focused

**Test Organization:**
```
tests/
├── unit/handlers/          # Handler unit tests (C++ AST → C AST)
├── integration/handlers/   # Multi-handler integration tests
├── e2e/                   # End-to-end transpilation tests
└── fixtures/              # Test utilities and mocks
```

---

## Phase 1: Basic Functions & Arithmetic

### Unit Tests: FunctionHandler (18 tests)

**Location:** `tests/unit/handlers/FunctionHandlerTest.cpp`

1. `EmptyFunction` - `void foo() {}`
2. `FunctionWithVoidReturn` - `void bar() { }`
3. `FunctionWithIntReturn` - `int baz() { return 0; }`
4. `FunctionWithSingleParameter` - `int add(int a)`
5. `FunctionWithMultipleParameters` - `int add(int a, int b, int c)`
6. `FunctionWithFloatParameter` - `double sqrt(double x)`
7. `FunctionWithMixedParameters` - `void mix(int i, float f, double d)`
8. `FunctionWithBody` - Function with statements in body
9. `FunctionWithLocalVariables` - Function declaring local vars
10. `FunctionDeclarationOnly` - Forward declaration without body
11. `FunctionDefinitionAfterDecl` - Declaration then definition
12. `FunctionReturningPointer` - `int* allocate()`
13. `FunctionWithArrayParameter` - `void process(int arr[])`
14. `FunctionWithConstParameter` - `void print(const int x)`
15. `StaticFunction` - `static void helper()`
16. `InlineFunction` - `inline int square(int x)`
17. `FunctionCallingAnother` - Verify call expressions generated
18. `RecursiveFunction` - Function calling itself

### Unit Tests: VariableHandler (15 tests)

**Location:** `tests/unit/handlers/VariableHandlerTest.cpp`

1. `UninitializedLocalInt` - `int x;`
2. `InitializedLocalInt` - `int x = 10;`
3. `InitializedLocalFloat` - `float f = 3.14f;`
4. `InitializedLocalDouble` - `double d = 2.718;`
5. `MultipleVariablesSeparate` - `int a; int b;`
6. `VariableWithComplexInit` - `int x = a + b * 2;`
7. `ConstLocalVariable` - `const int MAX = 100;`
8. `PointerVariable` - `int* ptr;`
9. `PointerWithNullInit` - `int* ptr = nullptr;` (Phase 5 feature preview)
10. `CharVariable` - `char c = 'a';`
11. `BoolVariable` - `bool flag = true;` (translate to int)
12. `VariableUsedInExpression` - Verify variable ref works
13. `ShadowedVariable` - Inner scope var shadows outer
14. `UnusedVariable` - Variable declared but not used
15. `MultipleTypesInSameFunction` - Mix of int, float, double, char

### Unit Tests: ExpressionHandler (35 tests)

**Location:** `tests/unit/handlers/ExpressionHandlerTest.cpp`

**Literals (5 tests):**
1. `IntegerLiteral_Positive` - `42`
2. `IntegerLiteral_Negative` - `-10`
3. `IntegerLiteral_Zero` - `0`
4. `FloatingLiteral_Float` - `3.14f`
5. `FloatingLiteral_Double` - `2.718`

**Binary Operators - Arithmetic (5 tests):**
6. `BinaryAdd` - `a + b`
7. `BinarySubtract` - `a - b`
8. `BinaryMultiply` - `a * b`
9. `BinaryDivide` - `a / b`
10. `BinaryModulo` - `a % b`

**Complex Expressions (10 tests):**
11. `ArithmeticPrecedence` - `a + b * c` (verify precedence)
12. `ArithmeticParentheses` - `(a + b) * c`
13. `NestedArithmetic` - `((a + b) * (c - d)) / e`
14. `MixedTypeArithmetic` - `int + float`
15. `IntegerDivision` - `int / int`
16. `FloatDivision` - `float / float`
17. `MixedDivision` - `int / float`
18. `ModuloExpression` - `x % 10`
19. `MultipleAdditions` - `a + b + c + d`
20. `MultipleMultiplications` - `a * b * c * d`

**Variable References (5 tests):**
21. `SimpleVariableRef` - Reference to local variable
22. `VariableRefInExpression` - `x + y`
23. `VariableRefAsReturnValue` - `return x;`
24. `MultipleVarRefsInExpr` - `a + b * c - d`
25. `VariableRefToParameter` - Reference function parameter

**Implicit Casts (5 tests):**
26. `ImplicitIntToFloat` - `float f = 10;`
27. `ImplicitFloatToDouble` - `double d = 3.14f;`
28. `ImplicitIntPromotion` - `char` → `int` in arithmetic
29. `ImplicitPointerCast` - `void*` conversions
30. `NoImplicitCast` - Same type, no cast needed

**Function Calls (5 tests):**
31. `SimpleFunctionCall` - `add(1, 2)`
32. `NestedFunctionCall` - `add(mul(2, 3), 4)`
33. `FunctionCallInExpression` - `x + foo(y)`
34. `FunctionCallAsArgument` - `bar(foo(x))`
35. `VoidFunctionCall` - `print();`

### Unit Tests: StatementHandler (12 tests)

**Location:** `tests/unit/handlers/StatementHandlerTest.cpp`

1. `EmptyCompoundStmt` - `{}`
2. `CompoundStmtWithOneStatement` - `{ int x = 10; }`
3. `CompoundStmtWithMultipleStatements` - `{ int x; x = 10; return x; }`
4. `NestedCompoundStmt` - `{ { int x; } }`
5. `ReturnStmtVoid` - `return;`
6. `ReturnStmtWithValue` - `return 42;`
7. `ReturnStmtWithExpression` - `return a + b;`
8. `ReturnStmtWithFunctionCall` - `return foo(x);`
9. `DeclStmtSingle` - `int x;`
10. `DeclStmtWithInit` - `int x = 10;`
11. `DeclStmtMultipleVars` - `int x = 1, y = 2;`
12. `ExprStmt` - Expression statement (e.g., `x++;`)

**Total Phase 1 Unit Tests: 80 tests**

### Handler Integration Tests (25 tests)

**Location:** `tests/integration/handlers/Phase1IntegrationTest.cpp`

1. `FunctionWithLocalVariableAndReturn` - Function with local var, arithmetic, return
2. `FunctionWithMultipleLocalVars` - Multiple local variables
3. `FunctionWithComplexArithmetic` - Complex arithmetic expression
4. `FunctionCallingAnotherFunction` - Function call chain
5. `RecursiveFunctionWithBase` - Recursive function with base case
6. `FunctionWithMultipleReturns` - Multiple return statements
7. `FunctionWithNestedBlocks` - Nested compound statements
8. `FunctionWithVariableReuse` - Variable shadowing in nested scopes
9. `FunctionWithAllArithmeticOps` - Use all +, -, *, /, %
10. `FunctionWithMixedTypes` - Int, float, double mixing
11. `MultipleFunctionsInFile` - Multiple functions in same TU
12. `FunctionForwardDeclaration` - Declaration before definition
13. `FunctionWithUnusedParameter` - Parameter not used in body
14. `FunctionWithLargeExpression` - Very long arithmetic expression
15. `FunctionWithDeepNesting` - Deeply nested compound statements
16. `ZeroDivisionHandling` - Test division by literal zero
17. `NegativeNumberArithmetic` - Negative literals in expressions
18. `FloatingPointPrecision` - Float/double precision
19. `IntegerOverflowExpression` - Large integer arithmetic
20. `ConstParameterUsage` - Const parameters in expressions
21. `InlineFunctionDefinition` - Inline function translated
22. `StaticFunctionDefinition` - Static function translated
23. `PointerParameterBasic` - Function with pointer parameter
24. `ArrayParameterBasic` - Function with array parameter
25. `VariadicFunctionBasic` - Variadic function (printf-like)

### E2E Integration Tests (10 tests)

**Location:** `tests/e2e/phase1/`

1. **SimpleProgram** (`simple_program.cpp`)
   ```cpp
   int add(int a, int b) { return a + b; }
   int main() { return add(3, 4); }
   ```
   - Verify compiles with gcc
   - Verify exit code is 7

2. **ArithmeticOperations** (`arithmetic.cpp`)
   - All arithmetic operators
   - Verify output correctness

3. **FunctionChain** (`function_chain.cpp`)
   - Multiple functions calling each other
   - Verify output

4. **Fibonacci** (`fibonacci.cpp`)
   - Recursive fibonacci
   - Verify fib(10) = 55

5. **Factorial** (`factorial.cpp`)
   - Recursive factorial
   - Verify 5! = 120

6. **Calculator** (`calculator.cpp`)
   - Simple calculator with multiple operations
   - Verify various calculations

7. **MixedTypes** (`mixed_types.cpp`)
   - Int, float, double arithmetic
   - Verify type conversions

8. **NestedCalls** (`nested_calls.cpp`)
   - Deeply nested function calls
   - Verify correct evaluation

9. **LargeExpression** (`large_expression.cpp`)
   - Very long arithmetic expression
   - Verify result

10. **MultipleFiles** (multiple files)
    - Multiple source files
    - Verify linking works

### Verification Criteria

For each test type:

**Unit Tests:**
- [ ] Test creates correct C AST node
- [ ] AST matchers verify structure
- [ ] No code emission (tests AST only)

**Integration Tests:**
- [ ] Multiple handlers coordinate correctly
- [ ] C AST structure is complete
- [ ] Symbol tables populated correctly

**E2E Tests:**
- [ ] Generated C code compiles with `gcc -std=c99 -Wall -Werror`
- [ ] Executable runs without errors
- [ ] Output matches expected
- [ ] No memory leaks (valgrind)

---

## Phase 2: Control Flow

### Unit Tests: StatementHandler Extensions (15 tests)

**Location:** `tests/unit/handlers/StatementHandlerPhase2Test.cpp`

**If Statements (5 tests):**
1. `IfStmtSimple` - `if (x > 0) { }`
2. `IfStmtWithElse` - `if (x) { } else { }`
3. `IfStmtWithElseIf` - `if (x) { } else if (y) { } else { }`
4. `NestedIfStmt` - if inside if
5. `IfStmtWithComplexCondition` - `if (a && b || c)`

**While Statements (3 tests):**
6. `WhileStmtSimple` - `while (x > 0) { }`
7. `WhileStmtWithBreak` - while with break statement
8. `WhileStmtWithContinue` - while with continue

**For Statements (3 tests):**
9. `ForStmtSimple` - `for (int i = 0; i < 10; i++)`
10. `ForStmtWithBreak` - for with break
11. `ForStmtWithContinue` - for with continue

**Switch Statements (4 tests):**
12. `SwitchStmtSimple` - switch with one case
13. `SwitchStmtMultipleCases` - Multiple case labels
14. `SwitchStmtWithDefault` - switch with default
15. `SwitchStmtWithFallthrough` - Cases without break

### Unit Tests: ExpressionHandler Extensions (12 tests)

**Location:** `tests/unit/handlers/ExpressionHandlerPhase2Test.cpp`

**Comparison Operators (6 tests):**
1. `BinaryEquals` - `a == b`
2. `BinaryNotEquals` - `a != b`
3. `BinaryLessThan` - `a < b`
4. `BinaryGreaterThan` - `a > b`
5. `BinaryLessOrEqual` - `a <= b`
6. `BinaryGreaterOrEqual` - `a >= b`

**Logical Operators (3 tests):**
7. `BinaryLogicalAnd` - `a && b`
8. `BinaryLogicalOr` - `a || b`
9. `UnaryLogicalNot` - `!a`

**Unary Operators (3 tests):**
10. `UnaryIncrement` - `++x`, `x++`
11. `UnaryDecrement` - `--x`, `x--`
12. `UnaryMinus` - `-x`

**Total Phase 2 Unit Tests: 27 tests**

### Handler Integration Tests (15 tests)

**Location:** `tests/integration/handlers/Phase2IntegrationTest.cpp`

1. `IfElseWithArithmetic` - If/else with arithmetic in branches
2. `NestedLoops` - For inside while
3. `LoopWithBreakAndContinue` - Mixed break/continue
4. `SwitchInLoop` - Switch inside loop
5. `LoopInSwitch` - Loop inside switch case
6. `ComplexCondition` - Complex boolean expression
7. `ShortCircuitEvaluation` - `&&` and `||` short-circuit
8. `ComparisonChain` - `a < b < c` (should work as `a < b && b < c` if written that way)
9. `IncrementInCondition` - `while (i++ < 10)`
10. `DecrementInLoop` - `for (int i = 10; i > 0; i--)`
11. `MultipleBreaks` - Multiple break points in loop
12. `MultipleContinues` - Multiple continue points
13. `InfiniteLoopWithBreak` - `while (1) { if (cond) break; }`
14. `EmptyLoop` - Loop with empty body
15. `LoopWithSingleStatement` - Loop without braces

### E2E Integration Tests (8 tests)

**Location:** `tests/e2e/phase2/`

1. **Abs** (`abs.cpp`) - Absolute value using if/else
2. **Max** (`max.cpp`) - Find maximum using if/else
3. **SumArray** (`sum_array.cpp`) - Sum array using for loop
4. **FindInArray** (`find_in_array.cpp`) - Find element using while
5. **Fibonacci_Iterative** (`fibonacci_iter.cpp`) - Fibonacci using loop
6. **Factorial_Iterative** (`factorial_iter.cpp`) - Factorial using loop
7. **BubbleSort** (`bubble_sort.cpp`) - Bubble sort using nested loops
8. **DayOfWeek** (`day_of_week.cpp`) - Switch statement for day names

---

## Phase 3: Global Variables & Types

### Unit Tests: VariableHandler Extensions (10 tests)

**Location:** `tests/unit/handlers/VariableHandlerPhase3Test.cpp`

1. `GlobalVariableUninitialized` - `int global;`
2. `GlobalVariableInitialized` - `int global = 100;`
3. `GlobalConst` - `const int MAX = 100;`
4. `StaticLocalVariable` - `static int counter = 0;`
5. `StaticGlobalVariable` - `static int internal;`
6. `ExternVariable` - `extern int external;`
7. `ArrayGlobal` - `int arr[10];`
8. `ArrayWithInit` - `int arr[] = {1, 2, 3};`
9. `MultidimensionalArray` - `int matrix[3][3];`
10. `PointerGlobal` - `int* ptr;`

### Unit Tests: ExpressionHandler Extensions (8 tests)

**Location:** `tests/unit/handlers/ExpressionHandlerPhase3Test.cpp`

1. `StringLiteral` - `"Hello, World!"`
2. `EmptyStringLiteral` - `""`
3. `StringWithEscapes` - `"Line1\nLine2\tTab"`
4. `CharacterLiteral` - `'a'`
5. `CharacterEscapeSequence` - `'\n'`, `'\t'`, `'\0'`
6. `CStyleCast` - `(int)3.14`
7. `ArraySubscript` - `arr[i]`
8. `MultidimensionalArraySubscript` - `matrix[i][j]`

**Total Phase 3 Unit Tests: 18 tests**

### Handler Integration Tests (10 tests)

**Location:** `tests/integration/handlers/Phase3IntegrationTest.cpp`

1. `GlobalVariableUsedInFunction` - Global var accessed in function
2. `StaticLocalPersistence` - Static local persists across calls
3. `StringProcessing` - String literals in functions
4. `ArrayAccess` - Array subscript in expressions
5. `ArrayModification` - Modify array elements
6. `ArrayPassedToFunction` - Array as function parameter
7. `GlobalArrayInit` - Global array with initialization
8. `CharArrayString` - `char str[] = "Hello";`
9. `PointerToGlobal` - Pointer pointing to global
10. `MultipleGlobals` - Multiple global variables

### E2E Integration Tests (5 tests)

**Location:** `tests/e2e/phase3/`

1. **GlobalCounter** (`global_counter.cpp`) - Global variable incremented
2. **StaticCounter** (`static_counter.cpp`) - Static local counter
3. **StringReverse** (`string_reverse.cpp`) - Reverse string in char array
4. **MatrixAddition** (`matrix_addition.cpp`) - Add two matrices
5. **GlobalConfig** (`global_config.cpp`) - Global configuration values

---

## Phase 4: Structs (C-style)

### Unit Tests: RecordHandler (12 tests)

**Location:** `tests/unit/handlers/RecordHandlerTest.cpp`

1. `EmptyStruct` - `struct Empty {};`
2. `StructWithSingleField` - `struct Point { int x; };`
3. `StructWithMultipleFields` - `struct Point { int x; int y; };`
4. `StructWithMixedTypes` - `struct Mixed { int i; float f; double d; };`
5. `NestedStruct` - `struct Outer { struct Inner { int x; } inner; };`
6. `StructWithArray` - `struct Data { int values[10]; };`
7. `StructWithPointer` - `struct Node { Node* next; };`
8. `StructWithConstField` - `struct Const { const int id; };`
9. `ForwardDeclaredStruct` - `struct Fwd;`
10. `SelfReferencingStruct` - `struct Node { Node* next; };`
11. `StructTypedef` - `typedef struct { int x; } Point;`
12. `AnonymousStruct` - `struct { int x; } point;` (if supported)

### Unit Tests: ExpressionHandler Extensions (5 tests)

**Location:** `tests/unit/handlers/ExpressionHandlerPhase4Test.cpp`

1. `MemberAccessDot` - `point.x`
2. `MemberAccessArrow` - `ptr->x`
3. `NestedMemberAccess` - `outer.inner.value`
4. `MemberAccessInExpression` - `point.x + point.y`
5. `InitListExpr` - `{1, 2, 3}`

**Total Phase 4 Unit Tests: 17 tests**

### Handler Integration Tests (12 tests)

**Location:** `tests/integration/handlers/Phase4IntegrationTest.cpp`

1. `StructDeclarationAndUsage` - Declare and use struct
2. `StructPassedByValue` - Function taking struct by value
3. `StructPassedByPointer` - Function taking struct pointer
4. `StructReturned` - Function returning struct
5. `StructInitialization` - `Point p = {1, 2};`
6. `StructAssignment` - `Point p2 = p1;`
7. `StructArrayAccess` - `struct.array[i]`
8. `ArrayOfStructs` - `Point points[10];`
9. `NestedStructAccess` - Access nested struct fields
10. `StructPointerChain` - `node->next->next->value`
11. `StructInArithmetic` - `p1.x + p2.x`
12. `StructComparison` - Compare struct fields

### E2E Integration Tests (5 tests)

**Location:** `tests/e2e/phase4/`

1. **PointDistance** (`point_distance.cpp`) - Distance between two points
2. **LinkedListBasic** (`linked_list.cpp`) - Basic linked list operations
3. **StructArray** (`struct_array.cpp`) - Array of structs
4. **NestedStructs** (`nested_structs.cpp`) - Nested struct usage
5. **Rectangle** (`rectangle.cpp`) - Rectangle struct with area calculation

---

## Phase 5: Pointers & References

### Unit Tests: ExpressionHandler Extensions (15 tests)

**Location:** `tests/unit/handlers/ExpressionHandlerPhase5Test.cpp`

**Pointer Operations (8 tests):**
1. `AddressOfVariable` - `&x`
2. `DereferencePointer` - `*ptr`
3. `PointerArithmetic_Add` - `ptr + 1`
4. `PointerArithmetic_Subtract` - `ptr - 1`
5. `PointerArithmetic_Increment` - `ptr++`, `++ptr`
6. `PointerArithmetic_Decrement` - `ptr--`, `--ptr`
7. `PointerComparison` - `ptr1 < ptr2`
8. `NullptrLiteral` - `nullptr` → `NULL`

**Reference Translation (7 tests):**
9. `ReferenceParameter` - `void foo(int& x)` → `void foo(int* x)`
10. `ConstReferenceParameter` - `void foo(const int& x)` → `void foo(const int* x)`
11. `ReferenceReturn` - `int& foo()` → `int* foo()`
12. `ReferenceInFunctionBody` - Access via reference → dereference
13. `ReferenceCallSite` - `foo(x)` → `foo(&x)`
14. `ReferenceAlias` - `int& ref = x;` → `int* ref = &x;`
15. `ReferenceUsage` - `ref = 10;` → `*ref = 10;`

**Total Phase 5 Unit Tests: 15 tests**

### Handler Integration Tests (12 tests)

**Location:** `tests/integration/handlers/Phase5IntegrationTest.cpp`

1. `SwapFunction` - Swap using references
2. `PointerArrayIteration` - Iterate array using pointer
3. `PointerToStruct` - Pointer to struct with arrow operator
4. `FunctionReturningPointer` - Function returns pointer
5. `NullPointerCheck` - Check if pointer is NULL
6. `PointerDoubleIndirection` - `**ptr`
7. `ArrayDecay` - Array decaying to pointer
8. `PointerArithmeticBounds` - Pointer arithmetic within bounds
9. `ReferenceParameterModification` - Modify via reference
10. `ConstReferenceNoModification` - Cannot modify const reference
11. `ReferenceToPointer` - Reference to pointer type
12. `MultipleReferencesInFunction` - Multiple reference parameters

### E2E Integration Tests (5 tests)

**Location:** `tests/e2e/phase5/`

1. **Swap** (`swap.cpp`) - Swap two variables using references
2. **LinkedListTraversal** (`list_traversal.cpp`) - Traverse linked list
3. **ArrayManipulation** (`array_manipulation.cpp`) - Manipulate array via pointers
4. **PointerSort** (`pointer_sort.cpp`) - Sort using pointer manipulation
5. **ReferenceChain** (`reference_chain.cpp`) - Chain of reference calls

---

## Phase 6: Classes (Simple)

### Unit Tests: RecordHandler Extensions (10 tests)

**Location:** `tests/unit/handlers/RecordHandlerPhase6Test.cpp`

1. `SimpleClass` - `class Empty {};`
2. `ClassWithPrivateField` - Private field becomes public in struct
3. `ClassWithPublicField` - Public field stays public
4. `ClassWithProtectedField` - Protected becomes public
5. `ClassWithMixedAccess` - Mix of public/private/protected
6. `ClassWithMultipleFields` - Multiple fields of different types
7. `ClassFieldOrder` - Verify field order preserved
8. `ClassWithNestedClass` - Nested class lifted
9. `ClassWithStaticMember` - Static member moved to file scope
10. `ClassWithConstMember` - Const member preserved

### Unit Tests: MethodHandler (15 tests)

**Location:** `tests/unit/handlers/MethodHandlerTest.cpp`

1. `SimpleMethod` - `void foo() {}`
2. `MethodWithReturn` - `int bar() { return 0; }`
3. `MethodWithParameters` - `void set(int x)`
4. `MethodWithThisUsage` - Method accessing `this->field`
5. `ConstMethod` - `int get() const {}`
6. `MethodNameMangling` - `ClassName_methodName`
7. `ThisParameterAdded` - `this` is first parameter
8. `ThisPointerType` - `struct ClassName* this`
9. `PrivateMethod` - Private method becomes regular function
10. `PublicMethod` - Public method becomes regular function
11. `ProtectedMethod` - Protected becomes regular function
12. `StaticMethod` - Static method (no `this` parameter)
13. `InlineMethod` - Inline method handling
14. `MethodAccessingMultipleFields` - Access multiple fields via `this`
15. `MethodCallingAnotherMethod` - Method-to-method call (becomes function call)

### Unit Tests: ConstructorHandler (10 tests)

**Location:** `tests/unit/handlers/ConstructorHandlerTest.cpp`

1. `DefaultConstructor` - `ClassName() {}`
2. `ParameterizedConstructor` - `ClassName(int x)`
3. `ConstructorWithInitialization` - Initialize fields in body
4. `MultipleConstructors` - Multiple constructors (overloading)
5. `ConstructorNameMangling` - `ClassName_init`
6. `ConstructorThisParameter` - `this` parameter added
7. `ConstructorInitAllFields` - Initialize all fields
8. `ConstructorInitSomeFields` - Initialize some fields
9. `ConstructorWithComplexBody` - Constructor with statements
10. `CopyConstructor` - `ClassName(const ClassName& other)` (if supported)

### Unit Tests: DestructorHandler (8 tests)

**Location:** `tests/unit/handlers/DestructorHandlerTest.cpp`

1. `SimpleDestructor` - `~ClassName() {}`
2. `DestructorWithCleanup` - Destructor with cleanup code
3. `DestructorNameMangling` - `ClassName_destroy`
4. `DestructorThisParameter` - `this` parameter added
5. `DestructorInjection` - Auto-inject destructor call at scope end
6. `DestructorInjectionMultiple` - Multiple objects, all destroyed
7. `DestructorInjectionOrder` - LIFO order (last created, first destroyed)
8. `EmptyDestructor` - Empty destructor still generated

### Unit Tests: ExpressionHandler Extensions (5 tests)

**Location:** `tests/unit/handlers/ExpressionHandlerPhase6Test.cpp`

1. `ThisExpr` - `this` keyword
2. `ThisMemberAccess` - `this->field`
3. `ImplicitThisAccess` - `field` (implicit `this->field`)
4. `ThisPointerDereference` - `(*this).field`
5. `ThisInReturn` - `return *this;`

**Total Phase 6 Unit Tests: 48 tests**

### Handler Integration Tests (20 tests)

**Location:** `tests/integration/handlers/Phase6IntegrationTest.cpp`

1. `ClassWithMethods` - Class with multiple methods
2. `ClassWithConstructorAndDestructor` - Full lifecycle
3. `ClassWithFieldAccessInMethods` - Methods access fields
4. `ClassObjectCreation` - Create object, call constructor
5. `ClassObjectDestruction` - Destroy object, call destructor
6. `ClassMethodCalls` - Call methods on object
7. `ClassPointerMethodCalls` - Call methods through pointer
8. `MultipleObjects` - Multiple objects of same class
9. `NestedClasses` - Nested class usage
10. `ClassWithStaticMethod` - Static method call
11. `ClassWithConstMethod` - Const method call
12. `ClassWithOverloadedMethods` - Overloaded methods
13. `ClassAsStructMember` - Class object as struct field
14. `ArrayOfClassObjects` - Array of objects
15. `ClassObjectPassed` - Pass object to function
16. `ClassObjectReturned` - Return object from function
17. `ClassCopySemantics` - Object copy (if implemented)
18. `ClassScopeDestruction` - Objects destroyed at scope end
19. `ClassExceptionSafety` - Destructor called on early return (basic)
20. `ClassInheritancePreview` - Preview base class (Phase 9 prep)

### E2E Integration Tests (8 tests)

**Location:** `tests/e2e/phase6/`

1. **Counter** (`counter.cpp`) - Counter class with increment
2. **Point** (`point.cpp`) - Point class with distance calculation
3. **Rectangle** (`rectangle.cpp`) - Rectangle class with area/perimeter
4. **BankAccount** (`bank_account.cpp`) - Bank account with deposit/withdraw
5. **Stack** (`stack.cpp`) - Stack class with push/pop
6. **Queue** (`queue.cpp`) - Queue class with enqueue/dequeue
7. **Vector** (`vector.cpp`) - Simple vector class
8. **String** (`string.cpp`) - Simple string class

---

## Phase 7: Method Calls

### Unit Tests: ExpressionHandler Extensions (15 tests)

**Location:** `tests/unit/handlers/ExpressionHandlerPhase7Test.cpp`

1. `MethodCallSimple` - `obj.method()`
2. `MethodCallWithArgs` - `obj.method(1, 2)`
3. `MethodCallThroughPointer` - `ptr->method()`
4. `MethodCallReturnValue` - `int x = obj.getValue()`
5. `MethodCallInExpression` - `x + obj.getValue()`
6. `MethodCallNested` - `obj.get().get()`
7. `ChainedMethodCalls` - `obj.method1().method2()`
8. `MethodCallOnTemporary` - `ClassName().method()`
9. `OverloadedMethodCall_Int` - Overload with int parameter
10. `OverloadedMethodCall_Float` - Overload with float parameter
11. `OverloadedMethodCall_Multiple` - Multiple overloads
12. `MethodCallThisArgument` - Verify `this` passed as first arg
13. `MethodCallObjectAddress` - Verify `&obj` for value calls
14. `MethodCallPointerDirect` - Verify `ptr` for pointer calls
15. `ConstMethodCall` - Call const method

**Total Phase 7 Unit Tests: 15 tests**

### Handler Integration Tests (15 tests)

**Location:** `tests/integration/handlers/Phase7IntegrationTest.cpp`

1. `MethodCallSequence` - Multiple method calls in sequence
2. `MethodCallingMethod` - Method calling another method
3. `MethodCallWithFieldAccess` - `obj.method(obj.field)`
4. `MethodCallInLoop` - Call method in loop
5. `MethodCallInCondition` - `if (obj.isEmpty())`
6. `MethodCallReturnStruct` - Method returning struct
7. `MethodCallPassStruct` - Method taking struct parameter
8. `OverloadResolution` - Correct overload selected
9. `MethodCallMixed` - Mix of value and pointer calls
10. `MethodCallRecursive` - Method calling itself
11. `BuilderPattern` - Chained method calls returning *this
12. `MethodCallFromConstructor` - Constructor calling method
13. `MethodCallFromDestructor` - Destructor calling method
14. `MethodCallOnArrayElement` - `arr[i].method()`
15. `MethodCallNested_Deep` - Deeply nested calls

### E2E Integration Tests (5 tests)

**Location:** `tests/e2e/phase7/`

1. **Calculator** (`calculator.cpp`) - Calculator with method calls
2. **Builder** (`builder.cpp`) - Builder pattern implementation
3. **Iterator** (`iterator.cpp`) - Iterator pattern with method calls
4. **CommandPattern** (`command.cpp`) - Command pattern
5. **ObserverPattern** (`observer.cpp`) - Observer pattern (simple)

---

## Phase 8: Enums

### Unit Tests: EnumHandler (15 tests)

**Location:** `tests/unit/handlers/EnumHandlerTest.cpp`

**Unscoped Enums (5 tests):**
1. `UnscopedEnumSimple` - `enum Color { Red, Green, Blue };`
2. `UnscopedEnumWithValues` - `enum Status { OK = 0, ERROR = 1 };`
3. `UnscopedEnumConstantRef` - Reference enum constant
4. `UnscopedEnumInExpression` - Use enum in expression
5. `UnscopedEnumUnderlyingType` - Underlying type specification

**Scoped Enums (10 tests):**
6. `ScopedEnumSimple` - `enum class State { A, B, C };`
7. `ScopedEnumWithValues` - Explicit values
8. `ScopedEnumPrefixing` - `State::A` → `State__A`
9. `ScopedEnumConstantRef` - Reference scoped constant
10. `ScopedEnumInSwitch` - Scoped enum in switch
11. `ScopedEnumComparison` - Compare scoped enum values
12. `ScopedEnumAssignment` - Assign scoped enum
13. `ScopedEnumParameter` - Enum as function parameter
14. `ScopedEnumReturn` - Enum as return type
15. `ScopedEnumInStruct` - Enum as struct member

**Total Phase 8 Unit Tests: 15 tests**

### Handler Integration Tests (10 tests)

**Location:** `tests/integration/handlers/Phase8IntegrationTest.cpp`

1. `EnumInSwitch` - Switch on enum
2. `EnumInFunction` - Enum parameter and return
3. `EnumInClass` - Enum as class member
4. `EnumArray` - Array of enums
5. `EnumBitFlags` - Enum used as bit flags
6. `EnumComparison` - Compare enum values
7. `EnumIncrement` - Increment enum (cast to int)
8. `EnumCast` - Cast enum to/from int
9. `MultipleEnums` - Multiple enums in same file
10. `NestedEnum` - Enum inside class/struct

### E2E Integration Tests (5 tests)

**Location:** `tests/e2e/phase8/`

1. **StateMachine** (`state_machine.cpp`) - State machine using enum
2. **DayOfWeek** (`day_of_week.cpp`) - Day enum with switch
3. **ErrorCodes** (`error_codes.cpp`) - Error code enum
4. **TrafficLight** (`traffic_light.cpp`) - Traffic light states
5. **FileMode** (`file_mode.cpp`) - File mode flags

---

## Phase 9: Inheritance (Single)

### Unit Tests: RecordHandler Extensions (10 tests)

**Location:** `tests/unit/handlers/RecordHandlerPhase9Test.cpp`

1. `SimpleInheritance` - `class Derived : public Base`
2. `BaseFieldEmbedding` - Verify `__base` field added
3. `BaseFieldPosition` - Verify `__base` is first field
4. `InheritanceMultipleFields` - Base and derived fields
5. `InheritancePrivateBase` - Private inheritance (if supported)
6. `InheritanceProtectedBase` - Protected inheritance
7. `MultiLevelInheritance` - Base → Middle → Derived
8. `InheritanceCheckSingle` - Reject multiple inheritance
9. `InheritanceEmptyBase` - Empty base class
10. `InheritanceVirtualBase` - Virtual base (reject or handle)

### Unit Tests: ConstructorHandler Extensions (5 tests)

**Location:** `tests/unit/handlers/ConstructorHandlerPhase9Test.cpp`

1. `BaseConstructorCall` - Call base constructor
2. `BaseConstructorParameters` - Pass parameters to base
3. `BaseConstructorOrder` - Base initialized before derived
4. `MultiLevelConstructorChain` - Base → Middle → Derived chain
5. `ConstructorWithBaseAndFields` - Initialize both base and fields

### Unit Tests: ExpressionHandler Extensions (8 tests)

**Location:** `tests/unit/handlers/ExpressionHandlerPhase9Test.cpp`

1. `BaseFieldAccess` - `baseField` → `this->__base.baseField`
2. `BaseMethodCall` - `baseMethod()` → `Base_baseMethod(&this->__base)`
3. `DerivedFieldAccess` - Access derived field normally
4. `DerivedMethodCall` - Call derived method normally
5. `MixedFieldAccess` - Access both base and derived fields
6. `MixedMethodCalls` - Call both base and derived methods
7. `BasePointerAccess` - `ptr->__base.field`
8. `MultiLevelAccess` - Access through multiple inheritance levels

**Total Phase 9 Unit Tests: 23 tests**

### Handler Integration Tests (15 tests)

**Location:** `tests/integration/handlers/Phase9IntegrationTest.cpp`

1. `InheritanceFullLifecycle` - Create, use, destroy derived object
2. `InheritanceMethodOverride` - Derived method shadows base (non-virtual)
3. `InheritanceFieldAccess` - Access fields from base and derived
4. `InheritanceConstructorChain` - Constructor chain executes
5. `InheritanceDestructorChain` - Destructor chain executes (derived → base)
6. `InheritancePointerToBase` - `Base* ptr = &derived;` (limitations)
7. `InheritanceArrayOfDerived` - Array of derived objects
8. `InheritancePassToFunction` - Pass derived to function expecting base
9. `InheritanceReturnDerived` - Return derived object
10. `MultiLevelInheritanceAccess` - Access through 3 levels
11. `InheritanceStaticMethod` - Static method in base
12. `InheritanceConstMethod` - Const method in base
13. `InheritanceMixedAccess` - Complex access patterns
14. `InheritanceNestedClass` - Nested class in base
15. `InheritanceDowncast` - Manual downcast (cast to derived type)

### E2E Integration Tests (5 tests)

**Location:** `tests/e2e/phase9/`

1. **ShapeHierarchy** (`shapes.cpp`) - Shape → Circle, Rectangle
2. **AnimalHierarchy** (`animals.cpp`) - Animal → Dog, Cat
3. **VehicleHierarchy** (`vehicles.cpp`) - Vehicle → Car, Truck
4. **EmployeeHierarchy** (`employees.cpp`) - Employee → Manager, Developer
5. **MultiLevelInheritance** (`multi_level.cpp`) - 3-level hierarchy

---

## Phase 10: Templates (Monomorphization)

### Unit Tests: TemplateMonomorphizer (20 tests)

**Location:** `tests/unit/handlers/TemplateMonomorphizerTest.cpp`

**Class Templates (10 tests):**
1. `ClassTemplateSingleParam` - `template<typename T> class Box`
2. `ClassTemplateMultipleParams` - `template<typename K, typename V> class Pair`
3. `ClassTemplateInstantiation` - `Box<int>`, `Box<float>`
4. `ClassTemplateNameMangling` - `Box__int`, `Box__float`
5. `ClassTemplateFieldSubstitution` - `T value;` → `int value;`
6. `ClassTemplateMethodSubstitution` - Method with `T` parameter
7. `ClassTemplateMultipleInstantiations` - Multiple instantiations
8. `ClassTemplateNested` - Template inside template
9. `ClassTemplateWithInheritance` - Template inheriting from non-template
10. `ClassTemplateSpecialization` - Explicit specialization (if supported)

**Function Templates (10 tests):**
11. `FunctionTemplateSingleParam` - `template<typename T> T max(T a, T b)`
12. `FunctionTemplateMultipleParams` - Multiple type parameters
13. `FunctionTemplateInstantiation` - `max<int>`, `max<float>`
14. `FunctionTemplateNameMangling` - `max__int`, `max__float`
15. `FunctionTemplateParameterSubstitution` - Replace `T` with concrete type
16. `FunctionTemplateReturnSubstitution` - Return type substitution
17. `FunctionTemplateDeduction` - Template argument deduction
18. `FunctionTemplateOverload` - Template and non-template overload
19. `FunctionTemplateRecursive` - Recursive template function
20. `FunctionTemplateSpecialization` - Explicit specialization

**Total Phase 10 Unit Tests: 20 tests**

### Handler Integration Tests (15 tests)

**Location:** `tests/integration/handlers/Phase10IntegrationTest.cpp`

1. `TemplateClassWithMethods` - Template class with multiple methods
2. `TemplateMethodCalls` - Call methods on template instance
3. `TemplateConstructor` - Template class constructor
4. `TemplateDestructor` - Template class destructor
5. `TemplateInheritance` - Template class inheriting
6. `TemplateComposition` - Template class as member
7. `TemplateFunctionMultipleTypes` - Function template called with different types
8. `TemplateNested` - Nested template types (`Container<Container<int>>`)
9. `TemplateArray` - Array of template instances
10. `TemplatePointer` - Pointer to template instance
11. `TemplateReference` - Reference to template instance
12. `TemplateMixedInstantiations` - Mix of different instantiations
13. `TemplateStaticMember` - Static member in template (if supported)
14. `TemplateFriend` - Friend function in template (if supported)
15. `TemplatePartialSpecialization` - Partial specialization (if supported)

### E2E Integration Tests (5 tests)

**Location:** `tests/e2e/phase10/`

1. **GenericContainer** (`container.cpp`) - Container<int>, Container<float>
2. **GenericStack** (`stack.cpp`) - Stack template
3. **GenericPair** (`pair.cpp`) - Pair<K,V> template
4. **GenericSwap** (`swap.cpp`) - Template swap function
5. **GenericSort** (`sort.cpp`) - Template sort function

---

## Phase 11: Virtual Methods (Advanced)

### Unit Tests: VirtualMethodHandler (25 tests)

**Location:** `tests/unit/handlers/VirtualMethodHandlerTest.cpp`

**Vtable Generation (10 tests):**
1. `VtableStructCreation` - Verify vtable struct generated
2. `VtableFieldsForVirtualMethods` - Function pointers in vtable
3. `VtableInstance` - Vtable instance with correct pointers
4. `VtablePointerInStruct` - `__vtable` pointer added to struct
5. `VtableInitInConstructor` - Constructor sets vtable pointer
6. `VtableInheritance` - Derived vtable inherits base vtable structure
7. `VtableOverride` - Overridden method updates vtable entry
8. `VtablePureVirtual` - Pure virtual (NULL in vtable)
9. `VtableMultipleMethods` - Multiple virtual methods
10. `VtableDestructor` - Virtual destructor in vtable

**Virtual Calls (10 tests):**
11. `VirtualCallSimple` - `obj->method()` → `obj->__vtable->method(obj)`
12. `VirtualCallWithParams` - Virtual call with parameters
13. `VirtualCallReturnValue` - Virtual call returning value
14. `VirtualCallInExpression` - Virtual call in expression
15. `VirtualCallThroughBase` - Call via base pointer
16. `VirtualCallOverridden` - Call overridden method
17. `VirtualCallChain` - Chain of virtual calls
18. `VirtualCallInLoop` - Virtual call in loop
19. `VirtualCallConditional` - Virtual call in if statement
20. `VirtualCallRecursive` - Recursive virtual call

**Abstract Classes (5 tests):**
21. `AbstractClassDetection` - Detect abstract class (pure virtual)
22. `AbstractClassNoInstantiation` - Verify no instantiation allowed
23. `AbstractClassDerivedConcrete` - Derived makes class concrete
24. `AbstractClassMultiplePure` - Multiple pure virtual methods
25. `AbstractClassPartialOverride` - Partial override still abstract

**Total Phase 11 Unit Tests: 25 tests**

### Handler Integration Tests (15 tests)

**Location:** `tests/integration/handlers/Phase11IntegrationTest.cpp`

1. `VirtualMethodPolymorphism` - Polymorphic call works correctly
2. `VirtualMethodOverride` - Override changes behavior
3. `VirtualDestructorPolymorphic` - Polymorphic delete calls correct destructor
4. `VirtualMethodMultiLevel` - Virtual methods through multi-level inheritance
5. `VirtualMethodMixed` - Mix of virtual and non-virtual methods
6. `VirtualMethodAbstract` - Abstract base class usage
7. `VirtualMethodInterface` - Pure virtual interface
8. `VirtualMethodCovariant` - Covariant return types (if supported)
9. `VirtualMethodProtected` - Protected virtual methods
10. `VirtualMethodFinal` - Final methods (C++11, if supported)
11. `VirtualMethodOverload` - Virtual method overloading
12. `VirtualMethodDefaultParams` - Virtual with default params (if supported)
13. `VirtualMethodConstOverload` - Const/non-const virtual overload
14. `VirtualMethodStaticBinding` - Static binding (direct call)
15. `VirtualMethodDynamicBinding` - Dynamic binding (indirect call)

### E2E Integration Tests (5 tests)

**Location:** `tests/e2e/phase11/`

1. **PolymorphicShapes** (`poly_shapes.cpp`) - Polymorphic shape hierarchy
2. **PluginSystem** (`plugin.cpp`) - Plugin architecture with virtual methods
3. **AbstractFactory** (`abstract_factory.cpp`) - Abstract factory pattern
4. **Strategy** (`strategy.cpp`) - Strategy pattern
5. **Visitor** (`visitor.cpp`) - Visitor pattern (if fully supported)

---

## Phase 12: Namespaces

### Unit Tests: NamespaceHandler (15 tests)

**Location:** `tests/unit/handlers/NamespaceHandlerTest.cpp`

1. `SimpleNamespace` - `namespace Math { ... }`
2. `NamespacePrefix` - `Math::add` → `Math_add`
3. `NestedNamespace` - `namespace A { namespace B { ... } }`
4. `NestedNamespacePrefix` - `A::B::func` → `A_B_func`
5. `NamespaceFunction` - Function in namespace
6. `NamespaceClass` - Class in namespace
7. `NamespaceEnum` - Enum in namespace
8. `NamespaceVariable` - Variable in namespace
9. `UsingDirective` - `using namespace Math;`
10. `UsingDirectiveResolution` - Resolve names at translation time
11. `AnonymousNamespace` - `namespace { ... }` → `static`
12. `AnonymousNamespaceFunction` - Function in anonymous namespace
13. `NamespaceAlias` - `namespace M = Math;`
14. `NamespaceConflict` - Two namespaces with same name
15. `GlobalNamespace` - `::` global namespace qualifier

**Total Phase 12 Unit Tests: 15 tests**

### Handler Integration Tests (10 tests)

**Location:** `tests/integration/handlers/Phase12IntegrationTest.cpp`

1. `NamespaceFunctionCall` - Call function from namespace
2. `NamespaceClassUsage` - Use class from namespace
3. `NamespaceEnumUsage` - Use enum from namespace
4. `NamespaceMultipleLevels` - Deeply nested namespaces
5. `NamespaceUsingDirective` - Using directive effects
6. `NamespaceCrossReference` - Reference across namespaces
7. `NamespaceAnonymous` - Anonymous namespace behavior
8. `NamespaceOverloading` - Overloading in namespaces
9. `NamespaceTemplates` - Templates in namespaces (if supported)
10. `NamespaceInheritance` - Inheritance across namespaces

### E2E Integration Tests (5 tests)

**Location:** `tests/e2e/phase12/`

1. **MathLibrary** (`math_lib.cpp`) - Math namespace with functions
2. **GeometryLibrary** (`geometry.cpp`) - Geometry namespace with classes
3. **UtilsLibrary** (`utils.cpp`) - Utils namespace with mixed declarations
4. **NestedNamespaces** (`nested.cpp`) - Deeply nested namespaces
5. **MultipleNamespaces** (`multiple.cpp`) - Multiple namespaces in one file

---

## Summary Statistics

### Total Test Counts

**Unit Tests:**
- Phase 1: 80 tests
- Phase 2: 27 tests
- Phase 3: 18 tests
- Phase 4: 17 tests
- Phase 5: 15 tests
- Phase 6: 48 tests
- Phase 7: 15 tests
- Phase 8: 15 tests
- Phase 9: 23 tests
- Phase 10: 20 tests
- Phase 11: 25 tests
- Phase 12: 15 tests

**Total Unit Tests: 318 tests**

**Integration Tests:**
- Phase 1: 25 tests
- Phase 2: 15 tests
- Phase 3: 10 tests
- Phase 4: 12 tests
- Phase 5: 12 tests
- Phase 6: 20 tests
- Phase 7: 15 tests
- Phase 8: 10 tests
- Phase 9: 15 tests
- Phase 10: 15 tests
- Phase 11: 15 tests
- Phase 12: 10 tests

**Total Integration Tests: 174 tests**

**E2E Tests:**
- Phase 1: 10 tests
- Phase 2: 8 tests
- Phase 3: 5 tests
- Phase 4: 5 tests
- Phase 5: 5 tests
- Phase 6: 8 tests
- Phase 7: 5 tests
- Phase 8: 5 tests
- Phase 9: 5 tests
- Phase 10: 5 tests
- Phase 11: 5 tests
- Phase 12: 5 tests

**Total E2E Tests: 71 tests**

**Grand Total: 563 tests**

### Test LOC Estimates

**Unit Tests:** ~11,000-14,000 LOC
**Integration Tests:** ~8,000-10,000 LOC
**E2E Tests:** ~3,000-4,000 LOC
**Test Fixtures/Utilities:** ~2,000-3,000 LOC

**Total Testing LOC: ~24,000-31,000 LOC**

### Coverage Targets

**Handler Code:** 100% line coverage
**Integration Scenarios:** 90% coverage
**E2E Features:** 100% of documented features tested

---

## Continuous Integration

### CI Pipeline

```yaml
# .github/workflows/tests.yml
name: Transpiler Tests

on: [push, pull_request]

jobs:
  unit-tests:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v3
      - name: Build
        run: cmake -B build -DCMAKE_BUILD_TYPE=Debug
      - name: Compile
        run: cmake --build build
      - name: Run Unit Tests
        run: cd build && ctest -R "Unit.*" --output-on-failure
      - name: Coverage Report
        run: |
          cd build
          lcov --capture --directory . --output-file coverage.info
          lcov --remove coverage.info '/usr/*' --output-file coverage.info
          lcov --list coverage.info

  integration-tests:
    runs-on: ubuntu-latest
    needs: unit-tests
    steps:
      - uses: actions/checkout@v3
      - name: Build
        run: cmake -B build -DCMAKE_BUILD_TYPE=Debug
      - name: Compile
        run: cmake --build build
      - name: Run Integration Tests
        run: cd build && ctest -R "Integration.*" --output-on-failure

  e2e-tests:
    runs-on: ubuntu-latest
    needs: integration-tests
    steps:
      - uses: actions/checkout@v3
      - name: Build
        run: cmake -B build -DCMAKE_BUILD_TYPE=Release
      - name: Compile
        run: cmake --build build
      - name: Run E2E Tests
        run: cd build && ctest -R "E2E.*" --output-on-failure
      - name: Check Generated Code
        run: |
          cd build
          gcc -std=c99 -Wall -Werror tests/e2e/phase1/*.c
          ./a.out

  valgrind-check:
    runs-on: ubuntu-latest
    needs: e2e-tests
    steps:
      - uses: actions/checkout@v3
      - name: Install Valgrind
        run: sudo apt-get install -y valgrind
      - name: Build
        run: cmake -B build -DCMAKE_BUILD_TYPE=Debug
      - name: Run with Valgrind
        run: |
          cd build
          valgrind --leak-check=full --error-exitcode=1 ./tests/e2e/phase1/simple_program
```

---

## Test Execution Strategy

### TDD Workflow

For each feature:

1. **Write Unit Test** (Red)
   - Create test for handler method
   - Test should fail (handler not implemented)

2. **Implement Handler** (Green)
   - Write minimal code to pass test
   - Focus on correctness, not optimization

3. **Refactor** (Refactor)
   - Clean up implementation
   - Ensure test still passes

4. **Write Integration Test**
   - Test handler cooperation
   - Should pass if handlers correct

5. **Write E2E Test**
   - Complete transpilation
   - Verify compiled C code works

### Test Execution Order

**Development:**
1. Run unit tests for current handler (fast, ~1s)
2. Run integration tests for current phase (medium, ~5s)
3. Run E2E tests for current phase (slow, ~30s)

**Pre-commit:**
1. Run all unit tests (~10s)
2. Run all integration tests (~60s)
3. Run all E2E tests (~5min)

**CI:**
1. Run all tests in parallel
2. Generate coverage report
3. Fail if coverage < 100% for handlers

---

## Success Criteria

### Per Phase

- [ ] All unit tests pass
- [ ] All integration tests pass
- [ ] All E2E tests pass
- [ ] Generated C code compiles without warnings
- [ ] Generated C code produces correct output
- [ ] No memory leaks (valgrind clean)
- [ ] 100% handler coverage
- [ ] Code reviewed
- [ ] Documentation updated

### Overall

- [ ] 563 tests passing
- [ ] 100% handler code coverage
- [ ] All 12 phases verified
- [ ] CI pipeline green
- [ ] Performance acceptable (transpilation time)
- [ ] Generated C code quality high (readable, maintainable)

---

## Next Steps

1. Implement test infrastructure (fixtures, utilities)
2. Begin Phase 1 TDD implementation
3. Run tests continuously during development
4. Expand test suite as edge cases discovered
5. Maintain 100% coverage throughout
