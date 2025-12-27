# Annotated AST: Basic Function

## Source Code
```cpp
int add(int a, int b) {
    int result = a + b;
    return result;
}
```

## AST Structure (Annotated)

```
FunctionDecl 0x157927198 <01-basic-function.cpp:2:1, line:5:1> line:2:5 add 'int (int, int)'
│   ↑ Function declaration node - represents the entire function
│   Name: "add", Type: "int (int, int)"
│
├─ParmVarDecl 0x157927030 <col:9, col:13> col:13 used a 'int'
│   ↑ Parameter declaration - first parameter "a"
│   Type: int, marked "used" (referenced in function body)
│
├─ParmVarDecl 0x1579270b0 <col:16, col:20> col:20 used b 'int'
│   ↑ Parameter declaration - second parameter "b"
│   Type: int, marked "used"
│
└─CompoundStmt 0x157927408 <col:23, line:5:1>
    ↑ Compound statement - the function body { ... }
    │
    ├─DeclStmt 0x1579273a8 <line:3:5, col:23>
    │   ↑ Declaration statement - "int result = a + b;"
    │   │
    │   └─VarDecl 0x1579272b0 <col:5, col:22> col:9 used result 'int' cinit
    │       ↑ Variable declaration - "result"
    │       Type: int, has C-style initializer (cinit)
    │       │
    │       └─BinaryOperator 0x157927388 <col:18, col:22> 'int' '+'
    │           ↑ Binary operator - "a + b"
    │           Operator: '+', Result type: int
    │           │
    │           ├─ImplicitCastExpr 0x157927358 <col:18> 'int' <LValueToRValue>
    │           │   ↑ Implicit cast - converts lvalue to rvalue (loads value)
    │           │   │
    │           │   └─DeclRefExpr 0x157927318 <col:18> 'int' lvalue ParmVar 0x157927030 'a' 'int'
    │           │       ↑ Declaration reference - refers to parameter "a"
    │           │       References: ParmVarDecl 'a' (defined above)
    │           │
    │           └─ImplicitCastExpr 0x157927370 <col:22> 'int' <LValueToRValue>
    │               ↑ Implicit cast for "b"
    │               │
    │               └─DeclRefExpr 0x157927338 <col:22> 'int' lvalue ParmVar 0x1579270b0 'b' 'int'
    │                   ↑ Declaration reference - refers to parameter "b"
    │
    └─ReturnStmt 0x1579273f8 <line:4:5, col:12>
        ↑ Return statement - "return result;"
        │
        └─ImplicitCastExpr 0x1579273e0 <col:12> 'int' <LValueToRValue>
            ↑ Implicit cast - loads value of "result"
            │
            └─DeclRefExpr 0x1579273c0 <col:12> 'int' lvalue Var 0x1579272b0 'result' 'int'
                ↑ Declaration reference - refers to variable "result"
                References: VarDecl 'result' (defined above)
```

## Key Observations for Translation

### 1. Function Translation (FunctionDecl → C function)
- Node: `FunctionDecl`
- Extract: name ("add"), return type (int), parameters
- Generate: Equivalent C function declaration

### 2. Parameter Translation (ParmVarDecl → C parameters)
- Node: `ParmVarDecl`
- Extract: name, type
- Generate: C function parameters (same syntax)

### 3. Variable Declaration (VarDecl → C variable)
- Node: `VarDecl` within `DeclStmt`
- Extract: name, type, initializer expression
- Generate: C variable declaration with initialization

### 4. Binary Operators (BinaryOperator → C operator)
- Node: `BinaryOperator`
- Extract: operator ('+'), left operand, right operand
- Generate: C binary expression (same syntax)

### 5. Variable References (DeclRefExpr → C identifier)
- Node: `DeclRefExpr`
- Extract: referenced declaration, name
- Generate: C identifier (variable name)
- **Important**: Track which declaration it refers to

### 6. Implicit Casts (ImplicitCastExpr)
- Node: `ImplicitCastExpr`
- Purpose: LValueToRValue conversion (load value from variable)
- Translation: Usually transparent in C (automatic)
- **Decision**: Skip in C code generation (C does this implicitly)

### 7. Return Statement (ReturnStmt → C return)
- Node: `ReturnStmt`
- Extract: return expression
- Generate: C return statement (same syntax)

## Handler Mapping

Based on this example, we need:

1. **FunctionHandler**
   - Processes: `FunctionDecl`
   - Generates: C function with signature and body

2. **VariableHandler**
   - Processes: `VarDecl`, `ParmVarDecl`
   - Generates: C variable declarations

3. **ExpressionHandler**
   - Processes: `BinaryOperator`, `DeclRefExpr`, `ImplicitCastExpr`, `IntegerLiteral`
   - Generates: C expressions

4. **StatementHandler**
   - Processes: `CompoundStmt`, `DeclStmt`, `ReturnStmt`
   - Generates: C statements

## Complexity Analysis

This example demonstrates **Complexity Level 1** features:
- ✅ Simple functions
- ✅ Integer parameters and return
- ✅ Local variables
- ✅ Arithmetic operators
- ✅ Variable references
- ✅ Return statements

No advanced features:
- ❌ No classes/structs
- ❌ No pointers/references
- ❌ No templates
- ❌ No inheritance
- ❌ No method calls

This is the perfect starting point for implementation.
