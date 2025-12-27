# StatementHandler Specification

## Responsibility

The StatementHandler is responsible for translating C++ statements into their C equivalents. This includes control flow statements (if, while, for, switch), declaration statements, expression statements, return statements, and compound statements. It orchestrates the translation of statement sequences and manages the control flow structure of functions.

## AST Nodes Processed

### Control Flow Statements
- **IfStmt**: Conditional statements (if, if-else)
- **WhileStmt**: While loops
- **DoStmt**: Do-while loops
- **ForStmt**: Traditional for loops
- **SwitchStmt**: Switch statements
- **CaseStmt**: Case labels in switch
- **DefaultStmt**: Default label in switch
- **BreakStmt**: Break statements
- **ContinueStmt**: Continue statements
- **ReturnStmt**: Return statements
- **GotoStmt**: Goto statements (if present)
- **LabelStmt**: Labels for goto

### Other Statements
- **CompoundStmt**: Block statements { ... }
- **DeclStmt**: Declaration statements
- **NullStmt**: Empty statements ;
- **ExprStmt**: Expression statements (function calls, assignments, etc.)

### NOT Handled (Later Phases)
- **CXXForRangeStmt**: Range-based for loops (C++11)
- **CXXTryStmt**: Try-catch blocks
- **CXXCatchStmt**: Catch clauses

## Translation Strategy

### Core Principle
Most C++ control flow statements translate directly to C with identical syntax. The key work is:
1. **Recursively translate sub-statements**
2. **Translate condition expressions**
3. **Translate variable declarations in conditions**
4. **Preserve control flow semantics**

### Key Transformations
1. **Variable declarations in conditions**: Extract to separate statement
2. **Compound statements**: Translate each statement in sequence
3. **Expression statements**: Delegate to ExpressionHandler
4. **Return statements**: Translate return expression

## Dependencies

- **ExpressionHandler**: To translate condition and other expressions
- **VariableHandler**: To translate variable declarations in DeclStmt
- **FileOriginFilter**: Not directly used, but statements belong to functions

## Algorithm

### Main Translation Entry Point

```cpp
Stmt* translateStmt(Stmt* S) {
    if (!S) return nullptr;

    switch (S->getStmtClass()) {
        case Stmt::CompoundStmtClass:
            return translateCompoundStmt(cast<CompoundStmt>(S));
        case Stmt::DeclStmtClass:
            return translateDeclStmt(cast<DeclStmt>(S));
        case Stmt::ReturnStmtClass:
            return translateReturnStmt(cast<ReturnStmt>(S));
        case Stmt::IfStmtClass:
            return translateIfStmt(cast<IfStmt>(S));
        case Stmt::WhileStmtClass:
            return translateWhileStmt(cast<WhileStmt>(S));
        case Stmt::DoStmtClass:
            return translateDoStmt(cast<DoStmt>(S));
        case Stmt::ForStmtClass:
            return translateForStmt(cast<ForStmt>(S));
        case Stmt::SwitchStmtClass:
            return translateSwitchStmt(cast<SwitchStmt>(S));
        case Stmt::CaseStmtClass:
            return translateCaseStmt(cast<CaseStmt>(S));
        case Stmt::DefaultStmtClass:
            return translateDefaultStmt(cast<DefaultStmt>(S));
        case Stmt::BreakStmtClass:
            return translateBreakStmt(cast<BreakStmt>(S));
        case Stmt::ContinueStmtClass:
            return translateContinueStmt(cast<ContinueStmt>(S));
        case Stmt::NullStmtClass:
            return translateNullStmt(cast<NullStmt>(S));
        case Stmt::ExprStmtClass:
            return translateExprStmt(cast<ExprStmt>(S));
        case Stmt::GotoStmtClass:
            return translateGotoStmt(cast<GotoStmt>(S));
        case Stmt::LabelStmtClass:
            return translateLabelStmt(cast<LabelStmt>(S));
        default:
            report_error("Unsupported statement type");
            return nullptr;
    }
}
```

### Specific Translation Functions

#### CompoundStmt (Block)

```cpp
Stmt* translateCompoundStmt(CompoundStmt* CS) {
    std::vector<Stmt*> C_stmts;

    for (Stmt* S : CS->body()) {
        Stmt* C_stmt = translateStmt(S);
        if (C_stmt) {
            C_stmts.push_back(C_stmt);
        }
    }

    return new CompoundStmt(
        context,
        C_stmts,
        CS->getLBracLoc(),
        CS->getRBracLoc()
    );
}
```

#### DeclStmt (Declaration Statement)

```cpp
Stmt* translateDeclStmt(DeclStmt* DS) {
    std::vector<Decl*> C_decls;

    for (Decl* D : DS->decls()) {
        if (VarDecl* VD = dyn_cast<VarDecl>(D)) {
            Decl* C_decl = VariableHandler->translateVarDecl(VD);
            if (C_decl) {
                C_decls.push_back(C_decl);
            }
        } else {
            // Other declarations (unlikely in statement context)
            report_error("Unexpected declaration type in DeclStmt");
        }
    }

    if (C_decls.empty())
        return nullptr;

    return new DeclStmt(
        DeclGroupRef::Create(context, C_decls.data(), C_decls.size()),
        DS->getBeginLoc(),
        DS->getEndLoc()
    );
}
```

#### ReturnStmt

```cpp
Stmt* translateReturnStmt(ReturnStmt* RS) {
    Expr* retValue = RS->getRetValue();
    Expr* C_retValue = nullptr;

    if (retValue) {
        C_retValue = ExpressionHandler->translateExpr(retValue);
    }

    return new ReturnStmt(
        RS->getReturnLoc(),
        C_retValue,
        nullptr // NRVOCandidate
    );
}
```

#### IfStmt

```cpp
Stmt* translateIfStmt(IfStmt* IS) {
    // Translate condition
    Expr* cond = IS->getCond();
    Expr* C_cond = ExpressionHandler->translateExpr(cond);

    // Handle variable declaration in condition (C++17)
    VarDecl* condVar = IS->getConditionVariable();
    Stmt* initStmt = nullptr;
    if (condVar) {
        // int x = foo(); if (x > 0) { ... }
        // Becomes: int x = foo(); if (x > 0) { ... }
        initStmt = new DeclStmt(/* condVar */);
        C_cond = new DeclRefExpr(condVar, ...);
    }

    // Translate then branch
    Stmt* thenStmt = IS->getThen();
    Stmt* C_thenStmt = translateStmt(thenStmt);

    // Translate else branch (if present)
    Stmt* elseStmt = IS->getElse();
    Stmt* C_elseStmt = nullptr;
    if (elseStmt) {
        C_elseStmt = translateStmt(elseStmt);
    }

    // If there's a condition variable, wrap in compound statement
    if (initStmt) {
        std::vector<Stmt*> stmts = {initStmt};
        IfStmt* innerIf = new IfStmt(context, IS->getIfLoc(), false,
                                      nullptr, nullptr, C_cond,
                                      C_thenStmt, IS->getElseLoc(), C_elseStmt);
        stmts.push_back(innerIf);
        return new CompoundStmt(context, stmts, SourceLocation(), SourceLocation());
    }

    return new IfStmt(
        context,
        IS->getIfLoc(),
        false, // isConstexpr
        nullptr, // init
        nullptr, // conditionVariable
        C_cond,
        C_thenStmt,
        IS->getElseLoc(),
        C_elseStmt
    );
}
```

#### WhileStmt

```cpp
Stmt* translateWhileStmt(WhileStmt* WS) {
    Expr* cond = WS->getCond();
    Expr* C_cond = ExpressionHandler->translateExpr(cond);

    Stmt* body = WS->getBody();
    Stmt* C_body = translateStmt(body);

    // Handle condition variable if present
    VarDecl* condVar = WS->getConditionVariable();
    if (condVar) {
        // Similar to IfStmt, extract declaration
        // while (int x = foo()) { ... }
        // Becomes: { int x; while ((x = foo())) { ... } }
    }

    return new WhileStmt(
        context,
        nullptr, // conditionVariable
        C_cond,
        C_body,
        WS->getWhileLoc()
    );
}
```

#### DoStmt

```cpp
Stmt* translateDoStmt(DoStmt* DS) {
    Stmt* body = DS->getBody();
    Stmt* C_body = translateStmt(body);

    Expr* cond = DS->getCond();
    Expr* C_cond = ExpressionHandler->translateExpr(cond);

    return new DoStmt(
        C_body,
        C_cond,
        DS->getDoLoc(),
        DS->getWhileLoc(),
        DS->getRParenLoc()
    );
}
```

#### ForStmt

```cpp
Stmt* translateForStmt(ForStmt* FS) {
    // Translate init statement
    Stmt* init = FS->getInit();
    Stmt* C_init = nullptr;
    if (init) {
        C_init = translateStmt(init);
    }

    // Translate condition
    Expr* cond = FS->getCond();
    Expr* C_cond = nullptr;
    if (cond) {
        C_cond = ExpressionHandler->translateExpr(cond);
    }

    // Translate increment
    Expr* inc = FS->getInc();
    Expr* C_inc = nullptr;
    if (inc) {
        C_inc = ExpressionHandler->translateExpr(inc);
    }

    // Translate body
    Stmt* body = FS->getBody();
    Stmt* C_body = translateStmt(body);

    return new ForStmt(
        context,
        C_init,
        C_cond,
        nullptr, // conditionVariable
        C_inc,
        C_body,
        FS->getForLoc(),
        FS->getLParenLoc(),
        FS->getRParenLoc()
    );
}
```

#### SwitchStmt

```cpp
Stmt* translateSwitchStmt(SwitchStmt* SS) {
    // Translate condition
    Expr* cond = SS->getCond();
    Expr* C_cond = ExpressionHandler->translateExpr(cond);

    // Translate body (contains CaseStmt and DefaultStmt)
    Stmt* body = SS->getBody();
    Stmt* C_body = translateStmt(body);

    return new SwitchStmt(
        context,
        nullptr, // init
        nullptr, // conditionVariable
        C_cond
    );
    // Note: Need to set body after creation
    C_switchStmt->setBody(C_body);
}
```

#### CaseStmt

```cpp
Stmt* translateCaseStmt(CaseStmt* CS) {
    Expr* lhs = CS->getLHS();
    Expr* C_lhs = ExpressionHandler->translateExpr(lhs);

    Expr* rhs = CS->getRHS(); // For case ranges (GNU extension)
    Expr* C_rhs = nullptr;
    if (rhs) {
        C_rhs = ExpressionHandler->translateExpr(rhs);
    }

    Stmt* subStmt = CS->getSubStmt();
    Stmt* C_subStmt = translateStmt(subStmt);

    return new CaseStmt(
        C_lhs,
        C_rhs,
        CS->getCaseLoc(),
        CS->getEllipsisLoc(),
        CS->getColonLoc()
    );
    // Note: Need to set substmt
}
```

#### Simple Statements

```cpp
Stmt* translateBreakStmt(BreakStmt* BS) {
    return new BreakStmt(BS->getBreakLoc());
}

Stmt* translateContinueStmt(ContinueStmt* CS) {
    return new ContinueStmt(CS->getContinueLoc());
}

Stmt* translateNullStmt(NullStmt* NS) {
    return new NullStmt(NS->getSemiLoc());
}

Stmt* translateExprStmt(ExprStmt* ES) {
    Expr* expr = ES->getExpr();
    Expr* C_expr = ExpressionHandler->translateExpr(expr);

    return new ExprStmt(
        C_expr,
        ES->getBeginLoc(),
        ES->getEndLoc()
    );
}
```

## Examples

### Example 1: Compound Statement

**C++ Input:**
```cpp
void foo() {
    int x = 1;
    int y = 2;
    int z = x + y;
}
```

**C Output:**
```c
void foo() {
    int x = 1;
    int y = 2;
    int z = x + y;
}
```

### Example 2: If-Else Statement

**C++ Input:**
```cpp
int abs(int x) {
    if (x < 0) {
        return -x;
    } else {
        return x;
    }
}
```

**C Output:**
```c
int abs(int x) {
    if (x < 0) {
        return -x;
    } else {
        return x;
    }
}
```

### Example 3: While Loop

**C++ Input:**
```cpp
int sum(int n) {
    int total = 0;
    int i = 1;
    while (i <= n) {
        total += i;
        i++;
    }
    return total;
}
```

**C Output:**
```c
int sum(int n) {
    int total = 0;
    int i = 1;
    while (i <= n) {
        total += i;
        i++;
    }
    return total;
}
```

### Example 4: For Loop

**C++ Input:**
```cpp
int factorial(int n) {
    int result = 1;
    for (int i = 1; i <= n; i++) {
        result *= i;
    }
    return result;
}
```

**C Output:**
```c
int factorial(int n) {
    int result = 1;
    for (int i = 1; i <= n; i++) {
        result *= i;
    }
    return result;
}
```

### Example 5: Switch Statement

**C++ Input:**
```cpp
const char* getDayName(int day) {
    switch (day) {
        case 0:
            return "Sunday";
        case 1:
            return "Monday";
        case 2:
            return "Tuesday";
        default:
            return "Unknown";
    }
}
```

**C Output:**
```c
const char* getDayName(int day) {
    switch (day) {
        case 0:
            return "Sunday";
        case 1:
            return "Monday";
        case 2:
            return "Tuesday";
        default:
            return "Unknown";
    }
}
```

### Example 6: Do-While Loop

**C++ Input:**
```cpp
void countdown(int n) {
    do {
        printf("%d\n", n);
        n--;
    } while (n > 0);
}
```

**C Output:**
```c
void countdown(int n) {
    do {
        printf("%d\n", n);
        n--;
    } while (n > 0);
}
```

### Example 7: Nested If Statements

**C++ Input:**
```cpp
int classify(int x) {
    if (x > 0) {
        if (x > 100) {
            return 2;
        } else {
            return 1;
        }
    } else {
        return 0;
    }
}
```

**C Output:**
```c
int classify(int x) {
    if (x > 0) {
        if (x > 100) {
            return 2;
        } else {
            return 1;
        }
    } else {
        return 0;
    }
}
```

### Example 8: Variable Declaration in Condition (C++17)

**C++ Input:**
```cpp
bool process() {
    if (int x = getValue(); x > 0) {
        return true;
    }
    return false;
}
```

**C Output:**
```c
int process() {
    {
        int x = getValue();
        if (x > 0) {
            return 1;
        }
    }
    return 0;
}
```

### Example 9: Break and Continue

**C++ Input:**
```cpp
int findFirst(int arr[], int size, int target) {
    for (int i = 0; i < size; i++) {
        if (arr[i] < 0) {
            continue;
        }
        if (arr[i] == target) {
            return i;
        }
    }
    return -1;
}
```

**C Output:**
```c
int findFirst(int arr[], int size, int target) {
    for (int i = 0; i < size; i++) {
        if (arr[i] < 0) {
            continue;
        }
        if (arr[i] == target) {
            return i;
        }
    }
    return -1;
}
```

### Example 10: Switch with Fallthrough

**C++ Input:**
```cpp
bool isWeekend(int day) {
    switch (day) {
        case 0:
        case 6:
            return true;
        default:
            return false;
    }
}
```

**C Output:**
```c
int isWeekend(int day) {
    switch (day) {
        case 0:
        case 6:
            return 1;
        default:
            return 0;
    }
}
```

## Test Cases

### Unit Tests

1. **test_empty_compound_stmt**
   - Input: `{}`
   - Expected: CompoundStmt with no statements

2. **test_single_statement_block**
   - Input: `{ int x = 1; }`
   - Expected: CompoundStmt with one DeclStmt

3. **test_simple_return**
   - Input: `return 42;`
   - Expected: ReturnStmt with IntegerLiteral

4. **test_return_void**
   - Input: `return;`
   - Expected: ReturnStmt with no expression

5. **test_simple_if**
   - Input: `if (x > 0) { return 1; }`
   - Expected: IfStmt with no else

6. **test_if_else**
   - Input: `if (x > 0) { return 1; } else { return 0; }`
   - Expected: IfStmt with else

7. **test_else_if_chain**
   - Input: `if (x > 0) ... else if (x < 0) ... else ...`
   - Expected: IfStmt with nested IfStmt in else

8. **test_while_loop**
   - Input: `while (x < 10) { x++; }`
   - Expected: WhileStmt

9. **test_do_while_loop**
   - Input: `do { x++; } while (x < 10);`
   - Expected: DoStmt

10. **test_for_loop_full**
    - Input: `for (int i = 0; i < 10; i++) { sum += i; }`
    - Expected: ForStmt with all components

11. **test_for_loop_no_init**
    - Input: `for (; i < 10; i++) { ... }`
    - Expected: ForStmt with null init

12. **test_for_loop_infinite**
    - Input: `for (;;) { ... }`
    - Expected: ForStmt with all nulls

13. **test_switch_basic**
    - Input: `switch (x) { case 1: break; }`
    - Expected: SwitchStmt with CaseStmt

14. **test_switch_with_default**
    - Input: `switch (x) { case 1: break; default: break; }`
    - Expected: SwitchStmt with CaseStmt and DefaultStmt

15. **test_break_stmt**
    - Input: `break;`
    - Expected: BreakStmt

16. **test_continue_stmt**
    - Input: `continue;`
    - Expected: ContinueStmt

17. **test_expr_stmt**
    - Input: `x = 5;`
    - Expected: ExprStmt with BinaryOperator (assignment)

### Integration Tests

1. **test_nested_loops**
   - Input: Nested for loops
   - Expected: Correct ForStmt nesting

2. **test_complex_control_flow**
   - Input: Mix of if, while, for, switch
   - Expected: All statements translated correctly

3. **test_deep_nesting**
   - Input: Deeply nested blocks
   - Expected: Correct CompoundStmt nesting

4. **test_early_return_pattern**
   - Input: Multiple return statements with guards
   - Expected: All ReturnStmts translated

### Edge Cases

1. **test_empty_for_body**
   - Input: `for (int i = 0; i < 10; i++);`
   - Expected: ForStmt with NullStmt body

2. **test_empty_if_body**
   - Input: `if (condition);`
   - Expected: IfStmt with NullStmt

3. **test_switch_no_default**
   - Input: Switch without default case
   - Expected: Valid SwitchStmt

4. **test_case_without_break**
   - Input: Case statement with fallthrough
   - Expected: Fallthrough preserved

5. **test_multiple_breaks**
   - Input: Multiple break statements in nested loops
   - Expected: Each break translated

6. **test_label_and_goto**
   - Input: `label: stmt; goto label;`
   - Expected: LabelStmt and GotoStmt

### Error Cases

1. **test_range_based_for_error**
   - Input: `for (int x : container) { ... }`
   - Expected: Error (not supported in Phase 1)

2. **test_try_catch_error**
   - Input: `try { ... } catch (...) { ... }`
   - Expected: Error (not supported in Phase 1)

## Implementation Notes

### Condition Variable Handling

C++17 allows variable declarations in if/switch/while conditions:
```cpp
if (int x = foo(); x > 0) { ... }
```

In C, we must extract this to a separate statement:
```c
{
    int x = foo();
    if (x > 0) { ... }
}
```

### Statement Ordering

Preserve the exact order of statements in compound statements. This is critical for correctness.

### Scope Management

Each compound statement creates a new scope. Variable declarations are local to that scope. This works the same in C and C++.

### Break and Continue Semantics

Break and continue work identically in C and C++:
- `break`: Exit innermost loop or switch
- `continue`: Skip to next iteration of innermost loop

### Switch Case Fallthrough

Both C and C++ allow case fallthrough (unless [[fallthrough]] is used in C++17). Preserve this behavior.

### Goto Statements

If present in C++ code, goto statements translate directly to C. However, they are rare in modern C++.

## Future Enhancements

### Phase 2: Range-Based For Loops
```cpp
// C++: for (int x : vec) { ... }
// C: for (size_t i = 0; i < vec_size(&vec); i++) {
//        int x = *vec_at(&vec, i);
//        ...
//    }
```

### Phase 3: Exception Handling
```cpp
// C++: try { ... } catch (Exception& e) { ... }
// C: Error code based error handling or setjmp/longjmp
```

### Phase 4: Structured Bindings (C++17)
```cpp
// C++: auto [x, y] = getPoint();
// C: Point p = getPoint(); int x = p.x; int y = p.y;
```

### Phase 5: Coroutines (C++20)
Complex transformation to state machines.

## Related Handlers

- **ExpressionHandler**: Translates all expressions within statements
- **VariableHandler**: Translates variable declarations in DeclStmt
- **FunctionHandler**: Functions contain statement bodies
- **MethodToFunctionTranslator**: Methods contain statement bodies
