<objective>
Implement comprehensive expression handlers following the Chain of Responsibility dispatcher pattern with recursive subexpression handling.

Expression handlers will process C++ expressions and translate them to C expressions, with ALL subexpressions dispatched recursively through the dispatcher (never translated inline).

Scope: All basic expression types
- Literals: IntegerLiteral, FloatingLiteral, StringLiteral, CharacterLiteral, CXXBoolLiteralExpr
- Variable references: DeclRefExpr
- Binary operators: BinaryOperator (+, -, *, /, %, ==, !=, <, >, <=, >=, &&, ||, etc.)
- Unary operators: UnaryOperator (!, -, ++, --, *, &, etc.)
- Additional common expressions as needed

This is a critical architectural component - expression handlers enable function body translation, which completes the basic transpilation pipeline.
</objective>

<context>
Project: C++ to C Transpiler using Clang AST
Architecture: Chain of Responsibility pattern with CppToCVisitorDispatcher

Recent work completed:
- TypeHandler: Dispatches types, stores in TypeMapper (@src/dispatch/TypeHandler.cpp)
- FunctionHandler: Dispatches parameters and types (@src/dispatch/FunctionHandler.cpp)
- ParameterHandler: Dispatches types (@src/dispatch/ParameterHandler.cpp)
- ReturnStmtHandler: Dispatches expressions (ready for integration) (@src/dispatch/ReturnStmtHandler.cpp)

Examine these files to understand the established pattern:
@src/dispatch/TypeHandler.cpp
@src/dispatch/TypeHandler.h
@include/dispatch/CppToCVisitorDispatcher.h
@src/mapping/TypeMapper.cpp
@include/mapping/TypeMapper.h

Key architectural principles:
- ALL child nodes must be dispatched through dispatcher (NEVER inline translation)
- Handlers store mappings in dedicated mappers (ExprMapper for expressions)
- Parent handlers retrieve child nodes from mappers
- Each handler has ONE responsibility (Single Responsibility Principle)
- Recursive dispatch for tree structures (expressions contain subexpressions)
</context>

<requirements>

1. **Create ExprMapper for expression mappings**:
   - Header: `include/mapping/ExprMapper.h`
   - Implementation: `src/mapping/ExprMapper.cpp`
   - Follow exact pattern from TypeMapper/DeclMapper
   - Methods: `setCreatedExpr(cppExpr, cExpr)`, `getCreatedExpr(cppExpr)`
   - Store: `std::map<const clang::Expr*, clang::Expr*>`

2. **Update CppToCVisitorDispatcher**:
   - Add `ExprMapper& exprMapper` member
   - Add to constructor parameters
   - Add `getExprMapper()` accessor method

3. **Create Expression Handlers** (separate handler for each expression type):

   **LiteralHandler** (handles all literal types):
   - Header: `include/dispatch/LiteralHandler.h`
   - Implementation: `src/dispatch/LiteralHandler.cpp`
   - Predicate: Match IntegerLiteral, FloatingLiteral, StringLiteral, CharacterLiteral, CXXBoolLiteralExpr
   - Handler: Create C literal nodes, store in ExprMapper
   - No subexpressions - simplest case

   **DeclRefExprHandler**:
   - Header: `include/dispatch/DeclRefExprHandler.h`
   - Implementation: `src/dispatch/DeclRefExprHandler.cpp`
   - Predicate: Match DeclRefExpr exactly
   - Handler: Create C DeclRefExpr, store in ExprMapper
   - No subexpressions

   **BinaryOperatorHandler**:
   - Header: `include/dispatch/BinaryOperatorHandler.h`
   - Implementation: `src/dispatch/BinaryOperatorHandler.cpp`
   - Predicate: Match BinaryOperator exactly
   - Handler:
     - Extract LHS and RHS subexpressions
     - **CRITICAL**: Dispatch LHS via dispatcher (recursive)
     - **CRITICAL**: Dispatch RHS via dispatcher (recursive)
     - Retrieve translated LHS from ExprMapper
     - Retrieve translated RHS from ExprMapper
     - Create C BinaryOperator with translated operands
     - Store in ExprMapper

   **UnaryOperatorHandler**:
   - Header: `include/dispatch/UnaryOperatorHandler.h`
   - Implementation: `src/dispatch/UnaryOperatorHandler.cpp`
   - Predicate: Match UnaryOperator exactly
   - Handler:
     - Extract operand subexpression
     - **CRITICAL**: Dispatch operand via dispatcher (recursive)
     - Retrieve translated operand from ExprMapper
     - Create C UnaryOperator with translated operand
     - Store in ExprMapper

4. **Recursive Dispatch Pattern** (CRITICAL - follow this exactly):
   ```cpp
   // Example from BinaryOperatorHandler
   const Expr* cppLHS = binaryOp->getLHS();
   const Expr* cppRHS = binaryOp->getRHS();

   // Dispatch LHS (recursive - may dispatch to another BinaryOperator, etc.)
   bool lhsHandled = disp.dispatch(cppASTContext, cASTContext,
                                    const_cast<Expr*>(cppLHS));

   // Retrieve translated LHS from ExprMapper
   ExprMapper& exprMapper = disp.getExprMapper();
   Expr* cLHS = exprMapper.getCreatedExpr(cppLHS);

   // Same for RHS
   bool rhsHandled = disp.dispatch(cppASTContext, cASTContext,
                                    const_cast<Expr*>(cppRHS));
   Expr* cRHS = exprMapper.getCreatedExpr(cppRHS);

   // Create C BinaryOperator with translated operands
   BinaryOperator* cBinOp = BinaryOperator::Create(..., cLHS, cRHS, ...);

   // Store in ExprMapper for parent handler retrieval
   exprMapper.setCreatedExpr(binaryOp, cBinOp);
   ```

5. **Update ReturnStmtHandler**:
   - Remove TODO comments
   - Use ExprMapper to retrieve translated expressions
   - Replace fallback with proper ExprMapper.getCreatedExpr() call

6. **Integration**:
   - Add all handlers to CMakeLists.txt
   - Update dispatcher instantiations in all tests

7. **Comprehensive Testing** (CRITICAL):
   Create test files for EACH handler:
   - `tests/unit/dispatch/LiteralHandlerDispatcherTest.cpp`
   - `tests/unit/dispatch/DeclRefExprHandlerDispatcherTest.cpp`
   - `tests/unit/dispatch/BinaryOperatorHandlerDispatcherTest.cpp`
   - `tests/unit/dispatch/UnaryOperatorHandlerDispatcherTest.cpp`

   Each test file must include:
   - Registration test
   - Basic translation test
   - Recursive dispatch test (for operators)
   - Multiple expression test
   - Integration test with ReturnStmtHandler

   Exhaustive test coverage:
   - All literal types (int, float, string, char, bool)
   - All binary operators (+, -, *, /, %, ==, !=, <, >, <=, >=, &&, ||, &, |, ^, <<, >>)
   - All unary operators (!, -, ++, --, *, &, ~)
   - Nested expressions (e.g., `a + (b * c)`)
   - Deep recursion (e.g., `((a + b) * (c - d)) / (e + f)`)
   - Mixed types (e.g., `(x > 5) && (y < 10)`)

</requirements>

<implementation>

**Why recursive dispatch matters:**
- Expressions form tree structures (AST)
- Binary operators have two subexpressions
- Unary operators have one subexpression
- Subexpressions can be ANY expression type (literals, operators, variables, etc.)
- Handler must NEVER translate subexpressions inline
- Handler must ALWAYS dispatch subexpressions to dispatcher
- Dispatcher routes to appropriate handler (may be same type, may be different)
- This enables arbitrary expression nesting: `a + (b * (c - d))`

**Example recursive flow:**
```
ReturnStmt handler dispatches: a + b
  ↓
BinaryOperator(+) handler dispatches LHS: a
  ↓
DeclRefExpr handler creates C DeclRefExpr for 'a', stores in ExprMapper
  ← returns
BinaryOperator(+) retrieves 'a' from ExprMapper
  ↓
BinaryOperator(+) handler dispatches RHS: b
  ↓
DeclRefExpr handler creates C DeclRefExpr for 'b', stores in ExprMapper
  ← returns
BinaryOperator(+) retrieves 'b' from ExprMapper
  ↓
BinaryOperator(+) creates C BinaryOperator(cA, cB), stores in ExprMapper
  ← returns
ReturnStmt retrieves result from ExprMapper
```

**Pattern to follow** (from TypeHandler/FunctionHandler):
1. Static registerWith() that calls `dispatcher.addHandler(predicate, visitor)`
2. Static canHandle() using exact type matching with `E->getStmtClass()`
3. Static handle method that:
   - Asserts preconditions
   - Casts to specific type
   - Extracts subexpressions
   - **DISPATCHES each subexpression via dispatcher** (NEVER inline translation)
   - Retrieves translated subexpressions from ExprMapper
   - Creates C expression node with translated subexpressions
   - Stores in ExprMapper

**What to avoid and WHY:**
- Do NOT translate subexpressions inline (violates Chain of Responsibility)
- Do NOT use isa<> for predicate (too broad - use exact getStmtClass() check)
- Do NOT create instance methods (violates established static pattern)
- Do NOT skip ExprMapper storage (parent handlers need to retrieve results)
- Do NOT forget to dispatch ALL subexpressions (incomplete translation)

</implementation>

<research>
Before implementing, examine:

1. **Dispatcher's Expr handling**:
   - Read @include/dispatch/CppToCVisitorDispatcher.h lines 81-83 (ExprPredicate/ExprVisitor typedefs)
   - Understand that Expr derives from Stmt, so handlers use Expr* or Stmt*

2. **Clang Expression API**:
   - IntegerLiteral: getValue(), getType()
   - BinaryOperator: getLHS(), getRHS(), getOpcode()
   - UnaryOperator: getSubExpr(), getOpcode()
   - DeclRefExpr: getDecl()

3. **Existing mapper patterns**:
   - Read @src/mapping/TypeMapper.cpp for exact pattern
   - Read @src/mapping/DeclMapper.cpp for map structure

4. **Test patterns**:
   - Read @tests/unit/dispatch/TypeHandlerDispatcherTest.cpp for comprehensive test structure
   - Adapt for Expr nodes instead of Type/Decl nodes

</research>

<output>
Create the following files:

1. `./include/mapping/ExprMapper.h` - Expression mapping storage
2. `./src/mapping/ExprMapper.cpp` - Implementation
3. `./include/dispatch/LiteralHandler.h` - Literal handler interface
4. `./src/dispatch/LiteralHandler.cpp` - Implementation
5. `./include/dispatch/DeclRefExprHandler.h` - Variable reference handler interface
6. `./src/dispatch/DeclRefExprHandler.cpp` - Implementation
7. `./include/dispatch/BinaryOperatorHandler.h` - Binary operator handler interface
8. `./src/dispatch/BinaryOperatorHandler.cpp` - Implementation with recursive dispatch
9. `./include/dispatch/UnaryOperatorHandler.h` - Unary operator handler interface
10. `./src/dispatch/UnaryOperatorHandler.cpp` - Implementation with recursive dispatch
11. `./tests/unit/dispatch/LiteralHandlerDispatcherTest.cpp` - Exhaustive literal tests
12. `./tests/unit/dispatch/DeclRefExprHandlerDispatcherTest.cpp` - Variable reference tests
13. `./tests/unit/dispatch/BinaryOperatorHandlerDispatcherTest.cpp` - Exhaustive operator tests with recursion
14. `./tests/unit/dispatch/UnaryOperatorHandlerDispatcherTest.cpp` - Exhaustive unary tests with recursion
15. Update `./include/dispatch/CppToCVisitorDispatcher.h` - Add ExprMapper member
16. Update `./src/dispatch/ReturnStmtHandler.cpp` - Use ExprMapper properly
17. Update `./CMakeLists.txt` - Add all new sources and tests

</output>

<verification>
Before declaring complete, verify:

1. **All handlers compile**: Run cmake --build for each handler test
2. **All tests pass**: Run each test executable - expect 100% pass rate
3. **Exhaustive coverage**: Each test file has 8+ test cases covering all variants
4. **Recursive dispatch works**: Test nested expressions like `(a + b) * (c - d)`
5. **ExprMapper integration**: Verify all handlers store AND retrieve from mapper
6. **ReturnStmtHandler integration**: Test that return statements work with expressions
7. **Pattern consistency**: Compare handlers side-by-side with TypeHandler
8. **SOLID compliance**:
   - Single Responsibility: Each handler handles ONE expression type
   - Chain of Responsibility: All subexpressions dispatched via dispatcher
   - DRY: No duplicate recursive dispatch logic
   - ExprMapper separation: Translation vs storage

Run integration test:
```cpp
int compute(int a, int b) {
    return (a + b) * 2 - 1;
}
```

Should translate to:
```c
int compute(int a, int b) {
    return (a + b) * 2 - 1;  // Phase 1: structure only, same expression
}
```

Verify dispatch chain:
- FunctionHandler dispatches parameters
- ReturnStmtHandler dispatches return value expression
- BinaryOperator(-) dispatches LHS: (a + b) * 2
- BinaryOperator(*) dispatches LHS: (a + b)
- BinaryOperator(+) dispatches LHS: a (DeclRefExpr)
- BinaryOperator(+) dispatches RHS: b (DeclRefExpr)
- BinaryOperator(*) dispatches RHS: 2 (IntegerLiteral)
- BinaryOperator(-) dispatches RHS: 1 (IntegerLiteral)

Every dispatch stores in ExprMapper, parent retrieves.

</verification>

<success_criteria>
- ExprMapper created following TypeMapper/DeclMapper pattern
- CppToCVisitorDispatcher updated with ExprMapper member
- LiteralHandler handles all 5 literal types, stores in ExprMapper
- DeclRefExprHandler handles variable references, stores in ExprMapper
- BinaryOperatorHandler dispatches LHS/RHS recursively, stores in ExprMapper
- UnaryOperatorHandler dispatches operand recursively, stores in ExprMapper
- ReturnStmtHandler updated to use ExprMapper (no more fallback/TODO)
- CMakeLists.txt updated with all sources and tests
- 4 test files created with 8+ tests each (32+ total tests)
- All tests pass (100% success rate)
- Recursive dispatch verified with nested expressions
- Integration test with full function translation passes
- Pattern-consistent with TypeHandler/FunctionHandler (verify side-by-side)
- Zero inline translation - all subexpressions dispatched via dispatcher
</success_criteria>
