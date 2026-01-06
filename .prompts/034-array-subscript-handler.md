<objective>
Implement ArraySubscriptExprHandler for C++ array subscript expressions ([] operator) and integrate it with the dispatcher framework.

Array subscript expressions access array elements using bracket notation: `array[index]`. This is equivalent in both C++ and C, but must be properly translated to handle cases where the array or index involves complex expressions.

This handler translates C++ array subscript expressions to C, ensuring both the base (array) and index expressions are recursively dispatched and correctly translated.
</objective>

<context>
Project: C++ to C Transpiler using Clang AST
Dispatcher Pattern: Chain of Responsibility with recursive dispatch
Reference existing handlers:
@include/dispatch/BinaryOperatorHandler.h
@include/dispatch/MemberExprHandler.h (once created)
@src/dispatch/BinaryOperatorHandler.cpp

Dispatcher framework:
@include/dispatch/CppToCVisitorDispatcher.h

Expression mapping:
@include/mapping/ExprMapper.h

Read @CLAUDE.md for project conventions (TDD, SOLID, etc.).
</context>

<requirements>
1. Create ArraySubscriptExprHandler following the established dispatcher pattern
2. Handler must implement:
   - `static void registerWith(CppToCVisitorDispatcher& dispatcher)`
   - `static bool canHandle(const clang::Expr* E)` - Check for ArraySubscriptExprClass
   - `static void handleArraySubscript(...)` - Translate array access to C
3. Use recursive dispatch pattern:
   - Dispatch base expression (the array being indexed)
   - Dispatch index expression (the subscript)
   - Retrieve both from ExprMapper
   - Create C ArraySubscriptExpr with translated operands
   - Store result in ExprMapper
4. Handle multi-dimensional arrays (nested subscripts)
5. Create comprehensive unit tests (minimum 8 tests)
6. Ensure type safety (array base should be pointer or array type)

Follow TDD: Write failing tests, implement to pass, refactor.
</requirements>

<implementation>
File structure to create:
1. `./include/dispatch/ArraySubscriptExprHandler.h` - Handler interface
2. `./src/dispatch/ArraySubscriptExprHandler.cpp` - Handler implementation
3. `./tests/unit/dispatch/ArraySubscriptExprHandlerDispatcherTest.cpp` - Unit tests

Key implementation details:
- ArraySubscriptExpr represents `base[index]` syntax
- Use `E->getStmtClass() == clang::Stmt::ArraySubscriptExprClass` to detect
- Cast to `clang::ArraySubscriptExpr` to access:
  * `getBase()` or `getLHS()` - Returns the array expression
  * `getIdx()` or `getRHS()` - Returns the index expression
- Both base and index can be complex expressions requiring recursive dispatch
- Create C ArraySubscriptExpr using `clang::ArraySubscriptExpr::Create()`
- Handle multi-dimensional arrays: `array[i][j]` becomes nested ArraySubscriptExpr

Special cases to handle:
- Simple array access: `arr[5]`
- Pointer arithmetic equivalent: `ptr[i]`
- Multi-dimensional: `matrix[row][col]`
- Complex index: `arr[i + j * 2]`
- Complex base: `getArray()[index]`
- Array of pointers: `ptrArray[i]->field`

WHY these patterns matter:
- Recursive dispatch ensures complex expressions in base/index are translated
- ExprMapper deduplication prevents redundant translations
- Proper handling of multi-dimensional arrays ensures correctness
- Type preservation ensures array semantics are maintained

DO NOT:
- Skip dispatching base or index expressions
- Assume simple types (both can be arbitrarily complex)
- Forget ExprMapper.hasCreated() check
- Mix up getLHS/getRHS semantics (base is LHS, index is RHS)
</implementation>

<output>
Create these files:
- `./include/dispatch/ArraySubscriptExprHandler.h` - Handler header with documentation
- `./src/dispatch/ArraySubscriptExprHandler.cpp` - Handler implementation with logging
- `./tests/unit/dispatch/ArraySubscriptExprHandlerDispatcherTest.cpp` - Tests (minimum 8)
- Update `./CMakeLists.txt` if needed for test target
</output>

<verification>
Before declaring complete:
1. Code compiles without errors or warnings
2. Run tests: `ctest -R ArraySubscriptExprHandlerDispatcherTest --output-on-failure`
3. All tests pass (100%)
4. Test single and multi-dimensional array access
5. Test complex base and index expressions
6. Verify debug output is informative
7. Check SOLID principles compliance
</verification>

<success_criteria>
- ArraySubscriptExprHandler.h created with full documentation
- ArraySubscriptExprHandler.cpp implements recursive dispatch correctly
- Unit tests cover:
  * Handler registration
  * Simple array access (arr[5])
  * Variable index (arr[i])
  * Multi-dimensional access (matrix[i][j])
  * Complex index expression (arr[i+j])
  * Complex base expression (getArray()[i])
  * Integration with ExprMapper
  * Predicate correctness
- All tests pass (100%)
- Code compiles cleanly
- Handler ready for integration
</success_criteria>
