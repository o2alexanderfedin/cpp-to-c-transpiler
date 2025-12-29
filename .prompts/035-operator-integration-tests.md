<objective>
Create comprehensive integration tests for ALL operator handlers (existing and new) to ensure they work correctly together in the dispatcher framework.

This verifies that:
1. All operator handlers are properly registered with the dispatcher
2. Complex expressions combining multiple operators are translated correctly
3. Recursive dispatch works correctly for nested operator expressions
4. All operators integrate seamlessly with other expression handlers (literals, variables, etc.)
5. No handlers are missing from the registration chain

This is the final verification step after implementing the new operator handlers.
</objective>

<context>
Existing operator handlers:
@include/dispatch/BinaryOperatorHandler.h - Arithmetic, comparison, logical, bitwise, assignment
@include/dispatch/UnaryOperatorHandler.h - Unary operators, increment/decrement
@src/dispatch/BinaryOperatorHandler.cpp
@src/dispatch/UnaryOperatorHandler.cpp

New operator handlers (should exist before running this prompt):
@include/dispatch/CommaOperatorHandler.h
@include/dispatch/MemberExprHandler.h
@include/dispatch/ArraySubscriptExprHandler.h

Integration test reference:
@tests/integration/FunctionTranslationIntegrationTest.cpp

Read @CLAUDE.md for project conventions and testing standards.
</context>

<requirements>
1. Create comprehensive integration test file that verifies ALL operators work together
2. Test must register ALL operator handlers with dispatcher:
   - BinaryOperatorHandler (existing)
   - UnaryOperatorHandler (existing)
   - CommaOperatorHandler (new)
   - MemberExprHandler (new)
   - ArraySubscriptExprHandler (new)
   - Plus supporting handlers: LiteralHandler, DeclRefExprHandler, ImplicitCastExprHandler, ParenExprHandler
3. Create test cases for complex expressions combining multiple operators:
   - Arithmetic with member access: `obj.x + obj.y * 2`
   - Array access with operators: `arr[i++] + arr[j--]`
   - Comma operator in complex context: `for (i=0, j=10; i<j; i++, j--)`
   - Nested member and array: `objects[i].field->data[j]`
   - All operators in one expression: `(arr[i++].ptr->value += 5, result)`
4. Verify each operator handler's registration is successful
5. Test that unregistered operators fail gracefully with clear error messages
6. Measure and report test coverage for operator handlers

Follow testing best practices: Clear test names, isolated test cases, comprehensive coverage.
</requirements>

<implementation>
File to create:
`./tests/integration/OperatorIntegrationTest.cpp`

Test structure:
1. Helper function `registerAllOperatorHandlers(dispatcher)` that registers all handlers in correct order
2. Test fixture with common setup (dispatcher, mappers, contexts)
3. Individual test cases for each operator category:
   - TEST: AllOperatorHandlersRegistered - Verify registration succeeds
   - TEST: ArithmeticOperatorsIntegration - Test +, -, *, /, %
   - TEST: CompoundAssignmentIntegration - Test +=, -=, *=, /=, %=
   - TEST: IncrementDecrementIntegration - Test ++, -- (prefix and postfix)
   - TEST: MemberAccessIntegration - Test . and ->
   - TEST: ArraySubscriptIntegration - Test []
   - TEST: CommaOperatorIntegration - Test ,
   - TEST: ComplexNestedExpression - Test combination of all
   - TEST: ErrorHandlingUnregisteredOperator - Verify graceful failure
4. Use Google Test framework (existing pattern)
5. Add proper assertions and error messages

WHY this matters:
- Integration tests catch issues that unit tests miss (handler interactions)
- Ensures dispatcher correctly chains handlers
- Verifies no handlers are accidentally omitted from registration
- Provides regression safety as code evolves
- Documents expected behavior through executable tests

Key implementation patterns:
- Use `buildAST()` helper to parse C++ code snippets
- Use `findNode<T>()` template helper to locate specific AST nodes
- Verify `dispatcher.dispatch()` returns true for handled expressions
- Check `ExprMapper.getCreated()` returns non-null translated expressions
- Compare translated expression types and structure
</implementation>

<output>
Create this file:
- `./tests/integration/OperatorIntegrationTest.cpp` - Comprehensive integration tests

Update if needed:
- `./CMakeLists.txt` - Add OperatorIntegrationTest target
</output>

<verification>
Before declaring complete:
1. Code compiles without errors or warnings
2. Run integration tests: `ctest -R OperatorIntegrationTest --output-on-failure`
3. All tests pass (100%)
4. Test coverage includes:
   - At least 9 test cases
   - All operator handlers verified
   - Complex nested expressions tested
   - Error handling verified
5. Debug output clearly shows which handlers are invoked
6. Test execution time is reasonable (< 5 seconds for all tests)
7. No memory leaks (verify with valgrind if available)
</verification>

<success_criteria>
- OperatorIntegrationTest.cpp created with comprehensive test coverage
- Minimum 9 test cases implemented
- All operator handlers registered and verified:
  * BinaryOperatorHandler ✓
  * UnaryOperatorHandler ✓
  * CommaOperatorHandler ✓
  * MemberExprHandler ✓
  * ArraySubscriptExprHandler ✓
- Complex expression tests pass:
  * Nested operators work correctly
  * Multi-operator expressions translate properly
  * Error handling works as expected
- All tests pass (100%)
- Code compiles cleanly
- CMakeLists.txt updated if needed
- Integration test can serve as documentation for operator handler usage
</success_criteria>
