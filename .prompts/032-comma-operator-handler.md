<objective>
Implement CommaOperatorHandler for C++ comma expressions and integrate it with the dispatcher framework.

The comma operator (,) evaluates multiple expressions sequentially and returns the value of the last expression. This is used in contexts like `for (int i=0, j=10; i<j; i++, j--)` or standalone expressions like `(a=1, b=2, c=3)`.

This handler follows the established Chain of Responsibility pattern used by BinaryOperatorHandler and UnaryOperatorHandler, ensuring consistency with the existing architecture.
</objective>

<context>
Project: C++ to C Transpiler using Clang AST
Dispatcher Pattern: Chain of Responsibility with recursive dispatch
Reference existing handlers:
@include/dispatch/BinaryOperatorHandler.h
@include/dispatch/UnaryOperatorHandler.h
@src/dispatch/BinaryOperatorHandler.cpp
@src/dispatch/UnaryOperatorHandler.cpp

The dispatcher framework is in:
@include/dispatch/CppToCVisitorDispatcher.h
@src/dispatch/CppToCVisitorDispatcher.cpp

Expression mapping utility:
@include/mapping/ExprMapper.h

Read @CLAUDE.md for project conventions and development process (TDD, SOLID principles).
</context>

<requirements>
1. Create CommaOperatorHandler following the exact pattern of existing operator handlers
2. Handler must implement:
   - `static void registerWith(CppToCVisitorDispatcher& dispatcher)`
   - `static bool canHandle(const clang::Expr* E)` - Check for BinaryOperatorClass with BO_Comma opcode
   - `static void handleCommaOperator(...)` - Translate comma expression to C
3. Use recursive dispatch pattern:
   - Dispatch LHS subexpression through dispatcher
   - Dispatch RHS subexpression through dispatcher
   - Retrieve translated operands from ExprMapper
   - Create C BinaryOperator with BO_Comma opcode
   - Store result in ExprMapper
4. Create comprehensive unit tests following the pattern of BinaryOperatorHandlerDispatcherTest
5. Ensure handler is registered in integration tests alongside other expression handlers

Follow TDD: Write failing tests first, implement to pass, then refactor.
</requirements>

<implementation>
File structure to create:
1. `./include/dispatch/CommaOperatorHandler.h` - Handler interface
2. `./src/dispatch/CommaOperatorHandler.cpp` - Handler implementation
3. `./tests/unit/dispatch/CommaOperatorHandlerDispatcherTest.cpp` - Unit tests

Key implementation details:
- Comma operator is a BinaryOperator with opcode BO_Comma
- Use `E->getStmtClass() == clang::Stmt::BinaryOperatorClass` to check class
- Use `llvm::cast<clang::BinaryOperator>(E)->getOpcode() == clang::BinaryOperator::BO_Comma` for precise matching
- Follow the exact error handling and logging pattern from BinaryOperatorHandler
- Include proper assertions and debug output
- Check ExprMapper.hasCreated() to avoid re-processing
- Use const_cast when calling dispatcher (dispatcher interface requires non-const)

WHY these patterns matter:
- Recursive dispatch ensures nested comma expressions are handled correctly
- ExprMapper deduplication prevents duplicate AST nodes and ensures referential integrity
- Consistent error handling ensures debugging is straightforward
- Following existing patterns makes the codebase maintainable

DO NOT:
- Mix ASTContexts (always use cppASTContext for C++ nodes, cASTContext for C nodes)
- Create handlers that don't follow the established pattern
- Skip unit tests - they verify correctness and prevent regressions
</implementation>

<output>
Create these files with relative paths:
- `./include/dispatch/CommaOperatorHandler.h` - Handler header with full documentation
- `./src/dispatch/CommaOperatorHandler.cpp` - Handler implementation with debug logging
- `./tests/unit/dispatch/CommaOperatorHandlerDispatcherTest.cpp` - Comprehensive unit tests (minimum 6 tests)
- Update `./CMakeLists.txt` to add CommaOperatorHandlerDispatcherTest target if needed
</output>

<verification>
Before declaring complete, verify:
1. Code compiles without errors or warnings
2. Run unit tests: `ctest -R CommaOperatorHandlerDispatcherTest --output-on-failure`
3. All tests pass (100% pass rate)
4. Handler follows exact pattern of BinaryOperatorHandler (same structure, same error handling)
5. Debug output is present and follows existing format
6. Code adheres to SOLID principles (verify Single Responsibility)
</verification>

<success_criteria>
- CommaOperatorHandler.h created with proper documentation
- CommaOperatorHandler.cpp implements recursive dispatch pattern correctly
- Unit tests created with minimum 6 test cases covering:
  * Handler registration
  * Basic comma expression (a, b)
  * Nested comma expressions ((a, b), c)
  * Comma in for-loop initialization
  * Integration with ExprMapper
  * Predicate correctness
- All unit tests pass (100%)
- Code compiles cleanly
- Handler is ready for integration with dispatcher
</success_criteria>
