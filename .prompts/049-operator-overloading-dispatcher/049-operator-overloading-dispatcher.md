<objective>
Integrate C++ operator overloading (CXXOperatorCallExpr) with the dispatcher framework by creating a CXXOperatorCallExprHandler that delegates to SpecialOperatorTranslator.

C++ operator overloading (like `a + b` where `operator+` is user-defined) translates to function calls in C. This handler detects CXXOperatorCallExpr nodes and translates them to C CallExpr nodes using the existing SpecialOperatorTranslator infrastructure.

WHY this matters:
- Operator overloading is a fundamental C++ feature used in real-world code
- SpecialOperatorTranslator already exists but is NOT integrated with the dispatcher
- Integration ensures operator overloading works seamlessly with other expression handlers
- Enables complex expressions like `obj[i] + vec.operator[](j)` to translate correctly
</objective>

<context>
Project: C++ to C Transpiler using Clang AST
Dispatcher Pattern: Chain of Responsibility with recursive dispatch

Existing infrastructure:
@include/SpecialOperatorTranslator.h - Handles 12 special operators (already implemented)
@src/SpecialOperatorTranslator.cpp - Translation logic (already implemented)
@tests/unit/operators/OperatorOverloadingTest.cpp - Detection tests (59 tests, all passing)

Existing dispatcher handlers:
@include/dispatch/BinaryOperatorHandler.h - Built-in binary operators
@include/dispatch/UnaryOperatorHandler.h - Built-in unary operators
@include/dispatch/CommaOperatorHandler.h - Built-in comma operator
@include/dispatch/MemberExprHandler.h - Member access
@include/dispatch/ArraySubscriptExprHandler.h - Array subscript

Dispatcher framework:
@include/dispatch/CppToCVisitorDispatcher.h
@src/dispatch/CppToCVisitorDispatcher.cpp

Expression mapping:
@include/mapping/ExprMapper.h

Read @CLAUDE.md for project conventions (TDD, SOLID, etc.).
</context>

<requirements>
1. Create CXXOperatorCallExprHandler following the dispatcher pattern
2. Handler must implement:
   - `static void registerWith(CppToCVisitorDispatcher& dispatcher)`
   - `static bool canHandle(const clang::Expr* E)` - Check for CXXOperatorCallExprClass
   - `static void handleOperatorCall(...)` - Translate using SpecialOperatorTranslator
3. Use SpecialOperatorTranslator as the underlying implementation:
   - Call `SpecialOperatorTranslator::transformCall()` to get C CallExpr
   - Store result in ExprMapper
4. Handle all 12 special operators:
   - operator[] (instance subscript)
   - operator() (function call/functor)
   - operator-> (smart pointer arrow)
   - operator* (smart pointer dereference)
   - operator<< (stream output)
   - operator>> (stream input)
   - operator T() (conversion operators)
   - operator bool() (bool conversion)
   - operator= (copy and move assignment)
   - operator& (address-of, rare)
   - operator, (comma, rare)
5. Distinguish from built-in operators:
   - Built-in operators: Handled by BinaryOperatorHandler, UnaryOperatorHandler
   - Overloaded operators: Handled by this handler via CXXOperatorCallExpr
6. Create comprehensive unit tests (minimum 12 tests)
7. Integrate with existing SpecialOperatorTranslator infrastructure

Follow TDD: Write failing tests, implement to pass, refactor.
</requirements>

<implementation>
File structure to create:
1. `./include/dispatch/CXXOperatorCallExprHandler.h` - Handler interface
2. `./src/dispatch/CXXOperatorCallExprHandler.cpp` - Handler implementation
3. `./tests/unit/dispatch/CXXOperatorCallExprHandlerDispatcherTest.cpp` - Unit tests

Key implementation details:
- CXXOperatorCallExpr represents calls to overloaded operators: `obj.operator+(other)`
- Use `E->getStmtClass() == clang::Stmt::CXXOperatorCallExprClass` to detect
- Cast to `clang::CXXOperatorCallExpr` to access:
  * `getOperator()` - Returns OverloadedOperatorKind (OO_Plus, OO_Subscript, etc.)
  * `getCalleeDecl()` - Returns the operator method being called
  * `getNumArgs()` - Number of arguments (includes implicit `this`)
  * `getArg(i)` - Access individual arguments
- Use SpecialOperatorTranslator::transformCall() to translate to C CallExpr
- Store translated CallExpr in ExprMapper
- Handle argument dispatch:
  * CXXOperatorCallExpr includes implicit `this` as first argument
  * Dispatch all arguments recursively through dispatcher
  * SpecialOperatorTranslator handles C function call construction

Special cases to handle:
- Instance operators: `arr[5]`, `obj()`, `ptr->field`, `*ptr`
- Stream operators: `cout << obj`, `cin >> obj`
- Conversion operators: `(int)obj`, `if (obj)` (uses MaterializeTemporaryExpr wrapper)
- Assignment operators: `a = b` (copy), `a = std::move(b)` (move)
- Rare operators: `&obj`, `(a, b)`

WHY these patterns matter:
- CXXOperatorCallExpr is distinct from BinaryOperator (built-in vs overloaded)
- Recursive dispatch ensures complex operator expressions translate correctly
- SpecialOperatorTranslator integration reuses existing, tested translation logic
- ExprMapper prevents duplicate translations

DO NOT:
- Confuse CXXOperatorCallExpr (overloaded) with BinaryOperator (built-in)
- Re-implement SpecialOperatorTranslator logic (reuse existing infrastructure)
- Skip dispatching arguments (causes incomplete translation)
- Forget ExprMapper.hasCreated() check (causes duplication)
</implementation>

<output>
Create these files:
- `./include/dispatch/CXXOperatorCallExprHandler.h` - Handler header with documentation
- `./src/dispatch/CXXOperatorCallExprHandler.cpp` - Handler implementation with logging
- `./tests/unit/dispatch/CXXOperatorCallExprHandlerDispatcherTest.cpp` - Tests (minimum 12)
- Update `./CMakeLists.txt` if needed for test target

Integration requirements:
- Handler must be registered in CppToCVisitorDispatcher::registerDefaultHandlers()
- Handler must work with existing SpecialOperatorTranslator
- Handler must integrate with ExprMapper
</output>

<verification>
Before declaring complete:
1. Code compiles without errors or warnings
2. Run tests: `ctest -R CXXOperatorCallExprHandlerDispatcherTest --output-on-failure`
3. All tests pass (100%)
4. Test all 12 special operator categories:
   - Instance subscript (operator[])
   - Instance call (operator())
   - Smart pointer operators (operator->, operator*)
   - Stream operators (operator<<, operator>>)
   - Conversion operators (operator T(), operator bool())
   - Assignment operators (operator=)
   - Rare operators (operator&, operator,)
5. Verify SpecialOperatorTranslator integration works correctly
6. Check debug output is informative
7. Verify SOLID principles compliance
</verification>

<success_criteria>
- CXXOperatorCallExprHandler.h created with full documentation
- CXXOperatorCallExprHandler.cpp implements delegation to SpecialOperatorTranslator
- Unit tests cover:
  * Handler registration
  * All 12 special operator categories
  * SpecialOperatorTranslator integration
  * ExprMapper integration
  * Predicate correctness (matches only CXXOperatorCallExpr)
  * Distinguish from built-in operators
  * Complex nested operator expressions
- All tests pass (100%)
- Code compiles cleanly
- Handler ready for dispatcher integration
- Integration with existing operator infrastructure verified
</success_criteria>
