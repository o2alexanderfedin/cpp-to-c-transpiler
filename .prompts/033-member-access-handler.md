<objective>
Implement MemberExprHandler for C++ member access expressions (both . and -> operators) and integrate it with the dispatcher framework.

Member access expressions access fields or methods of objects and pointers. In C++, `obj.field` accesses a member of an object, while `ptr->field` accesses a member through a pointer. In C, classes become structs and methods become functions, but field access remains the same.

This handler must translate C++ member access to equivalent C struct field access, handling both direct (.) and indirect (->) access patterns.
</objective>

<context>
Project: C++ to C Transpiler using Clang AST
Dispatcher Pattern: Chain of Responsibility with recursive dispatch
Reference existing handlers:
@include/dispatch/BinaryOperatorHandler.h
@include/dispatch/DeclRefExprHandler.h
@src/dispatch/BinaryOperatorHandler.cpp

The dispatcher framework:
@include/dispatch/CppToCVisitorDispatcher.h

Expression mapping utility:
@include/mapping/ExprMapper.h

Read @CLAUDE.md for project conventions and TDD process.
</context>

<requirements>
1. Create MemberExprHandler following the established pattern
2. Handler must implement:
   - `static void registerWith(CppToCVisitorDispatcher& dispatcher)`
   - `static bool canHandle(const clang::Expr* E)` - Check for MemberExprClass
   - `static void handleMemberExpr(...)` - Translate member access to C
3. Use recursive dispatch pattern:
   - Dispatch base expression (the object/pointer being accessed)
   - Retrieve translated base from ExprMapper
   - Create C MemberExpr with translated base
   - Preserve arrow vs dot distinction (important for -> in C)
   - Store result in ExprMapper
4. Handle both implicit and explicit member access
5. Create comprehensive unit tests (minimum 8 tests)
6. Ensure handler works with DeclMapper for member field lookups

Follow TDD: Write tests first, implement to pass, refactor.
</requirements>

<implementation>
File structure to create:
1. `./include/dispatch/MemberExprHandler.h` - Handler interface
2. `./src/dispatch/MemberExprHandler.cpp` - Handler implementation
3. `./tests/unit/dispatch/MemberExprHandlerDispatcherTest.cpp` - Unit tests

Key implementation details:
- MemberExpr represents both obj.field and ptr->field
- Use `E->getStmtClass() == clang::Stmt::MemberExprClass` to detect
- Cast to `clang::MemberExpr` to access:
  * `getBase()` - Returns the base expression (obj or ptr)
  * `getMemberDecl()` - Returns the FieldDecl being accessed
  * `isArrow()` - Returns true for ->, false for .
- Dispatch base expression recursively through dispatcher
- Create C MemberExpr using `clang::MemberExpr::Create()`
- Preserve the arrow flag (critical for pointer vs object access in C)

Special cases to handle:
- Nested member access: `obj.inner.field`
- Member access on method call results: `getObject().field`
- Member access through pointer: `ptr->field`
- Implicit `this->field` access (base is CXXThisExpr)

WHY these patterns matter:
- Recursive dispatch handles nested member access correctly
- Preserving arrow vs dot ensures correct C syntax (obj.field vs ptr->field)
- DeclMapper integration ensures field names are consistent with struct definitions
- ExprMapper prevents duplicate translation of base expressions

DO NOT:
- Change arrow to dot or vice versa (must preserve pointer semantics)
- Skip dispatching the base expression (causes incomplete translation)
- Forget to check ExprMapper.hasCreated() (causes duplication)
</implementation>

<output>
Create these files:
- `./include/dispatch/MemberExprHandler.h` - Handler header with full documentation
- `./src/dispatch/MemberExprHandler.cpp` - Handler implementation with debug output
- `./tests/unit/dispatch/MemberExprHandlerDispatcherTest.cpp` - Comprehensive tests (minimum 8 tests)
- Update `./CMakeLists.txt` if needed for test target
</output>

<verification>
Before declaring complete:
1. Code compiles without errors
2. Run tests: `ctest -R MemberExprHandlerDispatcherTest --output-on-failure`
3. All tests pass (100%)
4. Test both arrow and dot member access
5. Test nested member access
6. Verify debug output is clear and helpful
7. Check SOLID compliance (Single Responsibility Principle)
</verification>

<success_criteria>
- MemberExprHandler.h created with proper documentation
- MemberExprHandler.cpp implements recursive dispatch correctly
- Unit tests cover:
  * Handler registration
  * Basic field access (obj.field)
  * Pointer member access (ptr->field)
  * Nested member access (obj.a.b.c)
  * Integration with ExprMapper
  * Predicate correctness (matches only MemberExpr)
  * Arrow vs dot preservation
  * Member access on complex base expressions
- All tests pass (100%)
- Code compiles cleanly
- Handler ready for dispatcher integration
</success_criteria>
