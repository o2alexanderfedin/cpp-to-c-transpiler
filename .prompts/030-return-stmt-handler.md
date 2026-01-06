<objective>
Implement ReturnStmt handler following the Chain of Responsibility dispatcher pattern.

This handler will process C++ return statements and translate them to C return statements, integrating with the existing CppToCVisitorDispatcher architecture.

Phase 1 Scope: Basic return statement translation
- Translate return statement structure (ReturnStmt AST nodes)
- Translate return value expressions (references → pointers via TypeTranslator)
- Create C ReturnStmt nodes with translated expressions
- NOT included in Phase 1: Complex expression translation (that requires ExpressionHandler)

This follows the same architectural pattern as FunctionHandler and ParameterHandler, maintaining SOLID principles and the established dispatcher design.
</objective>

<context>
Project: C++ to C Transpiler using Clang AST
Architecture: Chain of Responsibility pattern with CppToCVisitorDispatcher

Recent work completed:
- FunctionHandler: Translates free function declarations (@src/dispatch/FunctionHandler.cpp, @include/dispatch/FunctionHandler.h)
- ParameterHandler: Translates function parameters (@src/dispatch/ParameterHandler.cpp, @include/dispatch/ParameterHandler.h)
- TypeTranslator: Utility for type translation (@src/translation/TypeTranslator.cpp, @include/translation/TypeTranslator.h)
- DeclMapper: Maps C++ → C declarations (@src/mapping/DeclMapper.cpp)

Examine these files to understand the established pattern:
@src/dispatch/FunctionHandler.cpp
@include/dispatch/FunctionHandler.h
@src/dispatch/ParameterHandler.cpp
@include/dispatch/ParameterHandler.h
@include/dispatch/CppToCVisitorDispatcher.h

Key architectural principles in use:
- Single Responsibility Principle (each handler does ONE thing)
- DRY (TypeTranslator eliminates duplication)
- Chain of Responsibility (handlers register with dispatcher)
- Static registration pattern (registerWith, canHandle, handle methods)
</context>

<requirements>

1. **Create ReturnStmtHandler class** following established pattern:
   - Header: `include/dispatch/ReturnStmtHandler.h`
   - Implementation: `src/dispatch/ReturnStmtHandler.cpp`
   - Namespace: `cpptoc`

2. **Handler interface** (follow FunctionHandler/ParameterHandler exactly):
   ```cpp
   class ReturnStmtHandler {
   public:
       static void registerWith(CppToCVisitorDispatcher& dispatcher);
   private:
       static bool canHandle(const clang::Stmt* S);
       static void handleReturnStmt(
           const CppToCVisitorDispatcher& disp,
           const clang::ASTContext& cppASTContext,
           clang::ASTContext& cASTContext,
           const clang::Stmt* S
       );
   };
   ```

3. **Registration with dispatcher**:
   - Use dispatcher's `addHandler(StmtPredicate, StmtVisitor)` overload
   - Register for `clang::Stmt::ReturnStmtClass` using `S->getStmtClass()`
   - Follow the exact pattern from FunctionHandler::registerWith

4. **Predicate implementation** (canHandle):
   - Check `S->getStmtClass() == clang::Stmt::ReturnStmtClass`
   - Assert S is not null (fail fast on programming errors)
   - Return true only for exact ReturnStmt match

5. **Handler implementation** (handleReturnStmt):
   - Cast S to `clang::ReturnStmt*`
   - Extract return value expression via `getRetValue()` (may be nullptr for `return;`)
   - If return value exists, translate its type using `TypeTranslator::translateType()`
   - Create C ReturnStmt using Clang's `clang::ReturnStmt::Create()`
   - Phase 1: Use existing expression AST node (no deep expression translation yet)
   - Store mapping in DeclMapper if needed for parent handler retrieval

6. **Integration**:
   - Add to CMakeLists.txt in cpptoc_core library sources
   - Follow alphabetical ordering with other handlers

7. **Testing**:
   - Create `tests/unit/dispatch/ReturnStmtHandlerDispatcherTest.cpp`
   - Follow the exact test structure from `FunctionHandlerDispatcherTest.cpp`
   - Test cases:
     - Registration with dispatcher
     - canHandle predicate (ReturnStmt yes, other Stmt no)
     - Return with value: `return 42;`
     - Return with expression: `return a + b;`
     - Return with reference: `return someRef;` (translated via TypeTranslator)
     - Void return: `return;`
   - All tests must pass before considering work complete

</requirements>

<implementation>

**File structure to create:**
- `include/dispatch/ReturnStmtHandler.h` - Handler interface and documentation
- `src/dispatch/ReturnStmtHandler.cpp` - Handler implementation
- `tests/unit/dispatch/ReturnStmtHandlerDispatcherTest.cpp` - Unit tests

**Pattern to follow** (from FunctionHandler):
1. Static registerWith() that calls `dispatcher.addHandler(predicate, visitor)`
2. Static canHandle() using exact type matching with `getStmtClass()`
3. Static handleReturnStmt() that:
   - Asserts preconditions
   - Casts to specific type
   - Extracts properties
   - Translates types using TypeTranslator
   - Creates C AST node
   - Returns or stores in mapper

**Why these patterns matter:**
- Static methods: No instance state needed, follows established pattern
- Exact type matching: Prevents handlers from overlapping (Liskov Substitution)
- TypeTranslator use: Maintains DRY principle, single source of truth for type translation
- DeclMapper use: Enables parent handlers to retrieve child nodes (Chain of Responsibility)

**What to avoid and WHY:**
- Do NOT inline type translation logic (violates DRY - use TypeTranslator)
- Do NOT use isa<> for predicate (too broad - use exact getStmtClass() check)
- Do NOT create instance methods (violates established static pattern)
- Do NOT translate complex expressions yet (Phase 1 limitation - needs ExpressionHandler)

</implementation>

<research>
Before implementing, examine:

1. **Dispatcher's Stmt handling**:
   - Read @include/dispatch/CppToCVisitorDispatcher.h lines 78-83 (StmtPredicate/StmtVisitor typedefs)
   - Read @src/dispatch/CppToCVisitorDispatcher.cpp for addHandler(StmtPredicate, StmtVisitor) implementation

2. **Clang ReturnStmt API**:
   - Check Clang documentation or existing code for:
     - `clang::ReturnStmt::getRetValue()` - returns const Expr*
     - `clang::ReturnStmt::Create()` - factory method signature
     - How to handle nullptr return value (void return)

3. **Test patterns**:
   - Read @tests/unit/dispatch/FunctionHandlerDispatcherTest.cpp entirely
   - Copy the test structure, helper functions, and assertion patterns
   - Adapt for Stmt nodes instead of Decl nodes

</research>

<output>
Create the following files:

1. `./include/dispatch/ReturnStmtHandler.h` - Handler class interface with documentation
2. `./src/dispatch/ReturnStmtHandler.cpp` - Handler implementation
3. `./tests/unit/dispatch/ReturnStmtHandlerDispatcherTest.cpp` - Unit tests (5+ test cases)
4. Update `./CMakeLists.txt` - Add src/dispatch/ReturnStmtHandler.cpp to cpptoc_core sources

</output>

<verification>
Before declaring complete, verify:

1. **Code compiles**: Run `cmake --build build --target ReturnStmtHandlerDispatcherTest`
2. **All tests pass**: Run `./build/ReturnStmtHandlerDispatcherTest` - expect 5+ tests passing
3. **Pattern consistency**: Compare your code side-by-side with FunctionHandler
   - Same static method structure?
   - Same registration pattern?
   - Same predicate approach?
   - Same documentation style?
4. **SOLID compliance**:
   - Single Responsibility: Handler only handles ReturnStmt
   - DRY: Uses TypeTranslator, not duplicate code
   - No magic numbers or hardcoded values
5. **Integration**: Handler registered in appropriate place (likely in main transpiler setup)

</verification>

<success_criteria>
- ReturnStmtHandler class created following exact pattern from FunctionHandler/ParameterHandler
- Registered with CppToCVisitorDispatcher for Stmt nodes
- Predicate uses exact type matching (getStmtClass())
- Handler creates C ReturnStmt AST nodes
- Uses TypeTranslator for type translation (DRY)
- CMakeLists.txt updated with new source file
- Test file created with 5+ passing test cases
- All tests pass (100% success rate)
- Code compiles without warnings
- Pattern-consistent with existing handlers (verify side-by-side)
</success_criteria>
