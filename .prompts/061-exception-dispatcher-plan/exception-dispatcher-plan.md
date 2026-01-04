<?xml version="1.0" encoding="UTF-8"?>
<plan>
  <metadata>
    <version>v1</version>
    <date>2026-01-03</date>
    <confidence>High</confidence>
    <dependencies>
      <dependency>NameMangler API (cpptoc::mangle_*) - stable and ready for integration</dependency>
      <dependency>Existing dispatcher handlers (CompoundStmt, CallExpr, etc.) - must work correctly</dependency>
      <dependency>CNodeBuilder - must support all required C AST node types (IfStmt, CallExpr, VarDecl, CompoundStmt)</dependency>
      <dependency>ExceptionFrameGenerator - complete and tested (17 passing tests)</dependency>
      <dependency>Mapper infrastructure - DeclMapper, TypeMapper, ExprMapper, StmtMapper</dependency>
    </dependencies>
    <open_questions>
      <question>Should TryCatchTransformer/ThrowTranslator remain as service classes called by handlers, or should logic be inlined directly into handlers?</question>
      <question>Do we need a dedicated ExceptionMapper for exception-specific context (frame variable names, action table names), or are existing mappers sufficient?</question>
      <question>Should exception runtime header generation (exception_support.h) be part of dispatcher workflow or remain standalone?</question>
      <question>Frame variable naming strategy for nested try-catch: counter-based (frame_0, frame_1) or UUID-based?</question>
    </open_questions>
    <assumptions>
      <assumption>Exception handling follows same dispatcher pattern as existing handlers (registration, predicate, visitor)</assumption>
      <assumption>TryCatchTransformer and ThrowTranslator can be refactored incrementally without breaking existing tests</assumption>
      <assumption>NameMangler API produces consistent names across all handlers (critical for exception type matching)</assumption>
      <assumption>String-to-AST conversion is feasible using CNodeBuilder and Clang AST API</assumption>
      <assumption>Integration tests will pass after migration if generated C code is functionally equivalent</assumption>
      <assumption>Expression-as-statement pattern (from CompoundStmtHandler) works for throw expressions</assumption>
    </assumptions>
  </metadata>

  <implementation_phases>
    <phase number="1" name="Name Mangling Migration">
      <scope>
        Replace all manual name mangling in TryCatchTransformer and ThrowTranslator with NameMangler API calls.
        This phase is a prerequisite for all other work - name consistency is critical for exception type matching.
      </scope>

      <deliverables>
        <deliverable>TryCatchTransformer.cpp: Replace getMangledTypeName() with cpptoc::mangle_class()</deliverable>
        <deliverable>TryCatchTransformer.cpp: Replace getDestructorName() with cpptoc::mangle_destructor()</deliverable>
        <deliverable>ThrowTranslator.cpp: Replace getMangledTypeName() with cpptoc::mangle_class()</deliverable>
        <deliverable>ThrowTranslator.cpp: Replace getConstructorName() with cpptoc::mangle_constructor()</deliverable>
        <deliverable>Update all existing tests to use NameMangler-generated names in assertions</deliverable>
      </deliverables>

      <tests>
        <test>All existing TryCatchTransformerTest cases pass with NameMangler names</test>
        <test>All existing ThrowTranslatorTest cases pass with NameMangler names</test>
        <test>All 9 integration tests continue to pass</test>
        <test>Type matching in catch handlers works correctly (strcmp with mangled names)</test>
      </tests>

      <success_criteria>
        <criterion>No manual string concatenation with "__" separator remains</criterion>
        <criterion>All exception type names match class names from RecordHandler</criterion>
        <criterion>All destructor names match names from DestructorHandler</criterion>
        <criterion>All constructor names match names from ConstructorHandler</criterion>
        <criterion>Zero test failures after migration</criterion>
      </success_criteria>

      <risks>
        <risk name="NameMangler produces different format than manual mangling">
          <detection>Test failures in type matching assertions</detection>
          <mitigation>Compare NameMangler output vs manual output in isolated unit test before migration</mitigation>
          <fallback>Adjust NameMangler if needed to match expected format</fallback>
        </risk>
        <risk name="Namespace prefixes break existing code">
          <detection>Type matching failures in catch handlers</detection>
          <mitigation>Verify NameMangler includes namespaces consistently across all handlers</mitigation>
          <fallback>Document namespace requirements in test expectations</fallback>
        </risk>
      </risks>

      <estimated_effort>2-3 hours</estimated_effort>
    </phase>

    <phase number="2" name="Handler Skeleton Creation">
      <scope>
        Create minimal TryStmtHandler and ThrowExprHandler classes with registration, predicate, and visitor stubs.
        Handlers delegate to existing TryCatchTransformer/ThrowTranslator service classes (no refactoring yet).
        This phase verifies dispatcher mechanics work before tackling complex AST generation.
      </scope>

      <deliverables>
        <deliverable>include/dispatch/TryStmtHandler.h - Handler interface</deliverable>
        <deliverable>src/dispatch/TryStmtHandler.cpp - Handler implementation (delegates to TryCatchTransformer)</deliverable>
        <deliverable>include/dispatch/ThrowExprHandler.h - Handler interface</deliverable>
        <deliverable>src/dispatch/ThrowExprHandler.cpp - Handler implementation (delegates to ThrowTranslator)</deliverable>
        <deliverable>Update CMakeLists.txt to include new handler source files</deliverable>
        <deliverable>Register handlers in TranslationUnitHandler or main setup code</deliverable>
      </deliverables>

      <tests>
        <test>Handler registration succeeds (no assertion failures)</test>
        <test>canHandle predicates match correct AST node types (CXXTryStmt, CXXThrowExpr)</test>
        <test>Basic dispatcher integration test (parse C++ code, dispatch, verify handler invoked)</test>
        <test>Handlers store results in correct mappers (StmtMapper for try, ExprMapper for throw)</test>
      </tests>

      <success_criteria>
        <criterion>TryStmtHandler registered with dispatcher and handles CXXTryStmt</criterion>
        <criterion>ThrowExprHandler registered with dispatcher and handles CXXThrowExpr</criterion>
        <criterion>Predicates use exact type matching (getStmtClass() == Stmt::CXXTryStmtClass)</criterion>
        <criterion>Visitor signatures match dispatcher interface (const CppToCVisitorDispatcher&amp;, ...)</criterion>
        <criterion>Handlers compile and link successfully</criterion>
      </success_criteria>

      <risks>
        <risk name="CXXThrowExpr is Expr, not Stmt">
          <detection>Compilation errors with StmtPredicate/StmtVisitor casts</detection>
          <mitigation>Use ExprPredicate/ExprVisitor for ThrowExprHandler (check dispatcher interface)</mitigation>
          <fallback>Study existing expression handlers (BinaryOperatorHandler, CallExprHandler) for pattern</fallback>
        </risk>
        <risk name="Handler registration order matters">
          <detection>Handlers not invoked despite correct predicates</detection>
          <mitigation>Study TranslationUnitHandler to understand registration sequence</mitigation>
          <fallback>Register exception handlers early in sequence</fallback>
        </risk>
      </risks>

      <estimated_effort>4-6 hours (2-3 hours per handler)</estimated_effort>
    </phase>

    <phase number="3" name="Placeholder Method Replacement - ThrowTranslator">
      <scope>
        Replace ThrowTranslator placeholder methods (exprToString, argumentsToString) with dispatcher delegation.
        This phase tackles expression translation for throw expressions (constructor arguments).
        Keeps string-based output temporarily to avoid breaking existing tests.
      </scope>

      <deliverables>
        <deliverable>ThrowTranslator.cpp: Replace exprToString() with dispatcher delegation</deliverable>
        <deliverable>ThrowTranslator.cpp: Replace argumentsToString() with dispatcher delegation</deliverable>
        <deliverable>ThrowTranslator gains dispatcher dependency (passed to generateThrowCode())</deliverable>
        <deliverable>Update ThrowExprHandler to pass dispatcher to ThrowTranslator</deliverable>
      </deliverables>

      <implementation_details>
        <detail>
          For each expression in constructor arguments:
          1. disp.dispatch(cppCtx, cCtx, expr)
          2. exprMapper.getCreated(expr) to retrieve translated C Expr*
          3. Use CodeGenerator or AST printing to convert C Expr* to string (temporary)
          4. Collect strings and join with ", " separator
        </detail>
        <detail>
          ThrowTranslator signature change:
          std::string generateThrowCode(
              const CXXThrowExpr* throwExpr,
              const CppToCVisitorDispatcher&amp; disp,
              const ASTContext&amp; cppCtx,
              ASTContext&amp; cCtx
          ) const;
        </detail>
      </implementation_details>

      <tests>
        <test>Throw with string literal argument: throw Error("message")</test>
        <test>Throw with integer literal: throw IntError(42)</test>
        <test>Throw with complex expression: throw Error(a + b)</test>
        <test>Throw with member access: throw Error(obj.message)</test>
        <test>Throw with function call: throw Error(getMessage())</test>
        <test>All existing ThrowTranslatorTest cases pass</test>
      </tests>

      <success_criteria>
        <criterion>No "/* expression */" placeholders in generated throw code</criterion>
        <criterion>All expression types handled by dispatcher (literals, DeclRefExpr, BinaryOperator, etc.)</criterion>
        <criterion>Constructor arguments translated correctly</criterion>
        <criterion>Generated C code compiles and runs correctly</criterion>
      </success_criteria>

      <risks>
        <risk name="Expression handler missing for some expression type">
          <detection>disp.dispatch() returns false, assertion failure</detection>
          <mitigation>Add missing expression handler (study ExpressionHandler hierarchy)</mitigation>
          <fallback>Temporary fallback to placeholder for unsupported expressions, log warning</fallback>
        </risk>
        <risk name="C Expr* to string conversion complex">
          <detection>No obvious API for AST node to string conversion</detection>
          <mitigation>Use CodeGenerator (if available) or Clang's AST printing utilities</mitigation>
          <fallback>Manually implement simple expression printer for common cases</fallback>
        </risk>
      </risks>

      <estimated_effort>5-7 hours</estimated_effort>
    </phase>

    <phase number="4" name="Placeholder Method Replacement - TryCatchTransformer">
      <scope>
        Replace TryCatchTransformer placeholder method (stmtToString) with dispatcher delegation.
        This phase enables translation of try body and catch body statements.
        Keeps string-based output temporarily.
      </scope>

      <deliverables>
        <deliverable>TryCatchTransformer.cpp: Replace stmtToString() with dispatcher delegation</deliverable>
        <deliverable>TryCatchTransformer gains dispatcher dependency (passed to transformTryCatch())</deliverable>
        <deliverable>Update TryStmtHandler to pass dispatcher to TryCatchTransformer</deliverable>
      </deliverables>

      <implementation_details>
        <detail>
          For each statement in try body or catch body:
          1. disp.dispatch(cppCtx, cCtx, stmt)
          2. stmtMapper.getCreated(stmt) to retrieve translated C Stmt*
          3. Convert C Stmt* to string (temporary, using CodeGenerator or AST printer)
          4. Append to body code with proper indentation
        </detail>
        <detail>
          TryCatchTransformer signature change:
          std::string transformTryCatch(
              const CXXTryStmt* tryStmt,
              const std::string&amp; frameVarName,
              const std::string&amp; actionsTableName,
              const CppToCVisitorDispatcher&amp; disp,
              const ASTContext&amp; cppCtx,
              ASTContext&amp; cCtx
          ) const;
        </detail>
      </implementation_details>

      <tests>
        <test>Try body with DeclStmt: try { int x = 42; }</test>
        <test>Try body with method call: try { obj.method(); }</test>
        <test>Catch body with DeclStmt and throw: catch (Error e) { int y = e.code; throw; }</test>
        <test>Nested try-catch blocks</test>
        <test>All existing TryCatchTransformerTest cases pass</test>
      </tests>

      <success_criteria>
        <criterion>No "/* declaration */;" or "/* function call */;" placeholders</criterion>
        <criterion>All statement types handled by dispatcher</criterion>
        <criterion>Try body and catch body translated correctly</criterion>
        <criterion>Nested statements work (CompoundStmt dispatches child statements)</criterion>
      </success_criteria>

      <risks>
        <risk name="Statement handler missing for some statement type">
          <detection>disp.dispatch() returns false for statement</detection>
          <mitigation>Add missing statement handler or use existing StatementHandler</mitigation>
          <fallback>Log warning and skip statement (for now)</fallback>
        </risk>
        <risk name="Indentation and formatting issues">
          <detection>Generated C code has incorrect formatting</detection>
          <mitigation>Use CodeGenerator's indentation utilities</mitigation>
          <fallback>Manually track indentation level in string generation</fallback>
        </risk>
      </risks>

      <estimated_effort>5-7 hours</estimated_effort>
    </phase>

    <phase number="5" name="String-to-AST Refactoring - ThrowTranslator">
      <scope>
        Refactor ThrowTranslator to return C AST nodes (Expr*) instead of strings.
        This phase aligns with the 3-stage pipeline: C++ AST → C AST → C code.
        Uses CNodeBuilder to create C VarDecl (for exception variable), C CallExpr (for constructor and cxx_throw).
      </scope>

      <deliverables>
        <deliverable>ThrowTranslator.cpp: Change return type from std::string to clang::Expr*</deliverable>
        <deliverable>ThrowTranslator.cpp: Use CNodeBuilder to create C AST nodes</deliverable>
        <deliverable>ThrowTranslator.cpp: Create C VarDecl for exception allocation (__ex)</deliverable>
        <deliverable>ThrowTranslator.cpp: Create C CallExpr for malloc, constructor, cxx_throw</deliverable>
        <deliverable>Update ThrowExprHandler to store C Expr* in ExprMapper</deliverable>
      </deliverables>

      <implementation_details>
        <detail>
          C AST nodes to create:
          1. VarDecl for exception variable: struct Type *__ex
          2. CallExpr for malloc: malloc(sizeof(struct Type))
          3. ImplicitCastExpr for malloc result cast: (struct Type*)malloc(...)
          4. CallExpr for constructor: Type__ctor(__ex, args...)
          5. CallExpr for cxx_throw: cxx_throw(__ex, "TypeName")
          6. Return CallExpr to cxx_throw as final result
        </detail>
        <detail>
          Constructor arguments are already C Expr* (from dispatcher delegation in Phase 3).
          Pass them directly to CallExpr::Create() for constructor call.
        </detail>
        <detail>
          Type info string remains as StringLiteral node in C AST.
        </detail>
      </implementation_details>

      <tests>
        <test>Verify C AST structure: VarDecl exists with correct type</test>
        <test>Verify CallExpr to malloc has correct arguments</test>
        <test>Verify CallExpr to constructor has correct function name and arguments</test>
        <test>Verify CallExpr to cxx_throw has exception variable and type string</test>
        <test>Use CodeGenerator to emit C code from C AST, compare with expected output</test>
        <test>Update ThrowTranslatorTest to assert C AST structure instead of strings</test>
      </tests>

      <success_criteria>
        <criterion>ThrowTranslator returns C Expr* (CallExpr to cxx_throw)</criterion>
        <criterion>No string-based code generation in ThrowTranslator</criterion>
        <criterion>C AST nodes have correct types and properties</criterion>
        <criterion>C AST nodes belong to C ASTContext (not C++ ASTContext)</criterion>
        <criterion>All existing tests pass after updating assertions</criterion>
      </success_criteria>

      <risks>
        <risk name="CNodeBuilder missing required node types">
          <detection>Compilation errors or runtime assertions in CNodeBuilder</detection>
          <mitigation>Extend CNodeBuilder to support VarDecl, CallExpr creation</mitigation>
          <fallback>Use Clang API directly (VarDecl::Create, CallExpr::Create)</fallback>
        </risk>
        <risk name="AST node parent/context setting incorrect">
          <detection>AST consistency errors or crashes during code generation</detection>
          <mitigation>Study existing handlers (MethodHandler, ConstructorHandler) for correct pattern</mitigation>
          <fallback>Use DeclContext utilities to set correct parent</fallback>
        </risk>
        <risk name="Memory management issues with C AST nodes">
          <detection>Leaks or crashes</detection>
          <mitigation>All nodes owned by ASTContext (no manual delete needed)</mitigation>
          <fallback>Review Clang AST ownership model</fallback>
        </risk>
      </risks>

      <estimated_effort>8-12 hours</estimated_effort>
    </phase>

    <phase number="6" name="String-to-AST Refactoring - TryCatchTransformer">
      <scope>
        Refactor TryCatchTransformer to return C AST nodes (Stmt*) instead of strings.
        Create C IfStmt (setjmp guard), CompoundStmt (try body, catch bodies), CallExpr (frame operations).
        Most complex phase due to control flow structure.
      </scope>

      <deliverables>
        <deliverable>TryCatchTransformer.cpp: Change return type from std::string to clang::Stmt*</deliverable>
        <deliverable>TryCatchTransformer.cpp: Use CNodeBuilder to create C AST nodes</deliverable>
        <deliverable>TryCatchTransformer.cpp: Create C IfStmt for setjmp guard</deliverable>
        <deliverable>TryCatchTransformer.cpp: Create C CompoundStmt for try body and catch handlers</deliverable>
        <deliverable>TryCatchTransformer.cpp: Create C VarDecl for exception frame variable</deliverable>
        <deliverable>Update TryStmtHandler to store C Stmt* in StmtMapper</deliverable>
      </deliverables>

      <implementation_details>
        <detail>
          C AST structure:
          {
              struct __cxx_exception_frame frame;  // VarDecl
              /* frame push code */                 // Stmt (from ExceptionFrameGenerator)
              if (setjmp(frame.jmpbuf) == 0) {     // IfStmt
                  /* try body */                    // CompoundStmt (from dispatcher)
                  /* frame pop code */              // Stmt
              } else {                              // IfStmt else branch
                  /* catch handlers */              // CompoundStmt with nested IfStmts
              }
          }
        </detail>
        <detail>
          Setjmp guard condition: BinaryOperator (==) with CallExpr to setjmp and IntegerLiteral (0)
        </detail>
        <detail>
          Catch handlers: Nested IfStmts with strcmp conditions (from generateTypeCheck)
        </detail>
        <detail>
          Frame push/pop: May need to convert ExceptionFrameGenerator string output to C AST,
          or extend ExceptionFrameGenerator to return C AST nodes.
        </detail>
      </implementation_details>

      <tests>
        <test>Verify C AST structure: IfStmt with correct condition (setjmp guard)</test>
        <test>Verify IfStmt then-branch contains try body CompoundStmt</test>
        <test>Verify IfStmt else-branch contains catch handler CompoundStmt</test>
        <test>Verify nested IfStmts for multiple catch handlers</test>
        <test>Verify VarDecl for exception frame exists and has correct type</test>
        <test>Use CodeGenerator to emit C code, compare with expected output</test>
        <test>Update TryCatchTransformerTest to assert C AST structure</test>
      </tests>

      <success_criteria>
        <criterion>TryCatchTransformer returns C Stmt* (outer CompoundStmt or IfStmt)</criterion>
        <criterion>No string-based code generation in TryCatchTransformer</criterion>
        <criterion>C AST nodes correctly represent setjmp/longjmp control flow</criterion>
        <criterion>Try body and catch bodies are CompoundStmt from dispatcher</criterion>
        <criterion>All existing tests pass after updating assertions</criterion>
      </success_criteria>

      <risks>
        <risk name="ExceptionFrameGenerator produces strings, not AST">
          <detection>Cannot integrate frame push/pop code into C AST</detection>
          <mitigation>Option 1: Extend ExceptionFrameGenerator to return C AST nodes</mitigation>
          <mitigation>Option 2: Parse frame push/pop strings back into AST (avoid this)</mitigation>
          <mitigation>Option 3: Inline frame push/pop logic into TryCatchTransformer</mitigation>
          <fallback>Use Option 3 (inline logic) - simplest for Phase 6</fallback>
        </risk>
        <risk name="Complex control flow hard to represent in AST">
          <detection>Incorrect nesting or missing statements in generated AST</detection>
          <mitigation>Build incrementally: first single catch, then multiple catches, then nested try</mitigation>
          <fallback>Study existing control flow handlers (IfStmtHandler, WhileStmtHandler if they exist)</fallback>
        </risk>
        <risk name="AST node creation order matters">
          <detection>AST consistency errors during construction</detection>
          <mitigation>Create leaf nodes first (expressions), then statements, then compounds</mitigation>
          <fallback>Review Clang AST construction documentation</fallback>
        </risk>
      </risks>

      <estimated_effort>10-15 hours</estimated_effort>
    </phase>

    <phase number="7" name="Test Migration and New Tests">
      <scope>
        Migrate existing unit tests to dispatcher pattern and create new dispatcher-specific tests.
        Integration tests should continue to work with minimal changes.
      </scope>

      <deliverables>
        <deliverable>tests/unit/dispatch/TryStmtHandlerDispatcherTest.cpp - New dispatcher test</deliverable>
        <deliverable>tests/unit/dispatch/ThrowExprHandlerDispatcherTest.cpp - New dispatcher test</deliverable>
        <deliverable>Update TryCatchTransformerTest.cpp to use dispatcher and assert C AST structure</deliverable>
        <deliverable>Update ThrowTranslatorTest.cpp to use dispatcher and assert C AST structure</deliverable>
        <deliverable>Verify all integration tests still pass (ExceptionHandlingIntegrationTest.cpp, etc.)</deliverable>
        <deliverable>Add cross-handler integration tests (throw in constructor, method call in try block, etc.)</deliverable>
      </deliverables>

      <new_tests>
        <test name="TryStmtHandlerRegistrationTest">
          Verify handler registers with dispatcher and handles CXXTryStmt
        </test>
        <test name="ThrowExprHandlerRegistrationTest">
          Verify handler registers with dispatcher and handles CXXThrowExpr
        </test>
        <test name="TryStmtWithMethodCallTest">
          Try block containing method call, verify method translation via MethodHandler
        </test>
        <test name="ThrowInConstructorTest">
          Throw expression in constructor body, verify integration with ConstructorHandler
        </test>
        <test name="ExceptionTypeMatchingTest">
          Verify NameMangler produces consistent names for exception types in throw and catch
        </test>
        <test name="NestedTryCatchTest">
          Nested try-catch blocks with unique frame variable names
        </test>
        <test name="RethrowInCatchTest">
          Re-throw (throw;) inside catch handler, verify frame access
        </test>
        <test name="ExceptionCleanupTest">
          Verify destructor call generation uses NameMangler API
        </test>
      </new_tests>

      <test_migration_strategy>
        <strategy>
          1. Keep integration tests as-is (they test runtime behavior, not implementation)
          2. Create new dispatcher tests first (TryStmtHandlerDispatcherTest, ThrowExprHandlerDispatcherTest)
          3. Migrate existing unit tests incrementally:
             - Update test fixtures to include dispatcher setup
             - Change assertions from string matching to C AST structure checks
             - Use CodeGenerator to verify emitted C code when needed
          4. Run both old and new tests in parallel during migration
          5. Remove old tests only after new tests pass reliably
        </strategy>
      </test_migration_strategy>

      <tests>
        <test>All new dispatcher tests pass</test>
        <test>All migrated unit tests pass with C AST assertions</test>
        <test>All 9 integration tests pass unchanged</test>
        <test>Cross-handler integration tests pass</test>
        <test>Code coverage maintained or improved</test>
      </tests>

      <success_criteria>
        <criterion>All existing test cases covered by new dispatcher tests</criterion>
        <criterion>New tests follow dispatcher test patterns (see ReturnStmtHandlerDispatcherTest)</criterion>
        <criterion>Zero test failures after migration</criterion>
        <criterion>Integration tests pass without modification (behavior preserved)</criterion>
        <criterion>Cross-handler integration verified</criterion>
      </success_criteria>

      <risks>
        <risk name="C AST assertions more complex than string matching">
          <detection>Tests become hard to read and maintain</detection>
          <mitigation>Create helper assertion functions (assertCallExprTo, assertIfStmtWithCondition, etc.)</mitigation>
          <fallback>Use CodeGenerator for string comparison as secondary verification</fallback>
        </risk>
        <risk name="Test fixtures require significant boilerplate">
          <detection>Lots of duplicated setup code</detection>
          <mitigation>Create shared test fixture base class (ExceptionDispatcherTestFixture)</mitigation>
          <fallback>Use helper functions for common setup patterns</fallback>
        </risk>
        <risk name="Integration tests fail due to behavior changes">
          <detection>Runtime failures in exception handling tests</detection>
          <mitigation>Debug carefully, compare generated C code before/after migration</mitigation>
          <fallback>Rollback to previous phase and investigate</fallback>
        </risk>
      </risks>

      <estimated_effort>10-14 hours</estimated_effort>
    </phase>
  </implementation_phases>

  <task_breakdown>
    <phase_1_tasks>
      <task id="1.1" name="Compare NameMangler vs Manual Mangling Output">
        <description>Write test to compare cpptoc::mangle_class() output vs getMangledTypeName() output</description>
        <steps>
          1. Create test with simple exception class (e.g., class Error {})
          2. Call both getMangledTypeName() and cpptoc::mangle_class()
          3. Compare outputs, verify format compatibility
          4. Test with namespaced class (e.g., namespace NS { class Error {}; })
        </steps>
        <dependencies>None</dependencies>
        <effort>0.5 hours</effort>
        <verification>Test passes, outputs match or differences documented</verification>
      </task>

      <task id="1.2" name="Update TryCatchTransformer Name Mangling">
        <description>Replace manual mangling with NameMangler API in TryCatchTransformer</description>
        <steps>
          1. Include NameMangler.h in TryCatchTransformer.cpp
          2. Replace getMangledTypeName() calls with cpptoc::mangle_class(RD)
          3. Replace getDestructorName() calls with cpptoc::mangle_destructor(DD)
          4. Remove getMangledTypeName() and getDestructorName() private methods
          5. Compile and run TryCatchTransformerTest
        </steps>
        <dependencies>Task 1.1 complete</dependencies>
        <effort>1 hour</effort>
        <verification>TryCatchTransformerTest passes, no manual mangling remains</verification>
      </task>

      <task id="1.3" name="Update ThrowTranslator Name Mangling">
        <description>Replace manual mangling with NameMangler API in ThrowTranslator</description>
        <steps>
          1. Include NameMangler.h in ThrowTranslator.cpp
          2. Replace getMangledTypeName() calls with cpptoc::mangle_class(RD)
          3. Replace getConstructorName() calls with cpptoc::mangle_constructor(CD)
          4. Remove getMangledTypeName() and getConstructorName() private methods
          5. Compile and run ThrowTranslatorTest
        </steps>
        <dependencies>Task 1.1 complete</dependencies>
        <effort>1 hour</effort>
        <verification>ThrowTranslatorTest passes, no manual mangling remains</verification>
      </task>

      <task id="1.4" name="Update Integration Tests for NameMangler Names">
        <description>Update integration test assertions to use NameMangler-generated names</description>
        <steps>
          1. Run integration tests and note failures (if any)
          2. Update string assertions to match NameMangler format
          3. Verify all 9 integration tests pass
        </steps>
        <dependencies>Tasks 1.2, 1.3 complete</dependencies>
        <effort>0.5 hours</effort>
        <verification>All integration tests pass</verification>
      </task>
    </phase_1_tasks>

    <phase_2_tasks>
      <task id="2.1" name="Create TryStmtHandler Header">
        <description>Create include/dispatch/TryStmtHandler.h following handler pattern</description>
        <steps>
          1. Copy ReturnStmtHandler.h as template
          2. Rename class to TryStmtHandler
          3. Update documentation for CXXTryStmt handling
          4. Define registerWith(), canHandle(), handleTryStmt() methods
          5. Document delegation to TryCatchTransformer
        </steps>
        <dependencies>None</dependencies>
        <effort>1 hour</effort>
        <verification>Header compiles, follows dispatcher pattern</verification>
      </task>

      <task id="2.2" name="Create TryStmtHandler Implementation">
        <description>Create src/dispatch/TryStmtHandler.cpp with minimal implementation</description>
        <steps>
          1. Implement registerWith() - register as StmtHandler
          2. Implement canHandle() - check S->getStmtClass() == Stmt::CXXTryStmtClass
          3. Implement handleTryStmt() - delegate to TryCatchTransformer.transformTryCatch()
          4. Store string result in StmtMapper (temporary, Phase 6 will change to AST)
          5. Generate unique frame variable name (frame_N with static counter)
        </steps>
        <dependencies>Task 2.1 complete</dependencies>
        <effort>2 hours</effort>
        <verification>Compiles and links, basic dispatch test passes</verification>
      </task>

      <task id="2.3" name="Create ThrowExprHandler Header">
        <description>Create include/dispatch/ThrowExprHandler.h following expression handler pattern</description>
        <steps>
          1. Copy DeclRefExprHandler.h or other expression handler as template
          2. Rename class to ThrowExprHandler
          3. Update documentation for CXXThrowExpr handling
          4. Define registerWith(), canHandle(), handleThrowExpr() methods
          5. Document delegation to ThrowTranslator
        </steps>
        <dependencies>None</dependencies>
        <effort>1 hour</effort>
        <verification>Header compiles, follows expression handler pattern</verification>
      </task>

      <task id="2.4" name="Create ThrowExprHandler Implementation">
        <description>Create src/dispatch/ThrowExprHandler.cpp with minimal implementation</description>
        <steps>
          1. Implement registerWith() - register as ExprHandler
          2. Implement canHandle() - check E->getStmtClass() == Stmt::CXXThrowExprClass
          3. Implement handleThrowExpr() - delegate to ThrowTranslator.generateThrowCode()
          4. Store string result in ExprMapper (temporary, Phase 5 will change to AST)
          5. Handle re-throw case (CXXThrowExpr with null subexpression)
        </steps>
        <dependencies>Task 2.3 complete</dependencies>
        <effort>2 hours</effort>
        <verification>Compiles and links, basic dispatch test passes</verification>
      </task>

      <task id="2.5" name="Register Handlers and Basic Test">
        <description>Register handlers and create basic dispatcher integration test</description>
        <steps>
          1. Update CMakeLists.txt to include new handler source files
          2. Register TryStmtHandler in TranslationUnitHandler or setup code
          3. Register ThrowExprHandler in setup code
          4. Create basic test: parse "void f() { try { throw 1; } catch(int) {} }"
          5. Dispatch and verify handlers invoked
        </steps>
        <dependencies>Tasks 2.2, 2.4 complete</dependencies>
        <effort>1.5 hours</effort>
        <verification>Handlers registered, basic test passes</verification>
      </task>
    </phase_2_tasks>

    <phase_3_tasks>
      <task id="3.1" name="Add Dispatcher Parameter to ThrowTranslator">
        <description>Modify ThrowTranslator to accept dispatcher parameter</description>
        <steps>
          1. Update generateThrowCode() signature to include dispatcher, contexts
          2. Update argumentsToString() to accept dispatcher
          3. Update exprToString() to accept dispatcher
          4. Update ThrowExprHandler to pass dispatcher to ThrowTranslator
        </steps>
        <dependencies>Phase 2 complete</dependencies>
        <effort>1 hour</effort>
        <verification>Code compiles, signature matches</verification>
      </task>

      <task id="3.2" name="Replace exprToString with Dispatcher Delegation">
        <description>Implement dispatcher-based expression translation in exprToString</description>
        <steps>
          1. For each expression type currently handled (literals, casts):
             - Call disp.dispatch(cppCtx, cCtx, expr)
             - Retrieve C Expr* from exprMapper.getCreated(expr)
             - Convert C Expr* to string (temporary, using AST printer)
          2. Return string result
          3. Add assertion if dispatch fails (no handler matched)
        </steps>
        <dependencies>Task 3.1 complete</dependencies>
        <effort>2 hours</effort>
        <verification>Expressions dispatch correctly, no placeholders for supported types</verification>
      </task>

      <task id="3.3" name="Replace argumentsToString with Dispatcher Delegation">
        <description>Implement dispatcher-based argument translation</description>
        <steps>
          1. For each constructor argument:
             - Call disp.dispatch(cppCtx, cCtx, arg)
             - Retrieve C Expr* from exprMapper.getCreated(arg)
             - Convert to string (temporary)
          2. Join argument strings with ", "
          3. Return result
        </steps>
        <dependencies>Task 3.2 complete</dependencies>
        <effort>1.5 hours</effort>
        <verification>Constructor arguments translate correctly</verification>
      </task>

      <task id="3.4" name="Test Complex Throw Expressions">
        <description>Create tests for throw with complex constructor arguments</description>
        <steps>
          1. Test throw Error(a + b) - binary operator
          2. Test throw Error(obj.field) - member access
          3. Test throw Error(func()) - function call
          4. Verify all expressions handled by dispatcher
        </steps>
        <dependencies>Task 3.3 complete</dependencies>
        <effort>1.5 hours</effort>
        <verification>All tests pass, no placeholders</verification>
      </task>
    </phase_3_tasks>

    <phase_4_tasks>
      <task id="4.1" name="Add Dispatcher Parameter to TryCatchTransformer">
        <description>Modify TryCatchTransformer to accept dispatcher parameter</description>
        <steps>
          1. Update transformTryCatch() signature to include dispatcher, contexts
          2. Update generateTryBody() to accept dispatcher
          3. Update generateCatchHandlers() to accept dispatcher
          4. Update stmtToString() to accept dispatcher
          5. Update TryStmtHandler to pass dispatcher to TryCatchTransformer
        </steps>
        <dependencies>Phase 3 complete</dependencies>
        <effort>1 hour</effort>
        <verification>Code compiles, signature matches</verification>
      </task>

      <task id="4.2" name="Replace stmtToString with Dispatcher Delegation">
        <description>Implement dispatcher-based statement translation in stmtToString</description>
        <steps>
          1. For each statement:
             - Call disp.dispatch(cppCtx, cCtx, stmt)
             - Retrieve C Stmt* from stmtMapper.getCreated(stmt)
             - Convert C Stmt* to string (temporary, using AST printer or CodeGenerator)
          2. Return string result
          3. Add assertion if dispatch fails
        </steps>
        <dependencies>Task 4.1 complete</dependencies>
        <effort>2.5 hours</effort>
        <verification>Statements dispatch correctly, no placeholders</verification>
      </task>

      <task id="4.3" name="Update Try Body Generation">
        <description>Update generateTryBody to use dispatcher for body statements</description>
        <steps>
          1. Iterate over try body statements (CompoundStmt children)
          2. For each statement, call stmtToString() (now using dispatcher)
          3. Collect statement strings and format with indentation
        </steps>
        <dependencies>Task 4.2 complete</dependencies>
        <effort>1 hour</effort>
        <verification>Try body translates correctly with dispatcher</verification>
      </task>

      <task id="4.4" name="Update Catch Handler Generation">
        <description>Update generateCatchHandlers to use dispatcher for catch body statements</description>
        <steps>
          1. Iterate over catch handler body statements
          2. For each statement, call stmtToString() (now using dispatcher)
          3. Collect and format catch body code
        </steps>
        <dependencies>Task 4.2 complete</dependencies>
        <effort>1 hour</effort>
        <verification>Catch handlers translate correctly with dispatcher</verification>
      </task>

      <task id="4.5" name="Test Try-Catch with Complex Bodies">
        <description>Create tests for try-catch with various statement types</description>
        <steps>
          1. Test try block with DeclStmt: try { int x = 42; }
          2. Test try block with method call: try { obj.method(); }
          3. Test catch with multiple statements
          4. Test nested try-catch
        </steps>
        <dependencies>Tasks 4.3, 4.4 complete</dependencies>
        <effort>1.5 hours</effort>
        <verification>All tests pass, no placeholders</verification>
      </task>
    </phase_4_tasks>

    <phase_5_tasks>
      <task id="5.1" name="Design C AST Structure for Throw">
        <description>Document C AST node structure for throw expression</description>
        <steps>
          1. Document node hierarchy (CompoundStmt containing VarDecl, CallExprs)
          2. Identify all node types needed (VarDecl, CallExpr, ImplicitCastExpr, etc.)
          3. Verify CNodeBuilder or Clang API supports all needed types
          4. Create example code showing node creation sequence
        </steps>
        <dependencies>Phase 4 complete</dependencies>
        <effort>1.5 hours</effort>
        <verification>Design documented, node types verified available</verification>
      </task>

      <task id="5.2" name="Implement C AST Node Creation for Exception Allocation">
        <description>Create C VarDecl for exception variable and CallExpr for malloc</description>
        <steps>
          1. Create C pointer type (struct Type*) using C ASTContext
          2. Create VarDecl for __ex variable with pointer type
          3. Create CallExpr to malloc with sizeof argument
          4. Create ImplicitCastExpr for malloc cast
          5. Set VarDecl initializer to malloc CallExpr
        </steps>
        <dependencies>Task 5.1 complete</dependencies>
        <effort>2 hours</effort>
        <verification>C AST nodes created correctly, types match</verification>
      </task>

      <task id="5.3" name="Implement C AST Node Creation for Constructor Call">
        <description>Create C CallExpr for exception constructor call</description>
        <steps>
          1. Get mangled constructor name (already using NameMangler from Phase 1)
          2. Create DeclRefExpr to constructor function
          3. Collect constructor argument C Expr* nodes (from dispatcher delegation in Phase 3)
          4. Create CallExpr with constructor DeclRefExpr and arguments
          5. First argument is __ex (exception variable)
        </steps>
        <dependencies>Task 5.2 complete</dependencies>
        <effort>2 hours</effort>
        <verification>Constructor CallExpr created with correct arguments</verification>
      </task>

      <task id="5.4" name="Implement C AST Node Creation for cxx_throw Call">
        <description>Create C CallExpr for cxx_throw runtime call</description>
        <steps>
          1. Create DeclRefExpr to cxx_throw function
          2. Create StringLiteral for type info string
          3. Create DeclRefExpr to __ex variable
          4. Create CallExpr with cxx_throw DeclRefExpr, __ex, and type info arguments
        </steps>
        <dependencies>Task 5.3 complete</dependencies>
        <effort>1.5 hours</effort>
        <verification>cxx_throw CallExpr created with correct arguments</verification>
      </task>

      <task id="5.5" name="Update generateThrowCode to Return C AST">
        <description>Change return type from string to Expr* and return cxx_throw CallExpr</description>
        <steps>
          1. Change return type: std::string → clang::Expr*
          2. Instead of building strings, create C AST nodes (from tasks 5.2-5.4)
          3. Return final CallExpr to cxx_throw
          4. Update ThrowExprHandler to store C Expr* in ExprMapper (not string)
        </steps>
        <dependencies>Tasks 5.2, 5.3, 5.4 complete</dependencies>
        <effort>2 hours</effort>
        <verification>generateThrowCode returns C Expr*, compiles successfully</verification>
      </task>

      <task id="5.6" name="Update Tests to Assert C AST Structure">
        <description>Modify ThrowTranslatorTest to check C AST instead of strings</description>
        <steps>
          1. Update test fixture to include C ASTContext
          2. Change assertions from string matching to AST structure checks
          3. Verify VarDecl exists with correct name (__ex)
          4. Verify CallExpr to malloc exists
          5. Verify CallExpr to constructor has correct arguments
          6. Verify CallExpr to cxx_throw is final result
          7. Optionally use CodeGenerator to emit C code for comparison
        </steps>
        <dependencies>Task 5.5 complete</dependencies>
        <effort>2.5 hours</effort>
        <verification>All ThrowTranslatorTest cases pass with AST assertions</verification>
      </task>
    </phase_5_tasks>

    <phase_6_tasks>
      <task id="6.1" name="Design C AST Structure for Try-Catch">
        <description>Document C AST node structure for try-catch control flow</description>
        <steps>
          1. Document outer structure (CompoundStmt or just IfStmt)
          2. Document IfStmt for setjmp guard (condition, then-branch, else-branch)
          3. Document setjmp condition (BinaryOperator with CallExpr and IntegerLiteral)
          4. Document frame VarDecl structure
          5. Identify how to integrate frame push/pop (inline or ExceptionFrameGenerator extension)
        </steps>
        <dependencies>Phase 5 complete</dependencies>
        <effort>2 hours</effort>
        <verification>Design documented, approach for frame operations decided</verification>
      </task>

      <task id="6.2" name="Implement Frame Variable Creation">
        <description>Create C VarDecl for exception frame</description>
        <steps>
          1. Create C struct type for __cxx_exception_frame
          2. Create VarDecl for frame variable (frame_N with unique name)
          3. No initializer needed (frame initialized by frame push code)
        </steps>
        <dependencies>Task 6.1 complete</dependencies>
        <effort>1.5 hours</effort>
        <verification>Frame VarDecl created with correct type</verification>
      </task>

      <task id="6.3" name="Implement Setjmp Guard Condition">
        <description>Create C BinaryOperator for setjmp guard: setjmp(...) == 0</description>
        <steps>
          1. Create MemberExpr for frame.jmpbuf
          2. Create CallExpr to setjmp with frame.jmpbuf argument
          3. Create IntegerLiteral for 0
          4. Create BinaryOperator with == operator
        </steps>
        <dependencies>Task 6.2 complete</dependencies>
        <effort>2 hours</effort>
        <verification>Setjmp condition created correctly</verification>
      </task>

      <task id="6.4" name="Implement Try Body CompoundStmt">
        <description>Create C CompoundStmt for try body (then-branch of IfStmt)</description>
        <steps>
          1. Dispatch try body CompoundStmt to CompoundStmtHandler
          2. Retrieve C CompoundStmt from stmtMapper
          3. Prepend frame activation statements (from ExceptionFrameGenerator or inlined)
          4. Append frame pop statement at end
          5. Return CompoundStmt as then-branch
        </steps>
        <dependencies>Task 6.3 complete</dependencies>
        <effort>2.5 hours</effort>
        <verification>Try body CompoundStmt contains correct statements</verification>
      </task>

      <task id="6.5" name="Implement Catch Handlers CompoundStmt">
        <description>Create C CompoundStmt for catch handlers (else-branch of IfStmt)</description>
        <steps>
          1. For each catch handler, create nested IfStmt with strcmp condition
          2. Dispatch catch body CompoundStmt to CompoundStmtHandler
          3. Add exception variable cast/assignment to catch body
          4. Add exception cleanup code to catch body
          5. Nest IfStmts for multiple catch handlers (else-if chain)
        </steps>
        <dependencies>Task 6.4 complete</dependencies>
        <effort>3 hours</effort>
        <verification>Catch handler CompoundStmt with nested IfStmts created correctly</verification>
      </task>

      <task id="6.6" name="Integrate Frame Push/Pop Operations">
        <description>Add frame push/pop statements to C AST</description>
        <steps>
          1. Option A: Inline frame push/pop logic (create CallExpr, assignment, etc.)
          2. Option B: Extend ExceptionFrameGenerator to return C Stmt* instead of string
          3. Choose Option A for simplicity (can refactor to B later)
          4. Create frame initialization statements as C AST nodes
          5. Insert at beginning of try body
        </steps>
        <dependencies>Task 6.4 complete</dependencies>
        <effort>2.5 hours</effort>
        <verification>Frame push/pop statements integrated into C AST</verification>
      </task>

      <task id="6.7" name="Create Final IfStmt and Update Return Type">
        <description>Assemble complete try-catch structure and return as C Stmt*</description>
        <steps>
          1. Create IfStmt with setjmp condition, try body, catch handlers
          2. Optionally wrap in CompoundStmt with frame VarDecl
          3. Change transformTryCatch() return type: std::string → clang::Stmt*
          4. Return final Stmt* (IfStmt or CompoundStmt)
          5. Update TryStmtHandler to store C Stmt* in StmtMapper
        </steps>
        <dependencies>Tasks 6.3, 6.4, 6.5, 6.6 complete</dependencies>
        <effort>2 hours</effort>
        <verification>transformTryCatch returns C Stmt*, structure correct</verification>
      </task>

      <task id="6.8" name="Update Tests to Assert Try-Catch C AST Structure">
        <description>Modify TryCatchTransformerTest to check C AST instead of strings</description>
        <steps>
          1. Update test fixture for C ASTContext
          2. Change assertions to C AST structure checks
          3. Verify IfStmt exists with setjmp condition
          4. Verify try body CompoundStmt
          5. Verify catch handler IfStmts
          6. Verify frame VarDecl
          7. Optionally use CodeGenerator for C code comparison
        </steps>
        <dependencies>Task 6.7 complete</dependencies>
        <effort>3.5 hours</effort>
        <verification>All TryCatchTransformerTest cases pass with AST assertions</verification>
      </task>
    </phase_6_tasks>

    <phase_7_tasks>
      <task id="7.1" name="Create TryStmtHandlerDispatcherTest">
        <description>Create new dispatcher test following ReturnStmtHandlerDispatcherTest pattern</description>
        <steps>
          1. Create tests/unit/dispatch/TryStmtHandlerDispatcherTest.cpp
          2. Test handler registration
          3. Test predicate matches only CXXTryStmt
          4. Test basic try-catch translation
          5. Test multiple catch handlers
          6. Test nested try-catch
        </steps>
        <dependencies>Phase 6 complete</dependencies>
        <effort>2.5 hours</effort>
        <verification>All dispatcher tests pass</verification>
      </task>

      <task id="7.2" name="Create ThrowExprHandlerDispatcherTest">
        <description>Create new dispatcher test for throw expressions</description>
        <steps>
          1. Create tests/unit/dispatch/ThrowExprHandlerDispatcherTest.cpp
          2. Test handler registration
          3. Test predicate matches only CXXThrowExpr
          4. Test throw with constructor arguments
          5. Test re-throw (throw;)
        </steps>
        <dependencies>Phase 6 complete</dependencies>
        <effort>2 hours</effort>
        <verification>All dispatcher tests pass</verification>
      </task>

      <task id="7.3" name="Create Cross-Handler Integration Tests">
        <description>Test exception handling integration with other handlers</description>
        <steps>
          1. Test throw in constructor body (ConstructorHandler + ThrowExprHandler)
          2. Test method call in try block (TryStmtHandler + MethodHandler + CallExprHandler)
          3. Test exception type matching (NameMangler consistency)
          4. Test throw with complex expression arguments
        </steps>
        <dependencies>Tasks 7.1, 7.2 complete</dependencies>
        <effort>2.5 hours</effort>
        <verification>All integration tests pass</verification>
      </task>

      <task id="7.4" name="Verify Existing Integration Tests">
        <description>Run all existing integration tests and verify they pass</description>
        <steps>
          1. Run ExceptionHandlingIntegrationTest.cpp
          2. Run ExceptionIntegrationTest.cpp
          3. Run ExceptionPerformanceTest.cpp
          4. Run ExceptionThreadSafetyTest.cpp
          5. Run ExceptionRuntimeTest.cpp
          6. Run ExceptionFrameTest.cpp
          7. Debug any failures, compare generated C code before/after
        </steps>
        <dependencies>Phase 6 complete</dependencies>
        <effort>2 hours</effort>
        <verification>All 9 integration tests pass</verification>
      </task>

      <task id="7.5" name="Create Test Helper Utilities">
        <description>Create assertion helpers for C AST verification</description>
        <steps>
          1. assertCallExprTo(expr, functionName) - verify CallExpr target
          2. assertIfStmtWithCondition(stmt, conditionCheck) - verify IfStmt structure
          3. assertVarDeclWithType(decl, typeName) - verify VarDecl type
          4. assertCompoundStmtSize(stmt, numChildren) - verify CompoundStmt size
        </steps>
        <dependencies>None (can be done in parallel with Phase 6)</dependencies>
        <effort>1.5 hours</effort>
        <verification>Helper functions work correctly in tests</verification>
      </task>

      <task id="7.6" name="Create ExceptionDispatcherTestFixture">
        <description>Create shared test fixture for exception dispatcher tests</description>
        <steps>
          1. Create fixture class with dispatcher setup
          2. Include all necessary handler registrations
          3. Provide helper methods for parsing exception code
          4. Include C ASTContext and mappers
          5. Reuse in TryStmtHandlerDispatcherTest and ThrowExprHandlerDispatcherTest
        </steps>
        <dependencies>None (can be done in parallel with Phase 6)</dependencies>
        <effort>1.5 hours</effort>
        <verification>Fixture reduces test boilerplate, tests pass</verification>
      </task>

      <task id="7.7" name="Document Test Migration and Update README">
        <description>Document test changes and update testing documentation</description>
        <steps>
          1. Document what changed in tests (string → AST assertions)
          2. Document new test files and their purpose
          3. Update README or TESTING.md with exception handler test info
          4. Document test helper utilities usage
        </steps>
        <dependencies>All Phase 7 tasks complete</dependencies>
        <effort>1 hour</effort>
        <verification>Documentation clear and accurate</verification>
      </task>
    </phase_7_tasks>
  </task_breakdown>

  <technical_debt_resolution>
    <debt_item id="TD1" name="Manual name mangling in TryCatchTransformer">
      <location>src/TryCatchTransformer.cpp line 233 (getMangledTypeName)</location>
      <location>src/TryCatchTransformer.cpp line 251 (getDestructorName)</location>
      <current_behavior>Returns simple class name without namespace prefix</current_behavior>
      <replacement>cpptoc::mangle_class(RD) and cpptoc::mangle_destructor(DD)</replacement>
      <resolution_phase>Phase 1</resolution_phase>
      <resolution_tasks>Tasks 1.2</resolution_tasks>
      <verification>No manual string concatenation with "__" separator</verification>
    </debt_item>

    <debt_item id="TD2" name="Manual name mangling in ThrowTranslator">
      <location>src/ThrowTranslator.cpp line 175 (getMangledTypeName)</location>
      <location>src/ThrowTranslator.cpp line 196 (getConstructorName)</location>
      <current_behavior>Returns simple class/constructor name without proper parameter encoding</current_behavior>
      <replacement>cpptoc::mangle_class(RD) and cpptoc::mangle_constructor(CD)</replacement>
      <resolution_phase>Phase 1</resolution_phase>
      <resolution_tasks>Tasks 1.3</resolution_tasks>
      <verification>Constructor names include parameter types</verification>
    </debt_item>

    <debt_item id="TD3" name="Placeholder exprToString in ThrowTranslator">
      <location>src/ThrowTranslator.cpp line 219</location>
      <current_behavior>Returns "/* expression */" for unsupported expression types</current_behavior>
      <replacement>Dispatcher delegation: disp.dispatch() → exprMapper.getCreated()</replacement>
      <resolution_phase>Phase 3</resolution_phase>
      <resolution_tasks>Tasks 3.2</resolution_tasks>
      <verification>No placeholders in generated throw code</verification>
    </debt_item>

    <debt_item id="TD4" name="Placeholder argumentsToString in ThrowTranslator">
      <location>src/ThrowTranslator.cpp line 203</location>
      <current_behavior>Limited by exprToString placeholder implementation</current_behavior>
      <replacement>Dispatcher delegation for each argument expression</replacement>
      <resolution_phase>Phase 3</resolution_phase>
      <resolution_tasks>Tasks 3.3</resolution_tasks>
      <verification>All constructor argument types handled</verification>
    </debt_item>

    <debt_item id="TD5" name="Placeholder stmtToString in TryCatchTransformer">
      <location>src/TryCatchTransformer.cpp line 258</location>
      <current_behavior>Returns placeholders "/* declaration */;", "/* function call */;", etc.</current_behavior>
      <replacement>Dispatcher delegation: disp.dispatch() → stmtMapper.getCreated()</replacement>
      <resolution_phase>Phase 4</resolution_phase>
      <resolution_tasks>Tasks 4.2</resolution_tasks>
      <verification>No placeholders in try/catch body code</verification>
    </debt_item>

    <debt_item id="TD6" name="String-based output in ThrowTranslator">
      <location>src/ThrowTranslator.cpp (entire generateThrowCode method)</location>
      <current_behavior>Generates C code as strings instead of C AST nodes</current_behavior>
      <replacement>Create C VarDecl, CallExpr nodes using CNodeBuilder/Clang API</replacement>
      <resolution_phase>Phase 5</resolution_phase>
      <resolution_tasks>Tasks 5.2, 5.3, 5.4, 5.5</resolution_tasks>
      <verification>generateThrowCode returns clang::Expr* (not std::string)</verification>
    </debt_item>

    <debt_item id="TD7" name="String-based output in TryCatchTransformer">
      <location>src/TryCatchTransformer.cpp (entire transformTryCatch method)</location>
      <current_behavior>Generates C code as strings instead of C AST nodes</current_behavior>
      <replacement>Create C IfStmt, CompoundStmt, VarDecl nodes using CNodeBuilder/Clang API</replacement>
      <resolution_phase>Phase 6</resolution_phase>
      <resolution_tasks>Tasks 6.2, 6.3, 6.4, 6.5, 6.6, 6.7</resolution_tasks>
      <verification>transformTryCatch returns clang::Stmt* (not std::string)</verification>
    </debt_item>
  </technical_debt_resolution>

  <test_strategy>
    <unit_tests>
      <test_category name="Handler Registration">
        <purpose>Verify handlers register with dispatcher correctly</purpose>
        <tests>
          <test>TryStmtHandler registration succeeds</test>
          <test>ThrowExprHandler registration succeeds</test>
          <test>Predicates match correct AST node types</test>
        </tests>
        <location>tests/unit/dispatch/TryStmtHandlerDispatcherTest.cpp</location>
        <location>tests/unit/dispatch/ThrowExprHandlerDispatcherTest.cpp</location>
      </test_category>

      <test_category name="Handler Translation">
        <purpose>Verify handlers create correct C AST nodes</purpose>
        <tests>
          <test>TryStmtHandler creates IfStmt with setjmp guard</test>
          <test>TryStmtHandler creates CompoundStmt for try body</test>
          <test>TryStmtHandler creates nested IfStmts for catch handlers</test>
          <test>ThrowExprHandler creates CallExpr to cxx_throw</test>
          <test>ThrowExprHandler creates VarDecl for exception allocation</test>
          <test>ThrowExprHandler handles re-throw</test>
        </tests>
        <location>tests/unit/dispatch/TryStmtHandlerDispatcherTest.cpp</location>
        <location>tests/unit/dispatch/ThrowExprHandlerDispatcherTest.cpp</location>
      </test_category>

      <test_category name="Name Mangling Integration">
        <purpose>Verify NameMangler API produces consistent names</purpose>
        <tests>
          <test>Exception type names match between throw and catch</test>
          <test>Destructor names match DestructorHandler output</test>
          <test>Constructor names include parameter types</test>
          <test>Namespace prefixes consistent across handlers</test>
        </tests>
        <location>tests/unit/dispatch/ExceptionNameManglingTest.cpp (new)</location>
      </test_category>

      <test_category name="Component Tests">
        <purpose>Verify TryCatchTransformer and ThrowTranslator work with dispatcher</purpose>
        <tests>
          <test>TryCatchTransformer with dispatcher delegation (Phase 4)</test>
          <test>ThrowTranslator with dispatcher delegation (Phase 3)</test>
          <test>Complex expression arguments translate correctly</test>
          <test>Complex statement bodies translate correctly</test>
        </tests>
        <location>tests/TryCatchTransformerTest.cpp (updated)</location>
        <location>tests/ThrowTranslatorTest.cpp (updated)</location>
      </test_category>
    </unit_tests>

    <integration_tests>
      <test_category name="Cross-Handler Integration">
        <purpose>Verify exception handlers work with other handlers</purpose>
        <tests>
          <test>Throw in constructor body (ConstructorHandler + ThrowExprHandler)</test>
          <test>Method call in try block (TryStmtHandler + MethodHandler + CallExprHandler)</test>
          <test>Throw with member access argument (ThrowExprHandler + MemberExprHandler)</test>
          <test>Nested try-catch blocks</test>
          <test>Virtual method call in try block (VirtualMethodHandler integration)</test>
        </tests>
        <location>tests/unit/dispatch/ExceptionCrossHandlerTest.cpp (new)</location>
      </test_category>

      <test_category name="End-to-End Integration">
        <purpose>Verify runtime behavior after dispatcher integration</purpose>
        <tests>
          <test>Basic try-catch with single handler</test>
          <test>Multiple catch handlers</test>
          <test>Catch-all handler (catch(...))</test>
          <test>Nested try-catch blocks</test>
          <test>Re-throw support</test>
          <test>Stack unwinding with destructors</test>
          <test>Exception propagation across functions</test>
        </tests>
        <location>tests/ExceptionHandlingIntegrationTest.cpp (existing, should pass unchanged)</location>
        <location>tests/ExceptionIntegrationTest.cpp (existing)</location>
      </test_category>

      <test_category name="Performance and Concurrency">
        <purpose>Verify non-functional requirements preserved</purpose>
        <tests>
          <test>Exception handling performance characteristics maintained</test>
          <test>Thread-local exception stack thread-safe</test>
        </tests>
        <location>tests/ExceptionPerformanceTest.cpp (existing)</location>
        <location>tests/ExceptionThreadSafetyTest.cpp (existing)</location>
      </test_category>
    </integration_tests>

    <migration_tests>
      <test_file name="TryCatchTransformerTest.cpp">
        <migration_approach>Update test fixture, change string assertions to AST assertions</migration_approach>
        <phase>Phase 6 (after string-to-AST refactoring)</phase>
        <effort>2 hours</effort>
      </test_file>

      <test_file name="ThrowTranslatorTest.cpp">
        <migration_approach>Update test fixture, change string assertions to AST assertions</migration_approach>
        <phase>Phase 5 (after string-to-AST refactoring)</phase>
        <effort>2 hours</effort>
      </test_file>

      <test_file name="ExceptionFrameTest.cpp">
        <migration_approach>No migration needed - ExceptionFrameGenerator remains standalone</migration_approach>
        <phase>N/A</phase>
        <effort>0 hours</effort>
      </test_file>

      <test_file name="Exception*IntegrationTest.cpp">
        <migration_approach>No migration needed - verify tests continue to pass</migration_approach>
        <phase>Phase 7 (verification only)</phase>
        <effort>1 hour</effort>
      </test_file>
    </migration_tests>

    <test_coverage_goals>
      <goal>100% handler registration coverage (all handlers registered successfully)</goal>
      <goal>100% predicate coverage (all AST node types tested)</goal>
      <goal>90%+ C AST creation coverage (all node types created correctly)</goal>
      <goal>100% name mangling integration coverage (all name types tested)</goal>
      <goal>All existing test cases covered by new dispatcher tests</goal>
      <goal>All integration tests pass unchanged (behavior preservation)</goal>
    </test_coverage_goals>
  </test_strategy>

  <risk_mitigation>
    <risk id="R1" name="NameMangler produces incompatible name format" severity="High" probability="Low">
      <detection_phase>Phase 1 (Task 1.1)</detection_phase>
      <detection_method>Test comparison of NameMangler vs manual mangling output</detection_method>
      <mitigation>
        <approach>Compare outputs before migration, adjust NameMangler if needed</approach>
        <fallback>Extend NameMangler to support compatibility mode</fallback>
        <contingency>Revert to manual mangling temporarily, file issue for NameMangler fix</contingency>
      </mitigation>
    </risk>

    <risk id="R2" name="Expression handler missing for some expression type" severity="Medium" probability="Medium">
      <detection_phase>Phase 3 (Tasks 3.2, 3.3, 3.4)</detection_phase>
      <detection_method>disp.dispatch() returns false, assertion failure in tests</detection_method>
      <mitigation>
        <approach>Add missing expression handler following existing patterns</approach>
        <fallback>Temporary placeholder with warning log for unsupported expressions</fallback>
        <contingency>Document unsupported expressions, prioritize based on real-world usage</contingency>
      </mitigation>
    </risk>

    <risk id="R3" name="Statement handler missing for some statement type" severity="Medium" probability="Medium">
      <detection_phase>Phase 4 (Tasks 4.2, 4.3, 4.4)</detection_phase>
      <detection_method>disp.dispatch() returns false for statement in try/catch body</detection_method>
      <mitigation>
        <approach>Add missing statement handler or extend StatementHandler</approach>
        <fallback>Skip statement with warning log</fallback>
        <contingency>Document unsupported statements, prioritize based on real-world usage</contingency>
      </mitigation>
    </risk>

    <risk id="R4" name="CNodeBuilder missing required node types" severity="High" probability="Low">
      <detection_phase>Phase 5, Phase 6 (AST node creation tasks)</detection_phase>
      <detection_method>Compilation errors or runtime assertions in CNodeBuilder</detection_method>
      <mitigation>
        <approach>Extend CNodeBuilder to support required node types (VarDecl, CallExpr, IfStmt)</approach>
        <fallback>Use Clang API directly (VarDecl::Create, CallExpr::Create, etc.)</fallback>
        <contingency>Study existing Clang AST usage in handlers for correct API calls</contingency>
      </mitigation>
    </risk>

    <risk id="R5" name="AST node parent/context setting incorrect" severity="High" probability="Medium">
      <detection_phase>Phase 5, Phase 6 (AST node creation tasks)</detection_phase>
      <detection_method>AST consistency errors, crashes during code generation</detection_method>
      <mitigation>
        <approach>Study existing handlers (MethodHandler, ConstructorHandler) for correct pattern</approach>
        <fallback>Use DeclContext utilities to set correct parent relationships</fallback>
        <contingency>Add AST validation utilities to detect incorrect parent/context early</contingency>
      </mitigation>
    </risk>

    <risk id="R6" name="ExceptionFrameGenerator produces strings, not AST" severity="Medium" probability="High">
      <detection_phase>Phase 6 (Task 6.6)</detection_phase>
      <detection_method>Cannot integrate frame push/pop code into C AST</detection_method>
      <mitigation>
        <approach>Option 1: Inline frame push/pop logic into TryCatchTransformer (create AST nodes directly)</approach>
        <approach>Option 2: Extend ExceptionFrameGenerator to return C AST nodes instead of strings</approach>
        <approach>Option 3: Parse frame push/pop strings back into AST (avoid this)</approach>
        <fallback>Use Option 1 (inline) for Phase 6, refactor to Option 2 in future if needed</fallback>
      </mitigation>
    </risk>

    <risk id="R7" name="Complex control flow hard to represent in AST" severity="Medium" probability="Medium">
      <detection_phase>Phase 6 (Tasks 6.4, 6.5, 6.7)</detection_phase>
      <detection_method>Incorrect nesting, missing statements in generated AST</detection_method>
      <mitigation>
        <approach>Build incrementally: single catch first, then multiple catches, then nested try</approach>
        <fallback>Study existing control flow handlers (IfStmtHandler, WhileStmtHandler if they exist)</fallback>
        <contingency>Create AST visualization/debugging utilities to inspect structure</contingency>
      </mitigation>
    </risk>

    <risk id="R8" name="Integration tests fail due to behavior changes" severity="High" probability="Low">
      <detection_phase>Phase 7 (Task 7.4)</detection_phase>
      <detection_method>Runtime failures in exception handling tests</detection_method>
      <mitigation>
        <approach>Compare generated C code before/after migration for functional equivalence</approach>
        <fallback>Debug carefully, use CodeGenerator to emit C code from AST for comparison</fallback>
        <contingency>Rollback to previous phase, investigate differences in generated code</contingency>
      </mitigation>
    </risk>

    <risk id="R9" name="Test migration complexity" severity="Low" probability="Medium">
      <detection_phase>Phase 7 (all tasks)</detection_phase>
      <detection_method>Tests become hard to read and maintain</detection_method>
      <mitigation>
        <approach>Create helper assertion functions (assertCallExprTo, assertIfStmtWithCondition)</approach>
        <approach>Create shared test fixture (ExceptionDispatcherTestFixture)</approach>
        <fallback>Use CodeGenerator for string comparison as secondary verification</fallback>
        <contingency>Keep both string-based and AST-based assertions during transition</contingency>
      </mitigation>
    </risk>

    <risk id="R10" name="Frame variable naming conflicts in nested try-catch" severity="Medium" probability="Medium">
      <detection_phase>Phase 2 (Task 2.2), Phase 6 (Tasks 6.2)</detection_phase>
      <detection_method>Compilation errors due to duplicate variable names</detection_method>
      <mitigation>
        <approach>Use counter-based naming: frame_0, frame_1, frame_2, etc.</approach>
        <approach>Use UUID-based naming for guaranteed uniqueness</approach>
        <fallback>Pass unique ID from TryStmtHandler to TryCatchTransformer</fallback>
        <contingency>Create frame name generator utility (singleton with atomic counter)</contingency>
      </mitigation>
    </risk>

    <risk id="R11" name="Re-throw needs access to current exception frame" severity="Medium" probability="Medium">
      <detection_phase>Phase 5 (Task 5.5), when implementing re-throw</detection_phase>
      <detection_method>Re-throw code cannot access frame variable name</detection_method>
      <mitigation>
        <approach>Option 1: Use fixed runtime name (__cxx_exception_stack thread-local)</approach>
        <approach>Option 2: Pass frame variable name via ExceptionMapper</approach>
        <approach>Option 3: Generate code that accesses thread-local stack directly</approach>
        <fallback>Use Option 1 (thread-local stack) - matches existing runtime implementation</fallback>
      </mitigation>
    </risk>
  </risk_mitigation>

  <integration_points>
    <integration_point id="IP1" name="Method call in try block">
      <scenario>Try block containing method call expression</scenario>
      <handler_chain>TryStmtHandler → CompoundStmtHandler → CallExprHandler → MethodHandler</handler_chain>
      <current_gap>TryCatchTransformer.stmtToString() cannot handle method calls (returns placeholder)</current_gap>
      <resolution_phase>Phase 4</resolution_phase>
      <resolution_tasks>Tasks 4.2, 4.3</resolution_tasks>
      <verification>Test with try { obj.method(); } compiles and runs correctly</verification>
    </integration_point>

    <integration_point id="IP2" name="Throw in constructor">
      <scenario>Throw expression inside constructor body</scenario>
      <handler_chain>ConstructorHandler → CompoundStmtHandler → ThrowExprHandler</handler_chain>
      <current_gap>ThrowTranslator is standalone, not integrated with ConstructorHandler</current_gap>
      <resolution_phase>Phase 2, Phase 5</resolution_phase>
      <resolution_tasks>Tasks 2.4, 5.5</resolution_tasks>
      <verification>Test with constructor throwing exception compiles and propagates correctly</verification>
    </integration_point>

    <integration_point id="IP3" name="Exception class translation">
      <scenario>Exception class with members, methods, inheritance</scenario>
      <handler_chain>RecordHandler → MethodHandler → DestructorHandler</handler_chain>
      <name_consistency>Exception class names from RecordHandler must match type strings in ThrowExprHandler</name_consistency>
      <current_gap>Manual name mangling may not match class names from RecordHandler</current_gap>
      <resolution_phase>Phase 1</resolution_phase>
      <resolution_tasks>Tasks 1.2, 1.3</resolution_tasks>
      <verification>Exception type matching works correctly in catch handlers (strcmp succeeds)</verification>
    </integration_point>

    <integration_point id="IP4" name="Exception frame in function">
      <scenario>Try-catch inside function body</scenario>
      <handler_chain>FunctionHandler → CompoundStmtHandler → TryStmtHandler → ExceptionFrameGenerator</handler_chain>
      <scoping>Frame variables must be unique within function scope (nested try-catch)</scoping>
      <current_gap>Fixed frame variable names may conflict in nested try-catch</current_gap>
      <resolution_phase>Phase 2, Phase 6</resolution_phase>
      <resolution_tasks>Tasks 2.2, 6.2</resolution_tasks>
      <verification>Nested try-catch blocks have unique frame variable names</verification>
    </integration_point>

    <integration_point id="IP5" name="Re-throw in catch">
      <scenario>Re-throw (throw;) inside catch handler</scenario>
      <handler_chain>TryStmtHandler → catch body → ThrowExprHandler (re-throw)</handler_chain>
      <frame_access>Re-throw needs access to current exception frame variable</frame_access>
      <current_gap>Frame variable name not available to ThrowExprHandler</current_gap>
      <resolution_phase>Phase 5</resolution_phase>
      <resolution_tasks>Task 5.5</resolution_tasks>
      <resolution_approach>Use thread-local stack access (__cxx_exception_stack) instead of local frame variable</resolution_approach>
      <verification>Re-throw generates cxx_throw(__cxx_exception_stack->exception_object, __cxx_exception_stack->exception_type)</verification>
    </integration_point>

    <integration_point id="IP6" name="Throw with complex arguments">
      <scenario>Throw with member access, binary operator, or function call arguments</scenario>
      <handler_chain>ThrowExprHandler → ConstructorHandler → MemberExprHandler / BinaryOperatorHandler / CallExprHandler</handler_chain>
      <current_gap>ThrowTranslator.exprToString() returns placeholders for complex expressions</current_gap>
      <resolution_phase>Phase 3</resolution_phase>
      <resolution_tasks>Tasks 3.2, 3.3, 3.4</resolution_tasks>
      <verification>Test with throw Error(obj.field + getValue()) translates all arguments correctly</verification>
    </integration_point>
  </integration_points>

  <success_criteria>
    <criterion id="SC1" name="All exception features work through dispatcher">
      <description>TryStmtHandler and ThrowExprHandler handle all exception-related AST nodes</description>
      <verification>Dispatch CXXTryStmt and CXXThrowExpr, handlers invoked successfully</verification>
      <phase>Phase 2 onwards</phase>
    </criterion>

    <criterion id="SC2" name="No manual mangling remains">
      <description>All name generation uses cpptoc::mangle_* functions from NameMangler API</description>
      <verification>Grep for manual "__" concatenation in exception components, zero results</verification>
      <phase>Phase 1</phase>
    </criterion>

    <criterion id="SC3" name="No placeholder methods remain">
      <description>exprToString, argumentsToString, stmtToString all use dispatcher delegation</description>
      <verification>Grep for "/* expression */" and "/* function call */;" placeholders, zero in generated code</verification>
      <phase>Phase 3, Phase 4</phase>
    </criterion>

    <criterion id="SC4" name="All 9 tests migrated and passing">
      <description>All existing exception tests work with dispatcher pattern</description>
      <verification>Run all test files, zero failures</verification>
      <phase>Phase 7</phase>
    </criterion>

    <criterion id="SC5" name="Dispatcher-specific tests added">
      <description>New tests verify handler registration, predicates, and dispatcher integration</description>
      <verification>TryStmtHandlerDispatcherTest.cpp and ThrowExprHandlerDispatcherTest.cpp exist and pass</verification>
      <phase>Phase 7</phase>
    </criterion>

    <criterion id="SC6" name="Handlers follow dispatcher pattern">
      <description>Handlers have static registerWith, canHandle, handleXXX methods matching dispatcher interface</description>
      <verification>Code review confirms pattern compliance</verification>
      <phase>Phase 2</phase>
    </criterion>

    <criterion id="SC7" name="Components remain reusable">
      <description>TryCatchTransformer and ThrowTranslator can still be used standalone (with dispatcher parameter)</description>
      <verification>Components have no hard dispatcher dependency, can be tested in isolation</verification>
      <phase>All phases</phase>
    </criterion>

    <criterion id="SC8" name="C AST creation, not string generation">
      <description>Exception handlers create C AST nodes (Expr*, Stmt*), not strings</description>
      <verification>generateThrowCode returns Expr*, transformTryCatch returns Stmt*</verification>
      <phase>Phase 5, Phase 6</phase>
    </criterion>

    <criterion id="SC9" name="Name consistency across handlers">
      <description>NameMangler produces consistent names for classes, methods, destructors, constructors</description>
      <verification>Exception type matching works in catch handlers (strcmp succeeds)</verification>
      <phase>Phase 1</phase>
    </criterion>

    <criterion id="SC10" name="Integration tests pass unchanged">
      <description>All existing integration tests continue to pass without modification</description>
      <verification>Run ExceptionHandlingIntegrationTest.cpp and others, all pass</verification>
      <phase>Phase 7</phase>
    </criterion>
  </success_criteria>

  <execution_order>
    <sequence>
      <step number="1" phase="Phase 1" duration="2-3 hours">
        Fix name mangling (Tasks 1.1, 1.2, 1.3, 1.4)
        Critical prerequisite for all other work
      </step>

      <step number="2" phase="Phase 2" duration="4-6 hours">
        Create handler skeletons (Tasks 2.1, 2.2, 2.3, 2.4, 2.5)
        Verify dispatcher mechanics work before complex refactoring
      </step>

      <step number="3" phase="Phase 3" duration="5-7 hours">
        Replace ThrowTranslator placeholders (Tasks 3.1, 3.2, 3.3, 3.4)
        Enable throw expression translation via dispatcher
      </step>

      <step number="4" phase="Phase 4" duration="5-7 hours">
        Replace TryCatchTransformer placeholders (Tasks 4.1, 4.2, 4.3, 4.4, 4.5)
        Enable try/catch body translation via dispatcher
      </step>

      <step number="5" phase="Phase 5" duration="8-12 hours">
        String-to-AST refactoring for ThrowTranslator (Tasks 5.1, 5.2, 5.3, 5.4, 5.5, 5.6)
        Align with 3-stage pipeline architecture
      </step>

      <step number="6" phase="Phase 6" duration="10-15 hours">
        String-to-AST refactoring for TryCatchTransformer (Tasks 6.1, 6.2, 6.3, 6.4, 6.5, 6.6, 6.7, 6.8)
        Most complex phase, create control flow C AST structure
      </step>

      <step number="7" phase="Phase 7" duration="10-14 hours">
        Test migration and new tests (Tasks 7.1, 7.2, 7.3, 7.4, 7.5, 7.6, 7.7)
        Verify all functionality, comprehensive test coverage
      </step>
    </sequence>

    <parallelization_opportunities>
      <parallel_work>
        <phases>Phase 2 (handler creation)</phases>
        <tasks>Task 2.1-2.2 (TryStmtHandler) and Task 2.3-2.4 (ThrowExprHandler) can be done in parallel</tasks>
        <benefit>Reduce Phase 2 duration from 6 hours to 3-4 hours</benefit>
      </parallel_work>

      <parallel_work>
        <phases>Phase 7 (test creation)</phases>
        <tasks>Tasks 7.1, 7.2, 7.5, 7.6 can be done in parallel</tasks>
        <benefit>Reduce Phase 7 duration from 14 hours to 8-10 hours</benefit>
      </parallel_work>

      <sequential_constraints>
        <constraint>Phase 1 must complete before Phase 2 (name mangling prerequisite)</constraint>
        <constraint>Phase 2 must complete before Phase 3 and 4 (handlers must exist)</constraint>
        <constraint>Phases 3 and 4 can run in parallel (independent components)</constraint>
        <constraint>Phase 5 depends on Phase 3 (ThrowTranslator dispatcher integration)</constraint>
        <constraint>Phase 6 depends on Phase 4 (TryCatchTransformer dispatcher integration)</constraint>
        <constraint>Phase 7 depends on Phases 5 and 6 (AST refactoring complete)</constraint>
      </sequential_constraints>
    </parallelization_opportunities>

    <critical_path>
      Phase 1 → Phase 2 → Phase 4 → Phase 6 → Phase 7
      (TryCatchTransformer is on critical path due to complexity)

      ThrowTranslator path (can run in parallel with TryCatchTransformer):
      Phase 1 → Phase 2 → Phase 3 → Phase 5
    </critical_path>

    <recommended_schedule>
      <day number="1">Phase 1 (2-3 hours) + Phase 2 start (1-2 hours)</day>
      <day number="2">Phase 2 complete (2-4 hours) + Phase 3 and 4 in parallel (start)</day>
      <day number="3">Phase 3 and 4 complete (6-10 hours total if parallel)</day>
      <day number="4">Phase 5 (8-12 hours)</day>
      <day number="5">Phase 6 start (4-6 hours)</day>
      <day number="6">Phase 6 complete (6-9 hours remaining)</day>
      <day number="7">Phase 7 (10-14 hours, parallelizable to 8-10 hours)</day>

      Total: 37-55 hours over 5-7 working days
      With parallelization: 30-45 hours over 5-6 working days
    </recommended_schedule>
  </execution_order>

  <estimated_effort>
    <phase_estimates>
      <phase number="1" name="Name Mangling Migration" effort="2-3 hours" complexity="Low" />
      <phase number="2" name="Handler Skeleton Creation" effort="4-6 hours" complexity="Medium" />
      <phase number="3" name="Placeholder Replacement - ThrowTranslator" effort="5-7 hours" complexity="Medium" />
      <phase number="4" name="Placeholder Replacement - TryCatchTransformer" effort="5-7 hours" complexity="Medium" />
      <phase number="5" name="String-to-AST - ThrowTranslator" effort="8-12 hours" complexity="High" />
      <phase number="6" name="String-to-AST - TryCatchTransformer" effort="10-15 hours" complexity="High" />
      <phase number="7" name="Test Migration" effort="10-14 hours" complexity="Medium" />
    </phase_estimates>

    <total_effort>
      <baseline>44-64 hours (baseline estimate)</baseline>
      <with_buffer>52-76 hours (with 20% buffer for unexpected issues)</with_buffer>
      <optimistic>37-55 hours (with parallelization)</optimistic>
      <pessimistic>60-80 hours (if major blockers encountered)</pessimistic>
    </total_effort>

    <working_days>
      <baseline>5.5-8 working days (8 hours per day)</baseline>
      <with_buffer>6.5-9.5 working days</with_buffer>
      <optimistic>4.5-7 working days (with parallelization)</optimistic>
      <pessimistic>7.5-10 working days (if major blockers)</pessimistic>
    </working_days>

    <effort_breakdown_by_activity>
      <activity name="Name mangling fixes" effort="2-3 hours" percentage="4-5%" />
      <activity name="Handler creation" effort="4-6 hours" percentage="9-10%" />
      <activity name="Placeholder replacement" effort="10-14 hours" percentage="20-25%" />
      <activity name="String-to-AST refactoring" effort="18-27 hours" percentage="40-45%" />
      <activity name="Test migration and creation" effort="10-14 hours" percentage="20-25%" />
    </effort_breakdown_by_activity>

    <confidence_level>Medium-High</confidence_level>
    <confidence_rationale>
      Estimates based on:
      - Code size analysis of existing components (300-500 lines per component)
      - Complexity of similar work (handler creation patterns established)
      - Research findings on technical debt locations and scope

      Uncertainty factors:
      - AST node creation complexity (CNodeBuilder vs Clang API)
      - Test migration complexity (AST assertions vs string assertions)
      - Integration debugging time (cross-handler issues)

      Buffer includes time for:
      - Debugging AST structure issues
      - Fixing test failures
      - Code review and iteration
      - Documentation updates
    </confidence_rationale>
  </estimated_effort>

  <recommendations>
    <recommendation priority="Critical" id="R1">
      <title>Fix Name Mangling First</title>
      <rationale>
        Name consistency is critical for exception handling. If type names don't match between
        throw site and catch site, exceptions won't be caught. This is a prerequisite for all
        other work and must be done first.
      </rationale>
      <action>Complete Phase 1 before starting any other phases</action>
      <impact>Enables correct exception type matching throughout the system</impact>
    </recommendation>

    <recommendation priority="Critical" id="R2">
      <title>Create Minimal Handlers Before Refactoring</title>
      <rationale>
        Verify dispatcher mechanics work before tackling complex AST generation. Creating
        handler skeletons that delegate to existing components reduces risk and allows
        incremental integration.
      </rationale>
      <action>Complete Phase 2 handler creation before starting placeholder replacement or AST refactoring</action>
      <impact>Reduces risk of major architectural issues, enables early testing</impact>
    </recommendation>

    <recommendation priority="High" id="R3">
      <title>Keep ExceptionFrameGenerator As-Is</title>
      <rationale>
        ExceptionFrameGenerator is a utility class for code generation, not an AST handler.
        It's complete, tested, and works correctly. Forcing it into dispatcher pattern adds
        no value and increases complexity.
      </rationale>
      <action>Use ExceptionFrameGenerator directly from TryStmtHandler without dispatcher registration</action>
      <impact>Reduces scope, avoids unnecessary refactoring</impact>
    </recommendation>

    <recommendation priority="High" id="R4">
      <title>Refactor String-to-AST Incrementally</title>
      <rationale>
        String-to-AST conversion is the highest risk area. Building incrementally (simple cases
        first, then complex) allows testing at each step and reduces chance of major failures.
      </rationale>
      <action>
        Phase 5: Start with simple expressions (literals, DeclRefExpr), then add complex (BinaryOperator, CallExpr)
        Phase 6: Start with single catch handler, then multiple catches, then nested try-catch
      </action>
      <impact>Reduces risk, enables early detection of issues</impact>
    </recommendation>

    <recommendation priority="High" id="R5">
      <title>Parallelize ThrowTranslator and TryCatchTransformer Work</title>
      <rationale>
        After Phase 2 completes, ThrowTranslator (Phases 3, 5) and TryCatchTransformer (Phases 4, 6)
        are independent. Working on them in parallel can reduce total calendar time by 30-40%.
      </rationale>
      <action>After Phase 2, work on Phase 3+5 (ThrowTranslator) and Phase 4+6 (TryCatchTransformer) in parallel</action>
      <impact>Reduces total time from 7 days to 5 days (if resources available)</impact>
    </recommendation>

    <recommendation priority="Medium" id="R6">
      <title>Create Test Helpers Early</title>
      <rationale>
        AST assertions are more complex than string assertions. Creating helper functions early
        (Phase 7 Task 7.5, 7.6) reduces test boilerplate and makes tests easier to read/maintain.
      </rationale>
      <action>Create ExceptionDispatcherTestFixture and assertion helpers early in Phase 7 (or even Phase 6)</action>
      <impact>Improves test readability, reduces migration effort</impact>
    </recommendation>

    <recommendation priority="Medium" id="R7">
      <title>Use Thread-Local Stack for Re-throw</title>
      <rationale>
        Re-throw needs access to current exception frame. Using thread-local stack
        (__cxx_exception_stack) is simpler than passing frame variable names through context.
        Matches existing runtime implementation.
      </rationale>
      <action>Implement re-throw using thread-local stack access in Phase 5</action>
      <impact>Simplifies implementation, avoids need for ExceptionMapper</impact>
    </recommendation>

    <recommendation priority="Medium" id="R8">
      <title>Inline Frame Push/Pop in Phase 6</title>
      <rationale>
        ExceptionFrameGenerator produces strings. Extending it to produce AST adds complexity.
        Inlining frame push/pop logic in TryCatchTransformer is simpler for Phase 6, can be
        refactored later if needed.
      </rationale>
      <action>Create frame push/pop C AST nodes directly in TryCatchTransformer (Phase 6 Task 6.6)</action>
      <impact>Reduces Phase 6 complexity, defers ExceptionFrameGenerator refactoring</impact>
    </recommendation>

    <recommendation priority="Low" id="R9">
      <title>Add Dispatcher Tests Before Migrating Existing Tests</title>
      <rationale>
        Creating new dispatcher tests (TryStmtHandlerDispatcherTest, ThrowExprHandlerDispatcherTest)
        validates new architecture. Existing tests validate behavior preservation. Having both
        provides comprehensive coverage during migration.
      </rationale>
      <action>Complete Phase 7 Tasks 7.1, 7.2 (new tests) before updating existing tests</action>
      <impact>Provides safety net during migration, validates both architecture and behavior</impact>
    </recommendation>

    <recommendation priority="Low" id="R10">
      <title>Document Design Decisions</title>
      <rationale>
        Several design decisions made during planning (frame variable naming, re-throw approach,
        frame push/pop inlining). Documenting these helps future maintainers understand why
        certain approaches were chosen.
      </rationale>
      <action>Add design decision comments in code and update architecture documentation</action>
      <impact>Improves maintainability, helps onboarding</impact>
    </recommendation>
  </recommendations>

  <quality_report>
    <research_coverage>
      <finding source="exception-dispatcher-research.md" coverage="100%">
        All research findings incorporated into plan:
        - Dispatcher patterns (registration, predicates, visitors) → Phase 2
        - Name mangling locations and replacements → Phase 1
        - Placeholder method locations → Phases 3, 4
        - Technical debt catalog → technical_debt_resolution section
        - Integration points → integration_points section
        - Test migration strategy → test_strategy section
        - Complexity assessment → effort estimates
      </finding>
    </research_coverage>

    <completeness_assessment>
      <area name="Implementation Phases" completeness="100%">
        All 7 phases defined with clear scope, deliverables, tests, success criteria, risks, and effort estimates.
        Phases cover entire migration: name mangling → handler creation → placeholder replacement → AST refactoring → testing.
      </area>

      <area name="Task Breakdown" completeness="100%">
        44 tasks defined across all phases. Each task has description, steps, dependencies, effort, and verification.
        Tasks are granular enough to be actionable (0.5-3.5 hours each).
      </area>

      <area name="Technical Debt Resolution" completeness="100%">
        All 7 technical debt items from research mapped to specific phases and tasks.
        Each item has current behavior, replacement approach, and verification criteria.
      </area>

      <area name="Test Strategy" completeness="100%">
        Comprehensive test strategy covering unit tests, integration tests, migration tests.
        Test categories defined with purpose, specific tests, and locations.
        Migration approach specified for each existing test file.
      </area>

      <area name="Risk Mitigation" completeness="100%">
        11 risks identified with severity, probability, detection phase, mitigation approaches, and contingencies.
        Risks cover technical issues (AST creation, name mangling) and process issues (test migration, integration).
      </area>

      <area name="Integration Points" completeness="100%">
        6 integration points identified with scenarios, handler chains, gaps, resolutions, and verification.
        Covers cross-handler interactions (method calls in try, throw in constructor, etc.).
      </area>

      <area name="Success Criteria" completeness="100%">
        10 specific, measurable success criteria defined.
        Each criterion has description, verification method, and target phase.
      </area>

      <area name="Execution Order" completeness="100%">
        7-step sequence defined with phase dependencies, parallelization opportunities, critical path analysis.
        Includes recommended schedule and working day estimates.
      </area>

      <area name="Effort Estimates" completeness="100%">
        Effort estimates provided for all phases, tasks, and activities.
        Includes baseline, optimistic, pessimistic scenarios with confidence level and rationale.
      </area>

      <area name="Recommendations" completeness="100%">
        10 prioritized recommendations covering critical decisions, risk reduction, and best practices.
        Each recommendation has rationale, action, and impact.
      </area>
    </completeness_assessment>

    <feasibility_assessment>
      <technical_feasibility rating="High">
        All required APIs verified to exist:
        - NameMangler API functions (mangle_class, mangle_constructor, etc.) - verified in NameMangler.h
        - Dispatcher interface (addHandler, dispatch, getters) - verified in research
        - Clang AST node creation (VarDecl::Create, CallExpr::Create, etc.) - standard Clang API
        - Handler patterns - multiple examples exist in codebase

        Potential issues:
        - CNodeBuilder may not support all node types (can use Clang API directly)
        - ExceptionFrameGenerator produces strings (can inline frame logic)
        - Complex control flow AST structure (can build incrementally)

        All issues have identified mitigations and fallbacks.
      </technical_feasibility>

      <resource_feasibility rating="Medium-High">
        Total effort: 37-55 hours (optimistic) to 60-80 hours (pessimistic)
        Working days: 5-7 days (optimistic) to 7.5-10 days (pessimistic)

        Assumptions:
        - Single developer (solo work as per CLAUDE.md)
        - 8-hour working days
        - Some tasks parallelizable (handler creation, test creation)

        Risks:
        - Unexpected blockers could extend timeline
        - Integration debugging may take longer than estimated
        - Test migration complexity may be underestimated

        Mitigation: 20% buffer included in estimates
      </resource_feasibility>

      <schedule_feasibility rating="High">
        Execution order clearly defined with dependencies.
        Critical path identified: Phase 1 → 2 → 4 → 6 → 7
        Parallelization opportunities: Phases 3+5 can run parallel to 4+6

        With parallelization: 5-6 working days
        Without parallelization: 7-9 working days

        Realistic schedule with daily milestones provided.
      </schedule_feasibility>

      <overall_feasibility rating="High">
        Plan is technically sound, well-researched, and comprehensive.
        All major risks identified with mitigations.
        Effort estimates reasonable based on code size and complexity analysis.
        Incremental approach reduces risk of major failures.

        Recommendation: Proceed with implementation following this plan.
      </overall_feasibility>
    </feasibility_assessment>

    <confidence_rationale>
      <high_confidence_areas>
        - Dispatcher patterns (verified across multiple handlers)
        - NameMangler API (verified in source code)
        - Technical debt locations (precise line numbers from research)
        - Test file structure (examined actual test files)
        - Handler registration patterns (consistent across all handlers)
        - Integration points (analyzed handler interaction chains)
      </high_confidence_areas>

      <medium_confidence_areas>
        - Effort estimates (based on code size, not empirical data)
        - AST node creation complexity (depends on CNodeBuilder capabilities)
        - Test migration complexity (depends on assertion strategies)
        - Frame push/pop integration (depends on chosen approach)
      </medium_confidence_areas>

      <low_confidence_areas>
        - Exact debugging time needed (highly variable)
        - Integration test pass rate (depends on behavior preservation)
        - Parallelization benefits (depends on developer workflow)
      </low_confidence_areas>

      <overall_confidence>High</overall_confidence>
      <rationale>
        All critical information verified from source code.
        Research findings based on actual implementation, not speculation.
        Multiple fallback strategies for identified risks.
        Incremental approach allows course correction.
        Plan is detailed enough to execute but flexible enough to adapt.
      </rationale>
    </confidence_rationale>

    <verified_elements>
      <element>Dispatcher registration pattern (verified in MethodHandler, ReturnStmtHandler)</element>
      <element>Handler method signatures (verified in multiple handlers)</element>
      <element>NameMangler API functions (verified in NameMangler.h)</element>
      <element>Manual name mangling locations (verified in TryCatchTransformer.cpp, ThrowTranslator.cpp with line numbers)</element>
      <element>Placeholder method locations (verified in source files)</element>
      <element>Test file structure (verified in test files)</element>
      <element>Mapper access patterns (verified in handler implementations)</element>
      <element>Expression-as-statement pattern (verified in CompoundStmtHandler)</element>
      <element>ExceptionFrameGenerator completeness (verified 17 passing tests mentioned in research)</element>
    </verified_elements>

    <assumed_elements>
      <element>Exact effort required for each task (based on complexity estimation)</element>
      <element>Test migration complexity (depends on specific assertion strategies)</element>
      <element>CNodeBuilder capabilities (may need to use Clang API directly)</element>
      <element>Integration test compatibility (assumes behavior preservation)</element>
      <element>Parallelization efficiency (depends on development workflow)</element>
      <element>Debugging time (highly variable based on issues encountered)</element>
    </assumed_elements>
  </quality_report>
</plan>
