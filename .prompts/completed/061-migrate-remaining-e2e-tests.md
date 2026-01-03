<objective>
Migrate the remaining 6 E2E test files from HandlerContext to CppToCVisitorDispatcher pattern, following the proven pattern from E2EPhase1Test.

WHY this matters: These E2E tests validate advanced transpiler features (control flow, pointers, structs, classes, inheritance). They must be migrated to complete the HandlerContext retirement and ensure the dispatcher pattern supports all functionality.
</objective>

<context>
Project: C++ to C transpiler using Clang frontend
Current State: E2EPhase1Test successfully migrated and all tests passing

E2E Test Files to Migrate (in this order):
1. tests/e2e/phase2/ControlFlowE2ETest.cpp (if/else, loops)
2. tests/e2e/phase3/GlobalVariablesE2ETest.cpp (global vars)
3. tests/e2e/phase4/PointersE2ETest.cpp (pointer operations)
4. tests/e2e/phase5/StructsE2ETest.cpp (C++ structs)
5. tests/e2e/phase6/ClassesE2ETest.cpp (C++ classes)
6. tests/e2e/phase46/MultipleInheritanceE2ETest.cpp (multiple inheritance)

Migration Pattern Source:
@tests/e2e/phase1/E2EPhase1Test.cpp (proven working example)
@tests/e2e/E2ETestExample_DISPATCHER_PATTERN.cpp (template)
@tests/fixtures/DispatcherTestHelper.h (test infrastructure)

Review CLAUDE.md for project conventions.
</context>

<requirements>

1. **Migrate Each Test File**:
   - Replace HandlerContext with DispatcherTestHelper
   - Update includes to use dispatcher handlers
   - Modify runPipeline() method to use createDispatcherPipeline()
   - Register appropriate handlers for each test's needs
   - Remove DISABLED_ prefix from tests
   - Update CMakeLists.txt to uncomment the test target

2. **Follow Proven Pattern** from E2EPhase1Test:
   ```cpp
   // Create pipeline
   auto pipeline = cpptoc::test::createDispatcherPipeline(cppCode);

   // Register handlers (order matters!)
   TypeHandler::registerWith(*pipeline.dispatcher);
   ParameterHandler::registerWith(*pipeline.dispatcher);
   // ... expression handlers ...
   // ... statement handlers ...
   // ... declaration handlers ...
   TranslationUnitHandler::registerWith(*pipeline.dispatcher);

   // Dispatch
   auto* TU = pipeline.cppAST->getASTContext().getTranslationUnitDecl();
   pipeline.dispatcher->dispatch(...);

   // Generate and compile
   std::string cCode = cpptoc::test::generateCCode(...);
   ```

3. **Handler Selection by Test Type**:
   - **ControlFlowE2ETest**: Add IfStmtHandler, ForStmtHandler, WhileStmtHandler
   - **GlobalVariablesE2ETest**: Already have VariableHandler
   - **PointersE2ETest**: May need UnaryOperatorHandler (dereference), AddressOfHandler
   - **StructsE2ETest**: Need RecordHandler
   - **ClassesE2ETest**: Need RecordHandler, ConstructorHandler, InstanceMethodHandler
   - **MultipleInheritanceE2ETest**: All class handlers + inheritance support

4. **Incremental Approach**:
   - Migrate one file at a time
   - Build and run tests after each migration
   - Fix any failures before moving to next file
   - Document which handlers were needed for each test

</requirements>

<implementation>

**Migration Workflow for Each File**:

```bash
# 1. Read existing test
# 2. Create migrated version following E2EPhase1Test pattern
# 3. Update CMakeLists.txt
# 4. Rebuild
cmake --build build --target [TestName]

# 5. Run tests
./build/[TestName]

# 6. If failures, debug and add missing handlers
# 7. Repeat until all tests pass
# 8. Move to next file
```

**Handler Registration Reference** (from TranspilerAPI.cpp):
```cpp
// Base handlers
TypeHandler::registerWith(dispatcher);
ParameterHandler::registerWith(dispatcher);

// Expression handlers
LiteralHandler, DeclRefExprHandler, MemberExprHandler,
ArraySubscriptExprHandler, ParenExprHandler, ImplicitCastExprHandler,
UnaryOperatorHandler, BinaryOperatorHandler, CallExprHandler,
CXXOperatorCallExprHandler, CXXTypeidExprHandler, CXXDynamicCastExprHandler

// Statement handlers
CompoundStmtHandler, ReturnStmtHandler, DeclStmtHandler,
IfStmtHandler, ForStmtHandler, WhileStmtHandler

// Declaration handlers
RecordHandler, FunctionHandler, ConstructorHandler,
InstanceMethodHandler, StaticMethodHandler, VirtualMethodHandler,
NamespaceHandler, TranslationUnitHandler
```

**Check Handler Availability**:
```bash
# Find all available handlers
find include/dispatch -name "*Handler.h" | sort
find src/dispatch -name "*Handler.cpp" | sort
```

</implementation>

<verification>

For each migrated test file, verify:

```bash
# Test compiles
cmake --build build --target [TestName]

# All tests in file pass
./build/[TestName]

# Expected: [  PASSED  ] N tests.
```

Final verification - run all E2E tests:
```bash
ctest -R "E2E.*Test" -V
```

Check CMakeLists.txt - all 7 E2E test targets should be uncommented and building.

</verification>

<success_criteria>

1. All 6 E2E test files successfully migrated
2. All tests passing in each file (no FAILED, no crashes)
3. All test targets uncommented in CMakeLists.txt
4. No HandlerContext references remain in any E2E test
5. All new handler includes added correctly
6. Code builds cleanly: `cmake --build build`
7. All E2E tests pass: `ctest -R "E2E.*Test"`

</success_criteria>

<output>

For each migrated test file, update:
- `tests/e2e/phase[N]/[TestName].cpp` - Full migration to dispatcher pattern
- `CMakeLists.txt` - Uncomment test target

Create migration report:
```
Migration Status:
✓ E2EPhase1Test - Already migrated (11/11 tests passing)
✓ ControlFlowE2ETest - Migrated ([X]/[Y] tests passing)
  - Handlers added: [list]
  - Issues fixed: [list]
✓ GlobalVariablesE2ETest - Migrated ([X]/[Y] tests passing)
...

Overall: [X]/[Y] E2E test files migrated
Total E2E tests passing: [X]/[Y]
```

</output>
