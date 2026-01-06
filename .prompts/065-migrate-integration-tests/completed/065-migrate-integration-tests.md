<objective>
Migrate integration tests from HandlerContext to CppToCVisitorDispatcher pattern, removing the last significant HandlerContext usage from the codebase.

WHY this matters: Integration tests validate that multiple handlers work together correctly. Once migrated, HandlerContext will have no remaining usage in active code and can be safely deleted, completing the architecture migration.
</objective>

<context>
Project: C++ to C transpiler
Current State: E2E tests and unit tests migrated to dispatcher pattern

Integration tests still using HandlerContext:
```bash
# Find integration tests using HandlerContext
grep -r "HandlerContext" tests/integration --include="*.cpp" --include="*.h"
```

Previous migration work completed:
- E2E tests: 100% migrated (prompts 060, 061)
- Unit tests: 100% migrated (prompt 062)
- Method handler SEGFAULTs: Fixed (prompt 064)

Migration reference:
@tests/e2e/phase1/E2EPhase1Test.cpp (successful E2E pattern)
@tests/fixtures/DispatcherTestHelper.h (test infrastructure)

Review CLAUDE.md for project conventions.
</context>

<requirements>

1. **Identify All Integration Tests to Migrate**:
   - Find all tests in tests/integration/ using HandlerContext
   - Categorize by feature area (control flow, structs, classes, etc.)
   - Determine dependencies between tests

2. **Migration Pattern**:
   ```cpp
   // OLD: HandlerContext pattern
   class MyIntegrationTest : public ::testing::Test {
   protected:
       std::unique_ptr<HandlerContext> context;
       std::unique_ptr<SomeHandler> handler;

       void SetUp() override {
           cppAST = buildASTFromCode(...);
           cAST = buildASTFromCode(...);
           builder = std::make_unique<CNodeBuilder>(...);
           context = std::make_unique<HandlerContext>(...);
           handler = std::make_unique<SomeHandler>(*context);
       }
   };

   // NEW: Dispatcher pattern
   class MyIntegrationTest : public ::testing::Test {
   protected:
       void SetUp() override {
           // Minimal setup, pipeline created per-test
       }

       bool runTest(const std::string& cppCode) {
           auto pipeline = cpptoc::test::createDispatcherPipeline(cppCode);

           // Register handlers needed for this test
           TypeHandler::registerWith(*pipeline.dispatcher);
           SomeHandler::registerWith(*pipeline.dispatcher);
           // ... other handlers

           // Dispatch and verify
           pipeline.dispatcher->dispatch(...);
           // ... assertions
       }
   };
   ```

3. **Handler Registration Order**:
   - Base handlers first (TypeHandler, ParameterHandler)
   - Expression handlers next
   - Statement handlers
   - Declaration handlers
   - TranslationUnitHandler last

4. **Update CMakeLists.txt**:
   - Uncomment any disabled integration test targets
   - Ensure all integration tests build
   - Link with dispatcher infrastructure

5. **Maintain Test Coverage**:
   - All existing test cases must still work
   - No reduction in coverage
   - Tests should verify same functionality as before

</requirements>

<implementation>

**Step 1: Survey Integration Tests**

```bash
# List all integration test files
find tests/integration -name "*.cpp" | sort

# Find HandlerContext usage
grep -l "HandlerContext" tests/integration/**/*.cpp

# Check for commented-out test targets
grep "integration.*Test" CMakeLists.txt | grep "^#"
```

**Step 2: Create Migration Plan**

Group tests by complexity:
1. Simple tests (single handler, few dependencies)
2. Moderate tests (multiple handlers, clear dependencies)
3. Complex tests (many handlers, intricate interactions)

Migrate simple tests first to establish pattern.

**Step 3: Migrate Each Test File**

For each integration test:
1. Remove HandlerContext includes and member variables
2. Add DispatcherTestHelper.h include
3. Update SetUp() to use minimal initialization
4. Replace test methods to use createDispatcherPipeline()
5. Register appropriate handlers for each test
6. Update assertions to use mapper getCreated() methods

**Step 4: Build and Verify**

After each test migration:
```bash
# Rebuild specific test
cmake --build build --target [TestName]

# Run it
./build/[TestName]

# Should show all tests passing
```

</implementation>

<verification>

Per-test verification:
```bash
# Each integration test must pass
./build/[IntegrationTestName]
```

Final verification:
```bash
# All integration tests pass
ctest -R "Integration.*Test"

# No HandlerContext references remain
! grep -r "HandlerContext" tests/integration --include="*.cpp" --include="*.h"

# All E2E and unit tests still pass (no regressions)
ctest -R "E2E.*Test"
ctest -R "Dispatcher.*Test"

# Build succeeds
cmake --build build
```

Check that:
- All integration tests pass
- No SEGFAULT or assertion failures
- No HandlerContext references in tests/integration
- E2E and unit tests show no regressions

</verification>

<success_criteria>

1. All integration tests migrated to dispatcher pattern
2. Zero HandlerContext references in tests/integration directory
3. All integration test targets active in CMakeLists.txt
4. All integration tests passing: `ctest -R "Integration.*Test"`
5. No regressions in E2E or unit tests
6. Build succeeds cleanly
7. Migration documented with before/after test counts

</success_criteria>

<output>

Update/create files:
- Migrate each integration test file to dispatcher pattern
- Update `CMakeLists.txt` to uncomment integration test targets
- Update any test fixtures if needed

Provide migration summary:
```
Integration Tests Migration Complete

Tests Migrated: [X] files
- [list of migrated test files]

Integration Test Results:
- All [X] tests passing
- 0 HandlerContext references remaining

Verification:
- E2E tests: Still 100% passing
- Unit tests: Still 100% passing
- Build: SUCCESS

HandlerContext Usage Status:
- tests/e2e: 0 references (100% migrated)
- tests/unit: 0 references (100% migrated)
- tests/integration: 0 references (100% migrated)
- Production code: 0 references
- Total active code: 0 references

Ready for HandlerContext deletion: YES
```

</output>
