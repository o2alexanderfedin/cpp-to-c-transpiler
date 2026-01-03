<objective>
Migrate 20+ unit tests from HandlerContext to CppToCVisitorDispatcher pattern, completing the HandlerContext retirement.

WHY this matters: Unit tests validate individual handler functionality. Migrating them ensures all handlers work correctly with the dispatcher pattern and removes the last HandlerContext dependencies from the codebase.
</objective>

<context>
Project: C++ to C transpiler
Current State: All E2E tests migrated and passing

Unit tests still using HandlerContext pattern (find with grep):
```bash
# Find unit tests using HandlerContext
grep -r "HandlerContext" tests/unit --include="*.cpp"
```

Common unit test patterns that need migration:
- Handler-specific tests (e.g., tests/unit/handlers/XxxHandlerTest.cpp)
- Dispatcher-based tests (already migrated, skip these)
- Integration tests using old pattern

Migration Infrastructure:
@tests/fixtures/DispatcherTestHelper.h
@tests/e2e/phase1/E2EPhase1Test.cpp (for reference)

Review CLAUDE.md for project conventions.
</context>

<requirements>

1. **Identify All Unit Tests to Migrate**:
   - Find all tests referencing HandlerContext
   - Categorize by handler type
   - Determine priority order (critical handlers first)

2. **Create Unit Test Helper** (if needed):
   - Similar to DispatcherTestHelper but for unit tests
   - Simpler setup (don't need full pipeline)
   - Helper for creating test AST nodes
   - Helper for dispatcher + single handler setup

3. **Migration Pattern for Unit Tests**:
   ```cpp
   // Old pattern:
   HandlerContext ctx(cppCtx, cCtx, builder);
   XxxHandler handler(ctx);
   handler.handleXxx(node);

   // New pattern:
   auto pipeline = createTestPipeline();
   XxxHandler::registerWith(*pipeline.dispatcher);
   pipeline.dispatcher->dispatch(cppCtx, cCtx, node);
   ```

4. **Handler-Specific Considerations**:
   - Some handlers may need TypeHandler registered first (dependency)
   - Expression handlers may need ExprMapper
   - Statement handlers may need StmtMapper
   - Verify handler order in registration

5. **Update CMakeLists.txt**:
   - Uncomment disabled unit test targets
   - Ensure all unit tests build
   - Add any new test files

</requirements>

<implementation>

**Step 1: Survey and Categorize**

```bash
# Find all unit tests
find tests/unit -name "*Test.cpp" | sort

# Find HandlerContext usage
grep -l "HandlerContext" tests/unit/**/*.cpp | sort

# Check CMakeLists.txt for commented-out test targets
grep -A 10 "# DISABLED.*unit" CMakeLists.txt
```

**Step 2: Create Helper (if beneficial)**

File: `tests/fixtures/UnitTestHelper.h`
```cpp
namespace cpptoc::test {
    // Lightweight helper for unit tests
    struct UnitTestContext {
        std::unique_ptr<ASTUnit> cppAST;
        std::unique_ptr<ASTUnit> cAST;
        std::unique_ptr<CppToCVisitorDispatcher> dispatcher;
        // Minimal mappers
    };

    UnitTestContext createUnitTestContext();
}
```

**Step 3: Migrate Tests Incrementally**

Priority order:
1. Core handler tests (TypeHandler, ParameterHandler)
2. Expression handler tests
3. Statement handler tests
4. Declaration handler tests
5. Integration tests

**Step 4: Build and Verify Each**

```bash
# Build specific test
cmake --build build --target [TestName]

# Run it
./build/[TestName]

# Continue until all pass
```

</implementation>

<verification>

Per-test verification:
```bash
# Each unit test must pass
./build/[UnitTestName]
```

Final verification:
```bash
# All unit tests pass
ctest -R "Test$" -E "E2ETest"

# No HandlerContext references remain
! grep -r "HandlerContext" tests/unit --include="*.cpp"

# All test targets uncommented
grep "add_executable.*Test" CMakeLists.txt | grep -v "^#"
```

Build verification:
```bash
# Full rebuild succeeds
cmake --build build --clean-first
```

</verification>

<success_criteria>

1. All unit tests migrated to dispatcher pattern
2. No HandlerContext references in tests/ directory
3. All unit test targets uncommented in CMakeLists.txt
4. All unit tests passing: `ctest -R "Test$" -E "E2ETest"`
5. UnitTestHelper.h created (if needed for simplification)
6. Build succeeds cleanly
7. Migration documented with before/after counts

</success_criteria>

<output>

Update/create files:
- Migrate each test file to dispatcher pattern
- Create `tests/fixtures/UnitTestHelper.h` if beneficial
- Update `CMakeLists.txt` to uncomment all unit test targets

Provide migration summary:
```
Unit Test Migration Complete

Tests Migrated: [X] files
- [list of migrated test files]

Tests Already Using Dispatcher: [Y] files
- [list of already-migrated files]

Helper Created:
- tests/fixtures/UnitTestHelper.h (if created)

Results:
- All [X] unit tests passing
- 0 HandlerContext references remaining
- Build: SUCCESS
```

</output>
