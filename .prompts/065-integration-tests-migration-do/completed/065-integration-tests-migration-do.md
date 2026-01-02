# Prompt 065: Migrate Integration Tests from HandlerContext to Dispatcher Pattern

## Objective

Migrate 10 integration test files from legacy HandlerContext pattern to modern dispatcher pattern, eliminating the remaining test code HandlerContext references and advancing overall HandlerContext retirement from ~95% to ~98%.

**Critical Finding**: HandlerTestFixture.h/cpp are **unused** and should be deleted as part of this migration.

## Context

**Background Documents**:
- @HANDLERCONTEXT_RETIREMENT_STATUS.md - Overall retirement status (~95% complete)
- @ARRAYLOOP_MIGRATION_COMPLETE.md - Recent successful production code migration
- @STATICMEMBER_VERIFICATION_COMPLETE.md - Recent successful test migration reference
- @tests/fixtures/DispatcherTestHelper.h - Modern test pattern to follow

**Current State**:
- **Production code**: ✅ 100% HandlerContext-free
- **Test code**: 15 files using HandlerContext
  - 10 integration tests (this prompt)
  - 2 E2E tests (separate prompt)
  - 2 fixture files (HandlerTestFixture - **UNUSED**, to be deleted)
  - 1 example template (migration reference)

**Key Discovery**:
HandlerTestFixture.h and HandlerTestFixture.cpp are **not used by any tests**. All integration tests create HandlerContext directly in their SetUp() methods. These files should be deleted, not migrated.

## Files to Migrate

### Integration Tests (10 files) - MIGRATE TO DISPATCHER PATTERN

1. `tests/integration/comparison-operators/ComparisonOperatorsIntegrationTest.cpp`
2. `tests/integration/handlers/ControlFlowIntegrationTest.cpp`
3. `tests/integration/handlers/StructsIntegrationTest.cpp`
4. `tests/integration/handlers/ClassesIntegrationTest.cpp`
5. `tests/integration/handlers/GlobalVariablesIntegrationTest.cpp`
6. `tests/integration/handlers/HandlerIntegrationTest.cpp`
7. `tests/integration/handlers/PointersIntegrationTest.cpp`
8. `tests/integration/handlers/EnumIntegrationTest.cpp`
9. `tests/integration/handlers/VirtualMethodsIntegrationTest.cpp`
10. `tests/integration/handlers/MultipleInheritanceIntegrationTest.cpp`

### Unused Fixture Files - DELETE

11. `tests/fixtures/HandlerTestFixture.h` - **DELETE** (unused)
12. `tests/fixtures/HandlerTestFixture.cpp` - **DELETE** (unused)

## Migration Pattern

### Current Pattern (HandlerContext-based):
```cpp
class ControlFlowIntegrationTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;  // LEGACY

    std::unique_ptr<FunctionHandler> funcHandler;  // LEGACY
    std::unique_ptr<VariableHandler> varHandler;   // LEGACY

    void SetUp() override {
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );

        funcHandler = std::make_unique<FunctionHandler>();
        varHandler = std::make_unique<VariableHandler>();
    }
};
```

### Target Pattern (Dispatcher-based):
```cpp
#include "DispatcherTestHelper.h"

class ControlFlowIntegrationTest : public ::testing::Test {
protected:
    cpptoc::test::DispatcherPipeline pipeline;

    void SetUp() override {
        pipeline = cpptoc::test::createDispatcherPipeline("int dummy;");

        // Register only the handlers needed for this test
        cpptoc::FunctionHandler::registerWith(*pipeline.dispatcher);
        cpptoc::VariableHandler::registerWith(*pipeline.dispatcher);
    }

    void TearDown() override {
        // Pipeline cleanup is automatic (unique_ptr RAII)
    }
};

TEST_F(ControlFlowIntegrationTest, TestName) {
    // Test implementation...
    // Use: pipeline.cppAST, pipeline.cAST, pipeline.dispatcher
}
```

## Requirements

### Phase 1: Delete Unused Files

1. **Verify HandlerTestFixture is unused**:
   ```bash
   grep -r "HandlerTestFixture" tests/ --include="*.cpp" --include="*.h" | \
     grep -v "HandlerTestFixture.cpp" | grep -v "HandlerTestFixture.h"
   # Should return 0 results (only the files themselves)
   ```

2. **Delete files**:
   - Delete `tests/fixtures/HandlerTestFixture.h`
   - Delete `tests/fixtures/HandlerTestFixture.cpp`

3. **Update CMakeLists.txt**:
   - Remove HandlerTestFixture from any test targets (if referenced)
   - Search for "HandlerTestFixture" in CMakeLists.txt

### Phase 2: Migrate Integration Tests (Template)

For each of the 10 integration test files:

1. **Update includes**:
   ```cpp
   // REMOVE:
   #include "handlers/HandlerContext.h"
   #include "handlers/FunctionHandler.h"  // Legacy handler includes

   // ADD:
   #include "DispatcherTestHelper.h"
   #include "dispatch/FunctionHandler.h"  // Dispatcher handler includes
   ```

2. **Update test class members**:
   ```cpp
   // REMOVE:
   std::unique_ptr<clang::ASTUnit> cppAST;
   std::unique_ptr<clang::ASTUnit> cAST;
   std::unique_ptr<clang::CNodeBuilder> builder;
   std::unique_ptr<HandlerContext> context;
   std::unique_ptr<FunctionHandler> funcHandler;
   // ... other legacy handlers

   // ADD:
   cpptoc::test::DispatcherPipeline pipeline;
   ```

3. **Update SetUp() method**:
   ```cpp
   void SetUp() override {
       // REMOVE all manual AST/context/handler creation

       // ADD:
       pipeline = cpptoc::test::createDispatcherPipeline("int dummy;");

       // Register handlers (replace handler instantiation)
       cpptoc::FunctionHandler::registerWith(*pipeline.dispatcher);
       cpptoc::VariableHandler::registerWith(*pipeline.dispatcher);
       // ... register other needed handlers
   }
   ```

4. **Update TearDown() method**:
   ```cpp
   void TearDown() override {
       // REMOVE all manual cleanup (.reset() calls)
       // Pipeline cleanup is automatic via unique_ptr destructors
   }
   ```

5. **Update test methods**:
   - Replace `context->` with `pipeline.dispatcher->`
   - Replace `cppAST->` with `pipeline.cppAST->`
   - Replace `cAST->` with `pipeline.cAST->`
   - Replace `builder->` with `pipeline.dispatcher->getBuilder().`
   - Update handler method calls to use dispatcher

### Phase 3: Build and Test Verification

1. **Build verification**:
   ```bash
   cd build
   cmake .. -DLLVM_DIR=/opt/homebrew/opt/llvm/lib/cmake/llvm \
            -DClang_DIR=/opt/homebrew/opt/llvm/lib/cmake/clang
   make -j8 2>&1 | tee ../integration_tests_build.log
   ```

2. **Run migrated tests**:
   ```bash
   # Run each test individually first
   ./ControlFlowIntegrationTest
   ./StructsIntegrationTest
   # ... etc.

   # Run all integration tests
   ctest -R "Integration" --output-on-failure
   ```

3. **Verify HandlerContext elimination**:
   ```bash
   # Check integration tests for HandlerContext
   grep -r "HandlerContext" tests/integration --include="*.cpp" --include="*.h"
   # Should return 0 results

   # Check all tests for HandlerContext (should drop significantly)
   grep -r "HandlerContext" tests/ --include="*.cpp" --include="*.h" | wc -l
   # Expected: ~31 (down from 41 - 10 integration tests)
   ```

## Migration Strategy (Map-Reduce)

To maximize efficiency, migrate tests in parallel using the Task tool:

**Parallel Execution**:
1. Spawn 3 parallel migration tasks (respecting CPU cores):
   - Task 1: Migrate tests 1-3
   - Task 2: Migrate tests 4-6
   - Task 3: Migrate tests 7-10
2. Each task reports:
   - Files modified
   - Build status
   - Test results
   - Any issues encountered

**Sequential Phases**:
1. Phase 1: Delete unused files (single task)
2. Phase 2: Parallel migration (3 tasks)
3. Phase 3: Build and verification (single task)

## Expected Challenges and Solutions

**Challenge 1**: Tests may use legacy handler APIs not available in dispatcher handlers
- **Solution**: Dispatcher handlers have modern APIs - consult existing migrated tests or handler source

**Challenge 2**: Tests may rely on HandlerContext methods
- **Solution**: DispatcherPipeline provides all needed components (dispatcher, mappers, AST contexts)

**Challenge 3**: Handler registration pattern differs
- **Solution**: Use `Handler::registerWith(*pipeline.dispatcher)` pattern consistently

**Challenge 4**: Build errors due to missing includes
- **Solution**: Include DispatcherTestHelper.h and dispatcher handler headers (dispatch/*)

## Output Specification

**Primary Output**: Modified test files (in place)
- 10 integration test .cpp files (migrated)
- 2 fixture files (deleted)
- CMakeLists.txt (updated if needed)

**Documentation Output**: `.prompts/065-integration-tests-migration-do/`
- `INTEGRATION_TESTS_MIGRATION_COMPLETE.md` - Migration report
- `SUMMARY.md` - Executive summary
- Update `HANDLERCONTEXT_RETIREMENT_STATUS.md` (in project root)

## Success Criteria

1. ✅ HandlerTestFixture.h deleted
2. ✅ HandlerTestFixture.cpp deleted
3. ✅ All 10 integration tests migrated to dispatcher pattern
4. ✅ All tests compile without errors
5. ✅ All tests pass (100% pass rate or document failures)
6. ✅ 0 HandlerContext references in integration tests
7. ✅ Project builds successfully
8. ✅ Test HandlerContext references reduced from ~41 to ~31
9. ✅ Overall retirement increased from ~95% to ~98%
10. ✅ Migration report created and committed

## Timeline Estimate

**Total**: 3-5 hours (as estimated in retirement status)
- Phase 1 (Delete): 0.5 hours
- Phase 2 (Migrate 10 tests): 2-3 hours (parallelized)
- Phase 3 (Build/Test): 0.5-1 hour
- Documentation: 0.5 hour

## Next Step After Completion

After achieving ~98% retirement:
- **Next Priority**: E2E test migration (2 files, 21 DISABLED tests)
  - `tests/e2e/phase47/EnumE2ETest.cpp` (9 DISABLED)
  - `tests/e2e/phase45/VirtualMethodsE2ETest.cpp` (12 DISABLED)
- **Estimated effort**: 6-10 hours
- **Final retirement**: ~99-100%

## Verification Commands

```bash
# Verify HandlerTestFixture deletion
ls tests/fixtures/HandlerTestFixture.*
# Should return: No such file or directory

# Count integration test HandlerContext references
grep -r "HandlerContext" tests/integration --include="*.cpp" --include="*.h" | wc -l
# Expected: 0

# Count total test HandlerContext references
grep -r "HandlerContext" tests/ --include="*.cpp" --include="*.h" | wc -l
# Expected: ~31 (down from 41)

# Run integration tests
cd build
ctest -R "Integration" --output-on-failure
# Expected: All tests passing

# Overall HandlerContext references in codebase
grep -r "HandlerContext" . --include="*.cpp" --include="*.h" \
  --exclude-dir=build --exclude-dir=.git | grep -v "//" | wc -l
# Expected: ~33 (2 production comments + 31 test)
```

## Quality Checklist

Before considering this task complete:

- [ ] HandlerTestFixture files verified unused and deleted
- [ ] All 10 integration tests migrated to DispatcherPipeline pattern
- [ ] All includes updated (removed HandlerContext, added DispatcherTestHelper)
- [ ] All SetUp/TearDown methods updated
- [ ] All test method bodies updated (context → pipeline)
- [ ] Project compiles successfully (no errors)
- [ ] All integration tests passing (or failures documented)
- [ ] 0 HandlerContext references in integration test code
- [ ] Migration report created with metrics
- [ ] HANDLERCONTEXT_RETIREMENT_STATUS.md updated (~98% completion)
- [ ] SUMMARY.md created with substantive one-liner
- [ ] Changes committed with descriptive message

## Reference Migrations

**Successful patterns to follow**:
1. **StaticMemberTranslator migration** - Test migration from HandlerContext to dispatcher
   - See: `tests/unit/helpers/StaticMemberTranslatorTest.cpp`
   - Pattern: Used DispatcherTestHelper functions
2. **E2EPhase1Test migration** - E2E test migration
   - See: `tests/e2e/phase1/E2EPhase1Test.cpp`
   - Pattern: Created pipeline, registered handlers, dispatched decls
3. **DispatcherTestHelper.h** - Modern test helper design
   - Function-based helpers vs fixture classes
   - Returns DispatcherPipeline struct with all components
