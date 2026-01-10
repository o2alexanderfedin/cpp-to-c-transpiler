<objective>
Run and verify all integration tests for virtual inheritance (Phase 56 Task 10).

The integration test file already exists at `tests/integration/handlers/VirtualInheritanceIntegrationTest.cpp` with approximately 28-40 test cases. Your goal is to build, run, and verify all tests pass to validate Phase 1-3 implementation (vbptr injection, VTT generation, vtable with virtual base offsets, C1/C2 constructor splitting).

**Why this matters:** Integration tests verify that all virtual inheritance components work together correctly in the handler dispatch pipeline. This is critical validation before enabling E2E tests.
</objective>

<context>
**Project:** C++ to C Transpiler (3-stage pipeline: C++ AST → C AST → C Source)

**Completed Phases:**
- Phase 1 (commit ed7d2db): VirtualInheritanceAnalyzer integration, vbptr field injection, VTT generation
- Phase 2 (commit dbf87ac): C1/C2 constructor splitting, VTT parameters
- Phase 3 (commit 36a7005): Vtable generation with virtual base offsets

**Current State:**
- Integration test file exists: `tests/integration/handlers/VirtualInheritanceIntegrationTest.cpp`
- Test build target exists in CMakeLists.txt: `VirtualInheritanceIntegrationTest`
- All unit tests passing (VirtualBaseDetectionTest, VirtualBaseOffsetTableTest, ConstructorSplitterCorrectnessTest)

**What You're Testing:**
- Virtual base detection across class hierarchies
- vbptr field injection in classes with virtual bases
- VTT (Virtual Table Table) generation for virtual inheritance
- Vtable generation with virtual base offset tables
- C1/C2 constructor variant generation
- Handler dispatch pipeline integration
- Diamond pattern handling (single virtual base instance)
- Mixed virtual/non-virtual inheritance scenarios

Read @VIRTUAL_INHERITANCE_IMPLEMENTATION_PLAN.md (lines 316-328) for Task 10 details.
</context>

<requirements>

## Primary Requirements

1. **Build Integration Tests**
   - Navigate to build directory: `build_working`
   - Build test target: `cmake --build . --target VirtualInheritanceIntegrationTest -j4`
   - Handle any build errors by examining error messages and fixing issues
   - If linker errors occur, check that ConstructorSplitter.cpp and other sources are linked

2. **Run Integration Tests**
   - Execute test binary: `./VirtualInheritanceIntegrationTest`
   - Capture full output showing test results
   - Expected: 28-40 tests (exact count depends on implementation)

3. **Analyze Test Results**
   - Count passing vs failing tests
   - Identify any failing test patterns
   - Check for test categories:
     - Virtual base detection tests
     - VTT generation tests
     - Vtable with offsets tests
     - C1/C2 constructor tests
     - Diamond pattern tests
     - Mixed inheritance tests

4. **Fix Failing Tests (if any)**
   - Read test code to understand expectations
   - Check generated output (vbptr fields, VTT structures, vtables)
   - Compare with expected Itanium C++ ABI behavior
   - Fix issues in handlers (RecordHandler, ConstructorHandler)
   - Re-run tests after fixes

5. **Document Results**
   - Report final pass/fail count
   - Document any issues found and fixed
   - Note any tests that need implementation updates

</requirements>

<implementation>

## Step-by-Step Process

### Step 1: Build Tests
```bash
cd build_working
cmake --build . --target VirtualInheritanceIntegrationTest -j4
```

If build fails:
- Check error messages for missing symbols
- Verify CMakeLists.txt includes all required source files
- Check that ConstructorSplitter, VirtualInheritanceAnalyzer, VTTGenerator are linked
- Fix build issues before proceeding

### Step 2: Run Tests
```bash
./VirtualInheritanceIntegrationTest
```

Capture output showing:
- Total test count
- Passing/failing tests
- Test suite organization
- Any error messages

### Step 3: Analyze Results

**If all tests pass (100%):**
- Report success with test count
- Verify expected test categories are covered
- Proceed to next prompt (E2E tests)

**If tests fail:**
- Identify which test categories are failing
- Read failing test code to understand expectations
- Check handler output (RecordHandler, ConstructorHandler logs)
- Common failure patterns:
  - Missing vbptr field injection
  - VTT not generated for classes with virtual bases
  - Vtable missing virtual base offset fields
  - C1/C2 constructors not generated
  - Diamond pattern not detected correctly

### Step 4: Fix Issues (if needed)

**For vbptr injection failures:**
- Check RecordHandler.cpp lines 235-263 (vbptr field injection)
- Verify hasVirtualBases flag is set correctly
- Ensure vbptrField is added to struct before regular fields

**For VTT generation failures:**
- Check RecordHandler.cpp lines 282-297 (VTT generation)
- Verify VTTGenerator is called for classes with virtual bases
- Check VTT code generation output in logs

**For vtable offset failures:**
- Check RecordHandler.cpp lines 299-319 (vtable with offsets)
- Verify VtableGenerator::generateVtableWithVirtualBaseOffsets() is called
- Check vtable struct contains offset fields

**For C1/C2 constructor failures:**
- Check ConstructorHandler.cpp integration
- Verify needsC1C2Split flag detection
- Check C1/C2 constructor generation output

### Step 5: Iterate Until Success
- Re-run tests after each fix
- Continue until 100% pass rate achieved
- Document all fixes made

</implementation>

<output>
After completing this task, provide:

1. **Test Execution Summary:**
   ```
   Integration Tests: XX/XX passing (100%)
   Test Categories:
   - Virtual base detection: X/X passing
   - VTT generation: X/X passing
   - Vtable with offsets: X/X passing
   - C1/C2 constructors: X/X passing
   - Diamond patterns: X/X passing
   - Mixed inheritance: X/X passing
   ```

2. **Issues Found and Fixed (if any):**
   - Description of each issue
   - Root cause identified
   - Fix applied
   - File(s) modified

3. **Files Modified (if any):**
   - List of handler files changed to fix test failures
   - Brief description of changes

4. **Verification:**
   - Confirm all integration tests pass
   - Confirm no regressions in unit tests
   - Ready to proceed to E2E tests

</output>

<verification>
Before declaring complete, verify:

1. ✅ VirtualInheritanceIntegrationTest builds successfully
2. ✅ All integration tests pass (100% pass rate)
3. ✅ Test output shows expected categories covered
4. ✅ No test failures or errors
5. ✅ Unit tests still pass (no regressions)
6. ✅ Build is clean (no warnings related to virtual inheritance)

If any verification fails, continue fixing until all criteria met.
</verification>

<success_criteria>
- VirtualInheritanceIntegrationTest builds without errors
- All integration tests pass (28-40 tests, 100% pass rate)
- Test coverage includes all virtual inheritance features:
  - Virtual base detection and analysis
  - vbptr field injection
  - VTT generation
  - Vtable with virtual base offsets
  - C1/C2 constructor splitting
  - Diamond pattern handling
  - Mixed inheritance scenarios
- No regressions in existing unit tests
- Clear summary of test results provided
- Any issues found have been fixed and documented
</success_criteria>

<constraints>
- **DO NOT** modify test expectations unless they're clearly incorrect
- **DO NOT** skip failing tests - fix the underlying issues
- **DO NOT** proceed to E2E tests until integration tests pass 100%
- **ALWAYS** verify fixes don't break other tests
- **ALWAYS** document any handler modifications made
</constraints>
