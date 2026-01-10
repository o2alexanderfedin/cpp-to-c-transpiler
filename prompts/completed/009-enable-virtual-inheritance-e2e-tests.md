<objective>
Enable and fix all E2E (end-to-end) tests for virtual inheritance (Phase 56 Task 11).

The E2E test file exists at `tests/e2e/phase56/VirtualInheritanceE2ETest.cpp` with 10-11 tests, all currently DISABLED. Your goal is to enable each test, run the complete transpilation pipeline (C++ → C AST → C source → compile → execute), fix any issues, and achieve 100% pass rate.

**Why this matters:** E2E tests verify the entire transpilation pipeline works end-to-end for virtual inheritance. This is the ultimate validation that virtual inheritance is fully implemented and generates correct, compilable, executable C code that matches C++ semantics.
</objective>

<context>
**Project:** C++ to C Transpiler (3-stage pipeline: C++ AST → C AST → C Source)

**Completed Phases:**
- Phase 1-3: Core virtual inheritance implementation complete
- Integration tests: All passing (verified by prompt 008)

**Current State:**
- E2E test file: `tests/e2e/phase56/VirtualInheritanceE2ETest.cpp`
- All tests currently DISABLED (prefixed with `DISABLED_`)
- Tests cover real-world scenarios:
  - Simple virtual base
  - Diamond pattern
  - Multiple virtual bases
  - Deep virtual inheritance
  - Virtual inheritance + virtual methods
  - Non-POD virtual bases
  - Casting with virtual inheritance
  - Real-world iostream-style hierarchy
  - Mixed inheritance
  - Virtual base access through multiple paths

**What You're Testing:**
- Complete C++ to C transpilation for virtual inheritance
- Generated C code compiles without warnings (gcc/clang)
- Executable runs without errors
- Output matches expected behavior
- Memory layout matches C++ ABI (Itanium)
- VTT structures generated correctly
- C1/C2 constructor variants work correctly
- Virtual base accessed through correct offsets

Read @VIRTUAL_INHERITANCE_IMPLEMENTATION_PLAN.md (lines 332-347) for Task 11 details.
</context>

<requirements>

## Primary Requirements

1. **Enable Tests Incrementally**
   - Start with simplest test: `DISABLED_SimpleVirtualBase`
   - Enable by removing `DISABLED_` prefix
   - Run test and fix issues
   - Move to next test only after previous passes
   - Test order (complexity): Simple → Diamond → Multiple → Deep → Complex

2. **Run E2E Tests**
   - Build test target: `cmake --build . --target VirtualInheritanceE2ETest -j4`
   - Execute: `./VirtualInheritanceE2ETest`
   - Each test runs complete pipeline:
     - Parse C++ with Clang → C++ AST
     - Translate C++ AST → C AST (handlers)
     - Generate C source from C AST (CodeGenerator)
     - Compile C code with gcc
     - Execute compiled binary
     - Verify exit code and behavior

3. **Fix Pipeline Issues**
   - **Stage 2 issues (C++ AST → C AST):**
     - Missing vbptr field injection
     - VTT not generated
     - Vtable missing virtual base offsets
     - C1/C2 constructors not generated
     - Handler dispatch not calling virtual inheritance code

   - **Stage 3 issues (C AST → C source):**
     - CodeGenerator not emitting vbptr fields
     - VTT structs not emitted to output
     - Vtable definitions not emitted
     - C1/C2 constructor functions not emitted

   - **Compilation issues:**
     - Missing struct definitions
     - Type mismatches
     - Undefined symbols

   - **Runtime issues:**
     - Incorrect virtual base offsets
     - Wrong constructor variant called
     - Memory layout mismatch
     - Segmentation faults

4. **Verify ABI Compliance**
   - Memory layout matches C++ (sizeof checks)
   - Virtual base offsets correct
   - VTT structure correct
   - Single virtual base instance in diamond patterns
   - Constructor calling order correct

5. **Document Results**
   - Track which tests pass/fail
   - Document issues found in each test
   - Document fixes applied
   - Ensure all 10-11 tests pass before completing

</requirements>

<implementation>

## Step-by-Step Process

### Step 1: Build E2E Tests
```bash
cd build_working
cmake --build . --target VirtualInheritanceE2ETest -j4
```

If build fails, check CMakeLists.txt includes all required sources.

### Step 2: Enable and Test Incrementally

**Test 1: SimpleVirtualBase**
1. Open `tests/e2e/phase56/VirtualInheritanceE2ETest.cpp`
2. Find `TEST_F(VirtualInheritanceE2ETest, DISABLED_SimpleVirtualBase)`
3. Change to: `TEST_F(VirtualInheritanceE2ETest, SimpleVirtualBase)`
4. Save and rebuild
5. Run: `./VirtualInheritanceE2ETest --gtest_filter="*SimpleVirtualBase"`
6. If fails:
   - Read test code to understand C++ input
   - Check generated C code (test prints on failure)
   - Identify which stage fails (translation, compilation, execution)
   - Fix issue in appropriate handler or CodeGenerator
   - Re-run test
7. Repeat until SimpleVirtualBase passes

**Test 2: DiamondPattern**
1. Enable by removing `DISABLED_` prefix
2. Run: `./VirtualInheritanceE2ETest --gtest_filter="*DiamondPattern"`
3. Fix issues (likely: single virtual base instance verification)
4. Repeat until passes

**Test 3-11: Continue Pattern**
Enable tests in order of complexity:
1. SimpleVirtualBase (basic case)
2. DiamondPattern (single virtual base instance)
3. MultipleVirtualBases (multiple independent virtual bases)
4. DeepVirtualInheritance (3+ level hierarchy)
5. VirtualInheritanceWithVirtualMethods (polymorphism + virtual inheritance)
6. NonPODVirtualBases (constructors, destructors, initialization order)
7. CastingWithVirtualInheritance (pointer adjustments)
8. RealWorldIOStreamStyle (iostream hierarchy pattern)
9. MixedInheritance (virtual and non-virtual bases mixed)
10. VirtualBaseAccessMultiplePaths (access through different paths)

### Step 3: Common Issues and Fixes

**Issue: Generated C code missing vbptr field**
- **Cause:** RecordHandler not injecting vbptr
- **Fix:** Check RecordHandler::handleRecord() vbptr injection logic
- **Location:** src/dispatch/RecordHandler.cpp lines 235-263

**Issue: VTT struct not in generated output**
- **Cause:** CodeGenerator not emitting VTT
- **Fix:** Check CodeGenerator emission logic for VTT
- **Note:** Currently VTT is logged but not emitted (TODO in RecordHandler)

**Issue: Vtable missing virtual base offset fields**
- **Cause:** VtableGenerator not called or CodeGenerator not emitting
- **Fix:** Check RecordHandler lines 299-319, verify vtable generation

**Issue: Compilation error: undefined constructor**
- **Cause:** C1/C2 constructors generated but not emitted by CodeGenerator
- **Fix:** Check ConstructorHandler, verify FunctionDecl creation
- **Note:** Phase 2 uses string-based generation (TODO: C AST nodes)

**Issue: Segmentation fault at runtime**
- **Cause:** Incorrect virtual base offset calculation
- **Fix:** Check VtableGenerator::calculateVirtualBaseOffset()
- **Verify:** Use ABI validator to check memory layout

**Issue: Diamond pattern has duplicate virtual base**
- **Cause:** Virtual base constructed multiple times (should be once)
- **Fix:** Check C1/C2 constructor generation, verify only C1 constructs virtual bases

### Step 4: Enable Remaining Tests

After first 3-4 tests pass, you can enable multiple tests:
```bash
# Enable all tests by editing file
# Replace all "DISABLED_" with empty string
# Then run all tests
./VirtualInheritanceE2ETest
```

### Step 5: Fix Remaining Issues

**If tests still fail:**
- Group failures by category (compilation, runtime, behavior)
- Fix systematic issues (e.g., all runtime failures → offset calculation)
- Re-run all tests after each fix category
- Use `--gtest_filter` to focus on specific failing tests

### Step 6: Verify ABI Compliance

Each test should include ABI validation:
- Memory layout (sizeof) matches C++
- Virtual base offsets correct
- VTT structure correct
- Single virtual base instance in diamonds

If ABI validation fails:
- Check VtableGenerator offset calculation
- Verify vbptr placement in struct
- Check VTT array generation

</implementation>

<output>
After completing this task, provide:

1. **E2E Test Execution Summary:**
   ```
   E2E Tests: 10/10 passing (100%)

   Test Results:
   ✓ SimpleVirtualBase
   ✓ DiamondPattern
   ✓ MultipleVirtualBases
   ✓ DeepVirtualInheritance
   ✓ VirtualInheritanceWithVirtualMethods
   ✓ NonPODVirtualBases
   ✓ CastingWithVirtualInheritance
   ✓ RealWorldIOStreamStyle
   ✓ MixedInheritance
   ✓ VirtualBaseAccessMultiplePaths
   ```

2. **Issues Found and Fixed:**
   - For each failing test category:
     - Issue description
     - Root cause
     - Fix applied
     - File(s) modified

3. **Files Modified:**
   - tests/e2e/phase56/VirtualInheritanceE2ETest.cpp (enabled tests)
   - Any handler files modified to fix issues
   - Any CodeGenerator changes (if needed)

4. **Verification:**
   - All E2E tests pass
   - Generated C code compiles without warnings
   - Executables run successfully
   - ABI compliance verified
   - No regressions in integration/unit tests

</output>

<verification>
Before declaring complete, verify:

1. ✅ All DISABLED_ prefixes removed from tests
2. ✅ VirtualInheritanceE2ETest builds successfully
3. ✅ All 10-11 E2E tests pass (100% pass rate)
4. ✅ Generated C code compiles without warnings
5. ✅ Compiled executables run without errors
6. ✅ ABI validation passes for all tests
7. ✅ Integration tests still pass (no regressions)
8. ✅ Unit tests still pass (no regressions)

Run final verification:
```bash
# All E2E tests
./VirtualInheritanceE2ETest

# Integration tests
./VirtualInheritanceIntegrationTest

# Unit tests
./VirtualBaseDetectionTest
./VirtualBaseOffsetTableTest
./ConstructorSplitterCorrectnessTest
```

If any verification fails, continue fixing until all pass.
</verification>

<success_criteria>
- All E2E tests enabled (no DISABLED_ prefix)
- VirtualInheritanceE2ETest: 10-11/10-11 passing (100%)
- Each test demonstrates working transpilation pipeline:
  - C++ code → C AST → C source → compiled binary → successful execution
- Generated C code is valid and compiles clean
- ABI compliance verified for all tests
- No regressions in integration or unit tests
- Virtual inheritance implementation is fully validated end-to-end
- Clear documentation of any issues found and fixes applied
</success_criteria>

<constraints>
- **ENABLE TESTS INCREMENTALLY** - Don't enable all at once
- **FIX BEFORE MOVING ON** - Each test must pass before enabling next
- **DO NOT** modify test expectations unless clearly wrong
- **DO NOT** skip tests - all must pass
- **ALWAYS** verify generated C code is correct
- **ALWAYS** check for ABI compliance
- **ALWAYS** verify no regressions in other tests
</constraints>

<notes>
**Expected Timeline:** This may take 2-4 hours depending on issues found.

**Most Likely Issues:**
1. CodeGenerator not emitting VTT/vtable structures (Phases 1-3 log but don't emit C AST nodes)
2. C1/C2 constructors generated as strings but not as FunctionDecl nodes
3. Virtual base offset calculations incorrect
4. Constructor calling order wrong (C2 should not construct virtual bases)

**Critical Files to Watch:**
- src/dispatch/RecordHandler.cpp (vbptr, VTT, vtable generation)
- src/dispatch/ConstructorHandler.cpp (C1/C2 constructor generation)
- src/CodeGenerator.cpp (emission of generated structures)
- src/VtableGenerator.cpp (offset calculation)

**Pipeline Reminder:**
- Stage 1: Clang → C++ AST (working)
- Stage 2: Handlers → C AST (your focus for fixes)
- Stage 3: CodeGenerator → C source (may need fixes for emission)
</notes>
