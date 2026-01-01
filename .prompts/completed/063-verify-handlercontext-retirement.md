<objective>
Perform final verification that HandlerContext retirement is complete, all tests pass, and the codebase is clean.

WHY this matters: This is the final quality gate ensuring the dispatcher pattern migration is 100% complete, no technical debt remains, and the transpiler is production-ready.
</objective>

<context>
Project: C++ to C transpiler
Current State: All E2E and unit tests should be migrated to dispatcher pattern

Expected State After Previous Prompts:
- E2EPhase1Test: 11/11 tests passing
- 6 other E2E tests: All migrated and passing
- 20+ unit tests: All migrated and passing
- HandlerContext removed or deprecated

This is the final checkpoint before declaring HandlerContext retirement complete.

Review CLAUDE.md for project standards.
</context>

<requirements>

1. **Verify No HandlerContext References**:
   ```bash
   # Should return empty or only in deprecated files
   grep -r "HandlerContext" . --include="*.cpp" --include="*.h" \
       --exclude-dir=build --exclude-dir=.git
   ```

2. **Run Full Test Suite**:
   ```bash
   # All tests must pass
   ctest -V
   ```

3. **Verify Build Cleanliness**:
   ```bash
   # Clean build must succeed
   cmake --build build --clean-first
   ```

4. **Check for Disabled Tests**:
   ```bash
   # Should be zero (or documented exceptions)
   grep -r "DISABLED_" tests/ --include="*.cpp" | wc -l
   ```

5. **Verify CMakeLists.txt**:
   - No commented-out test targets (except documented ones)
   - All handlers registered in build
   - No "TODO" comments about HandlerContext

6. **Documentation Check**:
   - Update HANDLERCONTEXT_CLEANUP_STATUS.md (if exists)
   - Update ARCHITECTURE.md or CLAUDE.md with new pattern
   - Document any remaining cleanup items

</requirements>

<implementation>

**Verification Script**:

```bash
#!/bin/bash
set -e

echo "=== HandlerContext Retirement Verification ==="

echo "1. Checking for HandlerContext references..."
if grep -r "HandlerContext" . --include="*.cpp" --include="*.h" \
    --exclude-dir=build --exclude-dir=.git | grep -v "DEPRECATED" ; then
    echo "❌ FAIL: HandlerContext references found"
    exit 1
fi
echo "✓ PASS: No HandlerContext references (or all marked DEPRECATED)"

echo "2. Building project..."
cmake --build build --clean-first 2>&1 | tail -20
if [ ${PIPESTATUS[0]} -ne 0 ]; then
    echo "❌ FAIL: Build failed"
    exit 1
fi
echo "✓ PASS: Build successful"

echo "3. Running all tests..."
cd build && ctest --output-on-failure
if [ $? -ne 0 ]; then
    echo "❌ FAIL: Tests failed"
    exit 1
fi
echo "✓ PASS: All tests passing"

echo "4. Checking for disabled tests..."
DISABLED_COUNT=$(grep -r "DISABLED_" ../tests/ --include="*.cpp" | wc -l)
if [ $DISABLED_COUNT -gt 0 ]; then
    echo "⚠️  WARNING: $DISABLED_COUNT disabled tests found"
    grep -r "DISABLED_" ../tests/ --include="*.cpp"
else
    echo "✓ PASS: No disabled tests"
fi

echo "5. Checking CMakeLists.txt..."
if grep "# TODO.*HandlerContext" ../CMakeLists.txt ; then
    echo "⚠️  WARNING: HandlerContext TODOs in CMakeLists.txt"
else
    echo "✓ PASS: No HandlerContext TODOs in CMakeLists.txt"
fi

echo ""
echo "=== VERIFICATION COMPLETE ==="
```

Save as: `./scripts/verify-handlercontext-retirement.sh`

</implementation>

<verification>

Run verification script:
```bash
chmod +x scripts/verify-handlercontext-retirement.sh
./scripts/verify-handlercontext-retirement.sh
```

Manual checks:
1. Review test output - all green
2. Check for warnings during build
3. Verify no DISABLED_ tests remain
4. Confirm no HandlerContext in active code

Test counts to verify:
```bash
# Count E2E tests
ctest -N -R "E2E" | grep "Test.*#" | wc -l

# Count unit tests
ctest -N -R "Test$" -E "E2E" | grep "Test.*#" | wc -l

# Total should match expected count
```

</verification>

<success_criteria>

**Must All Be True**:
1. ✅ Build succeeds cleanly (no errors, minimal warnings)
2. ✅ All E2E tests passing (7 test files, all tests within)
3. ✅ All unit tests passing (20+ test files)
4. ✅ No HandlerContext references in active code
5. ✅ No DISABLED_ test prefixes (or all documented)
6. ✅ No commented-out test targets in CMakeLists.txt
7. ✅ Verification script passes
8. ✅ Documentation updated

**Metrics**:
- E2E tests: [X]/[X] files passing
- E2E test cases: [Y]/[Y] passing
- Unit tests: [Z]/[Z] files passing
- Build warnings: 0 (or acceptable count with documentation)
- HandlerContext references: 0 (except in deprecated/ or docs)

</success_criteria>

<output>

Create final report: `./HANDLERCONTEXT_RETIREMENT_COMPLETE.md`

```markdown
# HandlerContext Retirement - COMPLETE

## Summary
The HandlerContext pattern has been fully retired and replaced with the CppToCVisitorDispatcher pattern across the entire codebase.

## Migration Statistics
- E2E Tests Migrated: 7 files
  - E2EPhase1Test: 11/11 tests passing
  - ControlFlowE2ETest: [X]/[X] tests passing
  - GlobalVariablesE2ETest: [X]/[X] tests passing
  - PointersE2ETest: [X]/[X] tests passing
  - StructsE2ETest: [X]/[X] tests passing
  - ClassesE2ETest: [X]/[X] tests passing
  - MultipleInheritanceE2ETest: [X]/[X] tests passing

- Unit Tests Migrated: [X] files
  - All tests passing

- Handlers Created/Modified: [list]
- Test Infrastructure Created:
  - tests/fixtures/DispatcherTestHelper.h
  - tests/fixtures/UnitTestHelper.h (if created)

## Verification Results
✅ Build: SUCCESS (clean, no errors)
✅ E2E Tests: [X]/[X] PASSING
✅ Unit Tests: [Y]/[Y] PASSING
✅ HandlerContext References: 0 (active code)
✅ Disabled Tests: 0
✅ CMakeLists.txt: All targets active

## Next Steps
HandlerContext retirement is COMPLETE. The codebase is ready for:
- Further feature development
- Performance optimization
- Additional test coverage

## Date Completed
[Date]
```

Also update:
- `./HANDLERCONTEXT_CLEANUP_STATUS.md` - Mark as COMPLETE
- `./CLAUDE.md` - Document dispatcher pattern as standard
- `./ARCHITECTURE.md` - Update architecture docs if they exist

</output>
