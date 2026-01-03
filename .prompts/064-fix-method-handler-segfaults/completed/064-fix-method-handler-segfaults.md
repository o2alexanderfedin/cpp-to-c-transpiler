<objective>
Fix all 37 SEGFAULT failures in method handler dispatcher tests to achieve 100% test pass rate.

WHY this matters: These SEGFAULTs indicate critical bugs in the method handler implementations (StaticMethodHandler, InstanceMethodHandler, VirtualMethodHandler). These handlers are essential for transpiling C++ classes to C, and they must work reliably before the HandlerContext class can be safely removed.
</objective>

<context>
Project: C++ to C transpiler using Clang frontend
Current State: Unit tests migrated to dispatcher pattern, but 37 tests failing with SEGFAULT

Test Failures (118/155 passing, 76%):
- StaticMethodHandlerDispatcherTest: 10 SEGFAULT failures
- InstanceMethodHandlerDispatcherTest: 13 SEGFAULT failures
- VirtualMethodHandlerDispatcherTest: 14 SEGFAULT failures

All other dispatcher tests pass successfully, indicating the SEGFAULT issues are specific to method handler implementations, not the dispatcher pattern itself.

Files to investigate:
@src/dispatch/StaticMethodHandler.cpp
@src/dispatch/InstanceMethodHandler.cpp
@src/dispatch/VirtualMethodHandler.cpp
@tests/unit/dispatch/StaticMethodHandlerDispatcherTest.cpp
@tests/unit/dispatch/InstanceMethodHandlerDispatcherTest.cpp
@tests/unit/dispatch/VirtualMethodHandlerDispatcherTest.cpp

Review CLAUDE.md for project conventions and debugging strategies.
</context>

<requirements>

1. **Identify Root Causes**:
   - Run failing tests individually with lldb/gdb to capture stack traces
   - Identify common patterns across the 37 failures
   - Check for null pointer dereferences, use-after-free, invalid casts
   - Verify AST node access patterns are correct

2. **Debug Each Handler Type**:

   **StaticMethodHandler** (10 failures):
   - Check static method AST node handling
   - Verify name mangling for static methods
   - Ensure proper handling of `this` parameter (should not exist for static)
   - Check DeclMapper and ExprMapper usage

   **InstanceMethodHandler** (13 failures):
   - Check instance method AST node handling
   - Verify `this` parameter addition
   - Ensure proper method body translation
   - Check member access patterns

   **VirtualMethodHandler** (14 failures):
   - Check virtual method dispatch mechanism
   - Verify vtable generation
   - Ensure virtual call translation
   - Check inheritance hierarchy traversal

3. **Common Issues to Check**:
   - Null pointer dereferences (use llvm::dyn_cast_or_null instead of llvm::cast)
   - Invalid AST context mixing (C++ AST vs C AST)
   - Missing mapper entries (check hasCreated before getCreated)
   - Recursive dispatch issues (infinite loops)
   - Memory management (use-after-free, dangling pointers)

4. **Debugging Workflow**:
   ```bash
   # Run specific failing test with debugger
   lldb ./build/StaticMethodHandlerDispatcherTest
   > run --gtest_filter=StaticMethodHandlerDispatcherTest.FailingTestName

   # Examine backtrace
   > bt

   # Inspect variables at crash point
   > frame variable
   ```

</requirements>

<implementation>

**Step 1: Reproduce and Categorize Failures**

For each failing test:
1. Run with lldb to get stack trace
2. Document crash location and immediate cause
3. Categorize by root cause pattern

**Step 2: Fix Common Patterns First**

If multiple tests fail from same root cause:
1. Fix the common issue in handler implementation
2. Rebuild and retest all affected tests
3. Verify fix resolves multiple failures

**Step 3: Fix Individual Issues**

For unique failures:
1. Analyze specific test case requirements
2. Identify handler logic bug
3. Implement fix with defensive programming
4. Add null checks and assertions where appropriate

**Step 4: Verify Fixes**

After each fix:
```bash
# Rebuild specific test
cmake --build build --target [HandlerName]DispatcherTest

# Run all tests for that handler
./build/[HandlerName]DispatcherTest

# Verify no regressions
ctest -R "DispatcherTest$"
```

</implementation>

<verification>

Before declaring complete, verify:

```bash
# All method handler tests must pass
./build/StaticMethodHandlerDispatcherTest    # Should show 0 failures
./build/InstanceMethodHandlerDispatcherTest  # Should show 0 failures
./build/VirtualMethodHandlerDispatcherTest   # Should show 0 failures

# Run all dispatcher tests
ctest -R "DispatcherTest$"  # Should show 155/155 passing (100%)

# Verify no new failures introduced
./build/E2EPhase1Test       # Should still show 11/11 passing
./build/ControlFlowE2ETest  # Should still show 11/11 passing
```

Check that:
- No SEGFAULT errors occur
- All 37 previously failing tests now pass
- No regressions in other tests
- Code builds cleanly without new warnings

</verification>

<success_criteria>

1. All 37 SEGFAULT failures fixed
2. StaticMethodHandlerDispatcherTest: 100% passing
3. InstanceMethodHandlerDispatcherTest: 100% passing
4. VirtualMethodHandlerDispatcherTest: 100% passing
5. Overall dispatcher tests: 155/155 passing (100%)
6. No regressions in E2E tests
7. Root causes documented for each fix
8. Defensive programming improvements added (null checks, assertions)

</success_criteria>

<output>

Fix bugs in handler implementations:
- Modify `src/dispatch/StaticMethodHandler.cpp` as needed
- Modify `src/dispatch/InstanceMethodHandler.cpp` as needed
- Modify `src/dispatch/VirtualMethodHandler.cpp` as needed

Report findings:
```
SEGFAULT Fixes Report:

StaticMethodHandler (10 failures):
- Root cause: [describe]
- Fix applied: [describe]
- Tests now passing: X/X

InstanceMethodHandler (13 failures):
- Root cause: [describe]
- Fix applied: [describe]
- Tests now passing: X/X

VirtualMethodHandler (14 failures):
- Root cause: [describe]
- Fix applied: [describe]
- Tests now passing: X/X

Overall Results:
- Total tests passing: 155/155 (100%)
- All SEGFAULTs resolved
- No regressions detected
```

</output>
