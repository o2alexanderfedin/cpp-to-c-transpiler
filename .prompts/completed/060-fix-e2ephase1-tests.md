<objective>
Fix all 10 failing tests in E2EPhase1Test to achieve 100% pass rate.

The SimpleProgram test is already passing. The remaining 10 tests (LocalVariables through NestedExpressions) are failing with assertion errors and dyn_cast failures. This must be fixed before proceeding with migrating other E2E test files.

WHY this matters: E2EPhase1Test validates the complete transpiler pipeline (C++ → C++ AST → C AST → C code → compile → execute). These are the most critical tests proving the dispatcher pattern works end-to-end.
</objective>

<context>
Project: C++ to C transpiler using Clang frontend
Architecture: 3-stage pipeline (Parse C++ → Translate AST → Generate C)
Current State: HandlerContext retirement in progress, migrating to CppToCVisitorDispatcher pattern

Recent Work Completed:
- Successfully migrated E2EPhase1Test from HandlerContext to dispatcher pattern
- Created CallExprHandler and DeclStmtHandler
- Fixed FunctionHandler and VariableHandler bugs
- SimpleProgram test (1/11) now passes

Current Failure:
- LocalVariables test crashes with: `Assertion failed: (detail::isPresent(Val) && "dyn_cast on a non-existent value"), function dyn_cast, file Casting.h, line 662`
- 9 other tests not yet attempted

@tests/e2e/phase1/E2EPhase1Test.cpp
@src/dispatch/VariableHandler.cpp
@src/dispatch/DeclStmtHandler.cpp
@tests/fixtures/DispatcherTestHelper.h

Review CLAUDE.md for project conventions and coding standards.
</context>

<requirements>

1. **Fix LocalVariables Test First**:
   - Debug the dyn_cast assertion failure
   - Likely issue: null pointer somewhere in the variable translation chain
   - Check DeclStmtHandler, VariableHandler for dyn_cast vs dyn_cast_or_null
   - Verify local variable parent context is being set correctly

2. **Fix Remaining 9 Tests Sequentially**:
   - ArithmeticExpression
   - FunctionCalls (might already work)
   - ComplexCalculation
   - Subtraction
   - Division
   - Modulo
   - MultipleFunctions
   - NestedExpressions
   - BasicSanity (should be trivial)

3. **Add Missing Handlers as Needed**:
   - Analyze what AST node types each test uses
   - Create new handlers if needed (pattern: see CallExprHandler, DeclStmtHandler)
   - Register handlers in E2EPhase1Test.cpp in correct dependency order

4. **Debug Strategy**:
   - Run tests one at a time with: `./build/E2EPhase1Test --gtest_filter=E2EPhase1Test.TestName`
   - Examine generated C code to see what's missing/wrong
   - Add debug output to handlers if needed
   - Use lldb/gdb if assertion failures occur

</requirements>

<implementation>

**Handler Creation Pattern** (if new handlers needed):
1. Create header in `include/dispatch/XxxHandler.h`
2. Create implementation in `src/dispatch/XxxHandler.cpp`
3. Follow StaticMethodHandler/CallExprHandler pattern exactly
4. Add to CMakeLists.txt under appropriate phase
5. Register in E2EPhase1Test.cpp

**Debugging Workflow**:
```bash
# Rebuild test
cmake --build build --target E2EPhase1Test

# Run specific test
./build/E2EPhase1Test --gtest_filter=E2EPhase1Test.LocalVariables

# If crash, use lldb
lldb ./build/E2EPhase1Test
> run --gtest_filter=E2EPhase1Test.LocalVariables
```

**Common Issues to Check**:
- Missing handler registration (causes "No handler for declaration" warnings)
- Wrong handler order (dependencies not met)
- dyn_cast instead of dyn_cast_or_null
- Missing StmtMapper.setCreated() calls
- Parent context not set for local variables

</implementation>

<verification>

Before declaring complete, verify:

```bash
# All 11 tests must pass
./build/E2EPhase1Test

# Expected output:
# [==========] Running 11 tests from 1 test suite.
# ...
# [  PASSED  ] 11 tests.
```

Check that:
- No assertion failures occur
- No "No handler for declaration" warnings
- Generated C code compiles and runs correctly
- All 11 tests show [  PASSED  ] status

</verification>

<success_criteria>

1. All 11 E2EPhase1Test tests pass (100% pass rate)
2. No crashes or assertion failures
3. No "unhandled declaration" warnings
4. Generated C code compiles with gcc
5. Executed C code returns expected exit codes
6. All new handlers (if created) added to CMakeLists.txt
7. Code builds cleanly without errors

</success_criteria>

<output>

Update/create files as needed:
- Modify existing handlers to fix bugs
- Create new handlers if required following dispatcher pattern
- Update `tests/e2e/phase1/E2EPhase1Test.cpp` to register any new handlers
- Update `CMakeLists.txt` to include any new handler files

Report findings in format:
```
Test Results:
✓ SimpleProgram - PASSING (already working)
✓ LocalVariables - FIXED (issue: [describe fix])
✓ ArithmeticExpression - FIXED (issue: [describe fix])
...

Handlers Created/Modified:
- [HandlerName]: [what was changed and why]

All 11/11 tests passing.
```

</output>
