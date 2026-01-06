# Phase 39-01c: Integration & E2E Testing

## Objective

Create comprehensive integration tests that validate handler cooperation and end-to-end tests that verify full transpilation pipeline (C++ → C AST → C code → compiled executable).

**Goal:** Validate that all handlers work together correctly and produce valid, executable C code.

**Dependencies:** Phase 39-01b must be complete (all 4 handlers implemented)

## Context

@docs/architecture/07-test-plan.md - Integration and E2E test specifications
@docs/architecture/10-phase1-detailed-plan.md - Integration test cases
@tests/fixtures/HandlerTestFixture.h - Test infrastructure
@include/handlers/*.h - All implemented handlers

## Tasks

### Task 1: Handler Integration Tests
**Type**: auto
**Estimated**: 3-4 hours

**Action**: Write 25+ integration tests combining multiple handlers

**Test Cases:**

**Function + Expression (5 tests):**
1. FunctionWithArithmetic - Function returning arithmetic expression
2. FunctionWithComplexExpr - Nested expressions in function
3. FunctionCallWithArithmetic - Function call with arithmetic args
4. MultipleArithmeticFunctions - Multiple functions with math
5. RecursiveFunctionCall - Function calling itself

**Function + Variable (5 tests):**
6. FunctionWithLocalVar - Function with local variable
7. FunctionWithMultipleVars - Multiple local variables
8. FunctionUsingVars - Variables used in expressions
9. FunctionWithConstVars - Const variables
10. FunctionVarInitFromParam - Local var init from parameter

**All Handlers Combined (15 tests):**
11. CompleteSimpleProgram - main() with vars and return
12. FunctionWithAllFeatures - Params, vars, arithmetic, return
13. MultipleStatements - Multiple statements in function
14. NestedCompounds - Nested compound statements
15. ComplexArithmetic - All operators in one expression
16. VariableReuse - Same variable used multiple times
17. ParameterPassing - Pass vars as function arguments
18. ReturnComplexExpression - Complex expr in return
19. ChainedFunctionCalls - f1() calls f2() calls f3()
20. MixedTypes - Int and float mixed
21. ConstExpressions - Const vars in expressions
22. DeepNesting - Deeply nested expressions and statements
23. LargeFunction - Function with many operations
24. EdgeCaseArithmetic - Division by constants, modulo
25. AllOperatorsCombined - +, -, *, /, % in one function

**Implementation:**
Create `tests/integration/handlers/HandlerIntegrationTest.cpp`

**Verification:**
- [ ] 25+ integration tests pass
- [ ] Handlers cooperate correctly
- [ ] C AST structure is valid
- [ ] No handler conflicts
- [ ] Symbol resolution works

---

### Task 2: E2E Integration Tests
**Type**: auto
**Estimated**: 2-3 hours

**Action**: Write 10+ end-to-end tests with full compilation and execution

**Test Structure:**
Each test:
1. Write C++ source code
2. Transpile to C AST using handlers
3. Emit C code (temporary CodeGenerator or manual)
4. Compile with gcc
5. Execute and verify output

**Test Cases:**

**Test 1: SimpleProgram**
```cpp
// C++
int add(int a, int b) {
    return a + b;
}
int main() {
    return add(3, 4);  // Expected: exit code 7
}
```

**Test 2: LocalVariables**
```cpp
int main() {
    int x = 5;
    int y = 3;
    return x + y;  // Expected: 8
}
```

**Test 3: ArithmeticExpression**
```cpp
int main() {
    return 2 + 3 * 4;  // Expected: 14
}
```

**Test 4: FunctionCalls**
```cpp
int double_it(int n) {
    return n * 2;
}
int main() {
    return double_it(5);  // Expected: 10
}
```

**Test 5: ComplexCalculation**
```cpp
int calculate() {
    int a = 10;
    int b = 20;
    int c = a + b;
    return c * 2;  // Expected: 60
}
int main() {
    return calculate();
}
```

**Test 6-10:** More complex scenarios mixing all features

**Implementation:**
Create `tests/e2e/phase1/E2ETest.cpp`
Create helper `IntegrationTestHarness` if not exists

**Verification:**
- [ ] 10+ E2E tests pass
- [ ] Generated C code compiles with gcc
- [ ] Generated C code produces correct output
- [ ] No memory leaks (valgrind)
- [ ] Exit codes match expected

---

## Verification

**Phase 39-01c Completion Criteria:**

1. **Integration Tests:**
   - [ ] 25+ integration tests pass (100%)
   - [ ] All handler combinations tested
   - [ ] C AST structure validated
   - [ ] Symbol resolution verified

2. **E2E Tests:**
   - [ ] 10+ E2E tests pass (100%)
   - [ ] C code compiles successfully
   - [ ] C code executes correctly
   - [ ] Output matches expected
   - [ ] No memory leaks

3. **Overall:**
   - [ ] Total tests: 100+ (3 FunctionHandler + 15 VariableHandler + 35 ExpressionHandler + 12 StatementHandler + 25 integration + 10 E2E)
   - [ ] 100% pass rate
   - [ ] Full pipeline validated

## Success Criteria

✅ Comprehensive integration testing complete
✅ E2E pipeline validated end-to-end
✅ 35+ new tests passing (total 100+)
✅ Generated C code confirmed working
✅ Ready for CodeGenerator implementation

**Estimated Total:** 5-7 hours

## Output

Create `.planning/phases/39-foundation-implementation/39-01c-SUMMARY.md` with:

**Deliverables:**
- 25+ integration tests
- 10+ E2E tests
- Test harness enhancements

**Statistics:**
- Total cumulative tests: 100+
- All tests passing
- C compilation success rate
- Execution success rate

**Validation Results:**
- Handler cooperation validated
- C AST correctness confirmed
- Generated C code quality verified

**Next Steps:**
- Phase 39-01d: CodeGenerator and full pipeline

**Commit:**
Format: `test(phase1): Add integration and E2E tests`
