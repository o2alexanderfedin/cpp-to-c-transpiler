# Execute Phase 45 Groups 3-5: Master Coordination Plan

**Status**: READY TO EXECUTE
**Current**: Groups 1-2 COMPLETE (40/40 tests passing)
**Remaining**: Groups 3-5 (~70 tests)
**Execution Mode**: PARALLEL where possible

## Current State Summary

### ✅ COMPLETED
- **Group 1**: Vtable Infrastructure (22/22 tests)
  - Task 1: VtableTypedefGenerator (10 tests)
  - Task 2: Vtable Struct Generator (12 tests)
- **Group 2**: Struct Layout (18/18 tests)
  - Task 3: lpVtbl Injection (8 tests)
  - Task 4: Vtable Instance Generator (10 tests)
- **Total**: 40/40 tests passing (100%)
- **Git Commits**: 3 commits for Groups 1-2

### 🔄 REMAINING WORK

#### Group 3: Constructor Integration (SEQUENTIAL)
- **Task 5**: lpVtbl Initialization in ConstructorHandler
  - Create: `tests/unit/handlers/ConstructorHandlerTest_lpVtbl.cpp`
  - Tests: 8-10 unit tests
  - Time: 2-3 hours
  - **Must complete BEFORE Group 4** (dependencies on constructor behavior)

#### Group 4: Virtual Call Translation (PARALLEL after Group 3)
- **Task 6**: Virtual Call Detection (CAN RUN IN PARALLEL with Task 7)
  - Create: `tests/unit/handlers/ExpressionHandlerTest_VirtualDetect.cpp`
  - Tests: 6-8 unit tests
  - Time: 2-3 hours

- **Task 7**: Virtual Call Code Generation (CAN RUN IN PARALLEL with Task 6)
  - Create: `tests/unit/handlers/ExpressionHandlerTest_VirtualCall.cpp`
  - Tests: 12-15 unit tests
  - Time: 3-4 hours

#### Group 5: Integration & E2E (SEQUENTIAL after Group 4)
- **Task 8**: Integration Tests
  - Create: `tests/integration/handlers/VirtualMethodsIntegrationTest.cpp`
  - Tests: 30-35 integration tests
  - Time: 4-5 hours
  - **Must complete BEFORE Task 9**

- **Task 9**: E2E Tests
  - Create: `tests/e2e/phase45/VirtualMethodsE2ETest.cpp`
  - Tests: 15 tests (1-3 active, rest disabled)
  - Time: 2-3 hours

## Execution Strategy

### Phase 1: Group 3 (SEQUENTIAL)
```
Execute Task 5 (lpVtbl initialization)
→ Verify all tests pass
→ Commit: "feat(phase45-g3): Implement lpVtbl initialization in constructors"
```

### Phase 2: Group 4 (PARALLEL)
```
Execute Task 6 (Virtual detection) || Execute Task 7 (Virtual codegen)
→ Wait for both to complete
→ Verify all tests pass
→ Commit: "feat(phase45-g4): Implement virtual call detection and code generation"
```

### Phase 3: Group 5 (SEQUENTIAL)
```
Execute Task 8 (Integration tests)
→ Verify all integration tests pass
→ Execute Task 9 (E2E tests)
→ Verify E2E tests pass
→ Commit: "feat(phase45-g5): Add comprehensive integration and E2E tests"
```

### Phase 4: Documentation & Final Commit
```
→ Create PHASE45-COMPLETE.md with full summary
→ Run full test suite
→ Verify 100% pass rate
→ Commit: "feat(phase45): Complete virtual methods with COM-style vtables"
```

## Task Execution Details

### Task 5: lpVtbl Initialization (Group 3)
**Prompt Context**: See `GROUP3-TASK.md`
**Implementation**:
1. Modify `include/handlers/ConstructorHandler.h`
2. Modify `src/handlers/ConstructorHandler.cpp`
3. Create `tests/unit/handlers/ConstructorHandlerTest_lpVtbl.cpp`
4. Follow TDD: Write test → Fail → Implement → Pass → Refactor
5. Verify 8-10 tests pass

**Key Requirements**:
- Inject `this->lpVtbl = &ClassName_vtable_instance;` as FIRST statement
- Only for polymorphic classes
- Before field initialization

### Task 6: Virtual Call Detection (Group 4)
**Prompt Context**: See `GROUP4-TASK6.md`
**Implementation**:
1. Modify `include/handlers/ExpressionHandler.h`
2. Modify `src/handlers/ExpressionHandler.cpp`
3. Create `tests/unit/handlers/ExpressionHandlerTest_VirtualDetect.cpp`
4. Follow TDD
5. Verify 6-8 tests pass

**Key Requirements**:
- Detect `CXXMethodDecl::isVirtual()`
- Distinguish virtual vs non-virtual
- Handle static/final/inline special cases

### Task 7: Virtual Call Code Generation (Group 4)
**Prompt Context**: See `GROUP4-TASK7.md`
**Implementation**:
1. Modify `src/handlers/ExpressionHandler.cpp`
2. Create `tests/unit/handlers/ExpressionHandlerTest_VirtualCall.cpp`
3. Follow TDD
4. Verify 12-15 tests pass

**Key Requirements**:
- Pattern: `obj->lpVtbl->methodName(obj, args...)`
- Handle value/pointer/reference objects
- Preserve return values

### Task 8: Integration Tests (Group 5)
**Prompt Context**: See `GROUP5-TASK8.md`
**Implementation**:
1. Create `tests/integration/handlers/VirtualMethodsIntegrationTest.cpp`
2. Test complete pipeline (C++ → C translation)
3. Verify 30-35 tests pass

**Test Categories**:
- Simple virtual methods (5 tests)
- Inheritance (10 tests)
- Pure virtual (5 tests)
- Polymorphic calls (8 tests)
- Advanced scenarios (7 tests)

### Task 9: E2E Tests (Group 5)
**Prompt Context**: See `GROUP5-TASK9.md`
**Implementation**:
1. Create `tests/e2e/phase45/VirtualMethodsE2ETest.cpp`
2. Compile and execute generated C code
3. Verify 1-3 active tests pass
4. Create 12 DISABLED_ tests for future

**Active Tests**:
- SimpleVirtualCall
- PolymorphicDispatch
- VirtualCallWithReturnValue

## Parallelization Plan

**Maximum Parallel Tasks**: 8 (CPU cores available)

### Execution Wave 1: Group 3
- 1 task (sequential)

### Execution Wave 2: Group 4
- 2 tasks in parallel (Task 6 + Task 7)

### Execution Wave 3: Group 5
- 2 tasks sequential (Task 8 → Task 9)

**Total Estimated Time**:
- Sequential: ~20-25 hours
- With parallelization: ~14-18 hours
- **Time Savings**: ~30-35%

## Success Criteria

- [ ] All 70+ new tests pass (100%)
- [ ] Total Phase 45: 110+ tests passing
- [ ] Generated C code uses COM pattern
- [ ] Type-safe function pointers (no void*)
- [ ] lpVtbl always first member
- [ ] Virtual calls use lpVtbl->method pattern
- [ ] All code follows SOLID principles
- [ ] TDD followed throughout
- [ ] Git commits after each group
- [ ] Documentation complete

## Reporting Requirements

Each task/subtask must report:
1. What was done
2. Test results (X/Y passed)
3. What still needs to be done (if any)
4. Issues encountered (if any)

## Problem Resolution Protocol

If any task encounters problems:
1. Spawn research subtask to investigate
2. Spawn experiment subtask to test solutions
3. Report findings
4. Implement fix
5. Re-run tests

## Final Deliverables

1. **Code**:
   - Modified handlers (ConstructorHandler, ExpressionHandler)
   - Test files (5 new test files)
   - CMakeLists.txt updates

2. **Documentation**:
   - `PHASE45-COMPLETE.md` - Comprehensive summary
   - Test coverage statistics
   - Translation examples
   - Code metrics

3. **Git Commits**:
   - Group 3 commit
   - Group 4 commit
   - Group 5 commit
   - Final phase commit (with documentation)

---

**Ready to Execute**: Yes
**Starting with**: Group 3 (Task 5)
**Then**: Group 4 (Tasks 6+7 parallel)
**Then**: Group 5 (Tasks 8→9 sequential)
**Finally**: Documentation and final commit
