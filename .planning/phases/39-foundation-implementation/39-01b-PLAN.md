# Phase 39-01b: Remaining Core Handlers (Parallel Execution)

## Objective

Implement VariableHandler, ExpressionHandler, and StatementHandler in parallel using TDD methodology. These three handlers can be developed independently as they have no interdependencies.

**Goal:** Complete all basic AST-to-AST translation handlers for Phase 1 features.

**Parallelization:** Tasks 1-3 execute in parallel (3 subagents simultaneously)

## Context

@docs/architecture/10-phase1-detailed-plan.md - Steps 11-60 (handler TDD cycles)
@docs/architecture/handlers/VariableHandler.md
@docs/architecture/handlers/ExpressionHandler.md
@docs/architecture/handlers/StatementHandler.md
@tests/fixtures/HandlerTestFixture.h - Existing test infrastructure
@include/handlers/HandlerContext.h - Existing context
@include/handlers/FunctionHandler.h - Reference implementation

## Tasks

### Task 1: Implement VariableHandler with TDD (PARALLEL)
**Type**: auto
**Estimated**: 3-4 hours
**Parallelizable**: YES - Independent from other handlers

**Action**: Implement VariableHandler for local variables

**TDD Cycles (15+ tests):**
1. LocalVariableNoInit - `int x;`
2. LocalVariableWithIntInit - `int x = 5;`
3. LocalVariableWithFloatInit - `float y = 3.14;`
4. LocalVariableUsedInExpr - Variable used in arithmetic
5. MultipleLocalVariables - Multiple vars in same scope
6. VariableReassignment - `x = 10;`
7. VariableWithComplexInit - `int z = x + y;`
8. ConstVariable - `const int c = 5;`
9. VariableShadowing - Inner scope shadowing outer
10. VariableInCompoundStmt - Vars in `{}` blocks
... (15+ total)

**Implementation:**
- `include/handlers/VariableHandler.h`
- `src/handlers/VariableHandler.cpp`
- `tests/unit/handlers/VariableHandlerTest.cpp`

**Verification:**
- [ ] 15+ unit tests pass (100%)
- [ ] Local variables translate correctly
- [ ] Initialization handled properly
- [ ] Variable references work
- [ ] Const qualifier preserved

---

### Task 2: Implement ExpressionHandler with TDD (PARALLEL)
**Type**: auto
**Estimated**: 5-7 hours
**Parallelizable**: YES - Independent from other handlers

**Action**: Implement ExpressionHandler for arithmetic, literals, and variable references

**TDD Cycles (35+ tests):**

**Literals (5 tests):**
1. IntegerLiteral - `42`
2. NegativeIntegerLiteral - `-10`
3. FloatingLiteral - `3.14`
4. NegativeFloatLiteral - `-2.5`
5. ZeroLiteral - `0`

**Binary Operators (15 tests):**
6. BinaryAddition - `a + b`
7. BinarySubtraction - `a - b`
8. BinaryMultiplication - `a * b`
9. BinaryDivision - `a / b`
10. BinaryModulo - `a % b`
11. NestedAddition - `(a + b) + c`
12. NestedMultiplication - `(a * b) * c`
13. MixedArithmetic - `a + b * c`
14. ComplexNesting - `(a + b) * (c - d)`
15. ParenthesizedExpression - `(a + b)`
... (more precedence tests)

**Unary Operators (5 tests):**
21. UnaryMinus - `-x`
22. UnaryPlus - `+x`
23. UnaryIncrement - `++x`
24. UnaryDecrement - `--x`
25. PostfixIncrement - `x++`

**DeclRefExpr (5 tests):**
26. SimpleVarRef - Reference to variable
27. VarRefInExpr - Variable in expression
28. MultipleVarRefs - Multiple variables
29. VarRefNested - Var in nested expr
30. ConstVarRef - Reference to const var

**Complex Expressions (5+ tests):**
31. ArithmeticChain - `a + b - c * d / e`
32. DeepNesting - Very nested expressions
33. AllOperators - Mix of all arithmetic
34. LargeExpression - Many operations
35. EdgeCases - Zero division protection, etc.

**Implementation:**
- `include/handlers/ExpressionHandler.h`
- `src/handlers/ExpressionHandler.cpp`
- `tests/unit/handlers/ExpressionHandlerTest.cpp`

**Verification:**
- [ ] 35+ unit tests pass (100%)
- [ ] All arithmetic operators work
- [ ] Literals translate correctly
- [ ] Variable references work
- [ ] Nested expressions handled
- [ ] Operator precedence correct

---

### Task 3: Implement StatementHandler with TDD (PARALLEL)
**Type**: auto
**Estimated**: 2-3 hours
**Parallelizable**: YES - Independent from other handlers

**Action**: Implement StatementHandler for return and compound statements

**TDD Cycles (12+ tests):**

**Return Statements (6 tests):**
1. ReturnVoid - `return;`
2. ReturnInt - `return 42;`
3. ReturnFloat - `return 3.14;`
4. ReturnExpression - `return a + b;`
5. ReturnComplexExpr - `return (a * b) + c;`
6. ReturnVarRef - `return x;`

**Compound Statements (6+ tests):**
7. CompoundStmtEmpty - `{}`
8. CompoundStmtSingleStmt - `{ return 0; }`
9. CompoundStmtMultiple - `{ int x = 5; return x; }`
10. NestedCompoundStmt - `{ { return 0; } }`
11. CompoundWithVars - Multiple vars and stmts
12. CompoundWithExprs - Expressions in compound

**Implementation:**
- `include/handlers/StatementHandler.h`
- `src/handlers/StatementHandler.cpp`
- `tests/unit/handlers/StatementHandlerTest.cpp`

**Verification:**
- [ ] 12+ unit tests pass (100%)
- [ ] Return statements work correctly
- [ ] Compound statements work
- [ ] Statement sequences handled
- [ ] Nesting works properly

---

## Parallel Execution Strategy

**All 3 tasks execute simultaneously:**

```
Subagent 1: VariableHandler (Task 1)
     │
     ├─ Write 15+ TDD tests
     ├─ Implement VariableHandler
     ├─ Run tests, verify 100% pass
     └─ Report results

Subagent 2: ExpressionHandler (Task 2)
     │
     ├─ Write 35+ TDD tests
     ├─ Implement ExpressionHandler
     ├─ Run tests, verify 100% pass
     └─ Report results

Subagent 3: StatementHandler (Task 3)
     │
     ├─ Write 12+ TDD tests
     ├─ Implement StatementHandler
     ├─ Run tests, verify 100% pass
     └─ Report results

──────────────────────────────────
        After all complete:
        Aggregate results
        Create SUMMARY.md
        Commit all changes
```

## Verification

**Phase 39-01b Completion Criteria:**

1. **VariableHandler Complete:**
   - [ ] 15+ tests passing
   - [ ] Local variables working
   - [ ] Initialization correct
   - [ ] Integration with context

2. **ExpressionHandler Complete:**
   - [ ] 35+ tests passing
   - [ ] All operators working
   - [ ] Literals correct
   - [ ] Precedence correct
   - [ ] Nesting handled

3. **StatementHandler Complete:**
   - [ ] 12+ tests passing
   - [ ] Return statements working
   - [ ] Compound statements working
   - [ ] Nesting handled

4. **Overall:**
   - [ ] Total 62+ tests passing (100%)
   - [ ] All handlers compile without warnings
   - [ ] Code follows SOLID principles
   - [ ] Well documented
   - [ ] CMake updated

## Success Criteria

✅ 3 core handlers implemented with TDD
✅ 62+ new tests passing (total 65+ with FunctionHandler)
✅ All handlers follow established pattern
✅ Ready for integration testing (Phase 39-01c)

**Estimated Total:** 10-14 hours (with parallelization: 5-7 hours calendar time)

## Output

Create `.planning/phases/39-foundation-implementation/39-01b-SUMMARY.md` with:

**Deliverables:**
- 3 handlers implemented (Variable, Expression, Statement)
- 62+ tests passing
- Total cumulative tests: 65+

**Statistics:**
- Files created (handlers + tests)
- LOC breakdown per handler
- Test counts per handler

**Parallel Execution Results:**
- Subagent 1 (VariableHandler) results
- Subagent 2 (ExpressionHandler) results
- Subagent 3 (StatementHandler) results
- Aggregated metrics

**Next Steps:**
- Phase 39-01c: Integration testing
- Phase 39-01d: Pipeline completion

**Commit:**
Format: `feat(phase1): Implement VariableHandler, ExpressionHandler, StatementHandler`
