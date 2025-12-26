# Implementation Timeline & Effort Estimates

## Overview

This document provides detailed effort estimates for implementing all 12 phases of the C++ to C transpiler, broken down into atomic work units with realistic time estimates.

**Total Estimated Effort:** 204-281 hours (~26-35 working days, ~5-7 weeks)
**With Parallelization:** ~4-6 weeks calendar time (with 2-4 developers)

---

## Phase 1: Basic Functions & Arithmetic

### Sub-tasks

#### 1.1 Test Infrastructure Setup (8-10 hours)
- **1.1.1** Implement MockASTContext (4-5 hours, 300-400 LOC)
  - Function builder
  - Variable builder
  - Expression builders (literals, binary ops, var refs)
  - Statement builders (compound, return)

- **1.1.2** Implement CNodeBuilder (2-3 hours, 150-200 LOC)
  - Function creation
  - Parameter creation
  - Basic expression creation

- **1.1.3** Implement HandlerTestFixture (1-2 hours, 100-150 LOC)
  - Base test class
  - Helper methods

- **1.1.4** Setup CMake test configuration (1 hour, 50-100 LOC)

#### 1.2 FunctionHandler Implementation (6-8 hours)
- **1.2.1** Write unit tests (3-4 hours, 250-300 LOC)
  - 18 unit tests from test plan

- **1.2.2** Implement handler (3-4 hours, 200-300 LOC)
  - `canHandle()` method
  - `handleFunctionDecl()` method
  - Parameter translation
  - Return type translation
  - Body translation (delegate to StatementHandler)

#### 1.3 VariableHandler Implementation (4-6 hours)
- **1.3.1** Write unit tests (2-3 hours, 200-250 LOC)
  - 15 unit tests from test plan

- **1.3.2** Implement handler (2-3 hours, 150-200 LOC)
  - `canHandle()` method
  - `handleVarDecl()` for local scope
  - Initialization handling

#### 1.4 ExpressionHandler Implementation (8-10 hours)
- **1.4.1** Write unit tests (4-5 hours, 450-550 LOC)
  - 35 unit tests from test plan

- **1.4.2** Implement handler (4-5 hours, 300-400 LOC)
  - `canHandle()` method
  - Literal handling (int, float)
  - Binary operators (+, -, *, /, %)
  - Variable references
  - Implicit casts (transparent)

#### 1.5 StatementHandler Implementation (3-4 hours)
- **1.5.1** Write unit tests (1-2 hours, 150-200 LOC)
  - 12 unit tests from test plan

- **1.5.2** Implement handler (2 hours, 50-100 LOC)
  - Return statements
  - Compound statements
  - Declaration statements

#### 1.6 Integration Testing (6-8 hours)
- **1.6.1** Write integration tests (3-4 hours, 300-400 LOC)
  - 25 integration tests from test plan

- **1.6.2** Write E2E tests (2-3 hours, 200-300 LOC)
  - 10 E2E tests from test plan

- **1.6.3** Debug and fix issues (1-2 hours)

### Phase 1 Totals
**Implementation:** 700-1000 LOC, 10-14 hours
**Testing:** 1300-2000 LOC, 11-15 hours
**Total:** 2000-3000 LOC, 21-29 hours (~3-4 days)

### Parallelization
- Test infrastructure: Sequential (must complete first)
- Handlers: Can parallelize 2-3 developers (FunctionHandler + VariableHandler + ExpressionHandler)
- Integration tests: Sequential (after handlers complete)

**With parallelization: 15-20 hours calendar time**

---

## Phase 2: Control Flow (14-19 hours, ~2-3 days)

### Sub-tasks

#### 2.1 StatementHandler Extensions (5-7 hours)
- **2.1.1** Write unit tests (2-3 hours, 200-250 LOC)
  - 15 tests: if/else, while, for, switch

- **2.1.2** Implement extensions (3-4 hours, 200-300 LOC)
  - If/else, while, for, switch, break, continue

#### 2.2 ExpressionHandler Extensions (4-6 hours)
- **2.2.1** Write unit tests (2-3 hours, 150-200 LOC)
  - 12 tests: comparison, logical, unary operators

- **2.2.2** Implement extensions (2-3 hours, 100-150 LOC)
  - Comparison operators, logical operators, unary operators

#### 2.3 Integration Testing (5-6 hours)
- **2.3.1** Write integration tests (2-3 hours, 250-300 LOC)
  - 15 integration tests

- **2.3.2** Write E2E tests (2-3 hours, 200-250 LOC)
  - 8 E2E tests

### Phase 2 Totals
**Implementation:** 300-450 LOC, 5-7 hours
**Testing:** 800-1000 LOC, 9-12 hours
**Total:** 1100-1450 LOC, 14-19 hours

---

## Phase 3: Global Variables & Types (10-15 hours, ~1-2 days)

### Sub-tasks

#### 3.1 VariableHandler Extensions (4-6 hours)
- **3.1.1** Write unit tests (2-3 hours, 150-200 LOC)
  - 10 tests: globals, static, arrays

- **3.1.2** Implement extensions (2-3 hours, 150-200 LOC)
  - Global scope, static locals, array declarations

#### 3.2 ExpressionHandler Extensions (3-5 hours)
- **3.2.1** Write unit tests (1-2 hours, 100-150 LOC)
  - 8 tests: strings, chars, casts, array subscript

- **3.2.2** Implement extensions (2-3 hours, 100-150 LOC)
  - String literals, char literals, casts, array subscript

#### 3.3 Integration Testing (3-4 hours)
- **3.3.1** Write integration tests (2-3 hours, 150-200 LOC)
- **3.3.2** Write E2E tests (1-2 hours, 150-200 LOC)

### Phase 3 Totals
**Implementation:** 250-350 LOC, 4-6 hours
**Testing:** 550-750 LOC, 6-9 hours
**Total:** 800-1100 LOC, 10-15 hours

---

## Phase 4: Structs (C-style) (11-16 hours, ~1.5-2 days)

### Sub-tasks

#### 4.1 RecordHandler Implementation (5-7 hours)
- **4.1.1** Write unit tests (2-3 hours, 150-200 LOC)
  - 12 tests: struct declarations, fields, nesting

- **4.1.2** Implement handler (3-4 hours, 200-300 LOC)
  - Struct declaration handling
  - Field translation
  - Nested structs

#### 4.2 ExpressionHandler Extensions (3-4 hours)
- **4.2.1** Write unit tests (1-2 hours, 75-100 LOC)
  - 5 tests: member access

- **4.2.2** Implement extensions (2 hours, 100-150 LOC)
  - Member access (`.` and `->`)

#### 4.3 Integration Testing (3-5 hours)
- **4.3.1** Write integration tests (2-3 hours, 200-250 LOC)
- **4.3.2** Write E2E tests (1-2 hours, 150-200 LOC)

### Phase 4 Totals
**Implementation:** 300-450 LOC, 5-7 hours
**Testing:** 575-750 LOC, 6-9 hours
**Total:** 875-1200 LOC, 11-16 hours

---

## Phase 5: Pointers & References (15-21 hours, ~2-3 days)

### Sub-tasks

#### 5.1 TypeTranslator Implementation (3-4 hours)
- **5.1.1** Write unit tests (1-2 hours, 100-150 LOC)
- **5.1.2** Implement translator (2 hours, 150-200 LOC)
  - Reference → pointer conversion
  - Type mapping

#### 5.2 FunctionHandler Extensions (3-4 hours)
- **5.2.1** Write unit tests (1-2 hours, 100-150 LOC)
  - Reference parameter tests

- **5.2.2** Implement extensions (2 hours, 100-150 LOC)
  - Reference parameter translation
  - Call site rewriting

#### 5.3 ExpressionHandler Extensions (5-7 hours)
- **5.3.1** Write unit tests (2-3 hours, 200-250 LOC)
  - 15 tests: pointers, references, nullptr

- **5.3.2** Implement extensions (3-4 hours, 200-250 LOC)
  - Address-of, dereference, pointer arithmetic, nullptr

#### 5.4 Integration Testing (4-6 hours)
- **5.4.1** Write integration tests (2-3 hours, 250-300 LOC)
- **5.4.2** Write E2E tests (2-3 hours, 200-250 LOC)

### Phase 5 Totals
**Implementation:** 450-600 LOC, 8-10 hours
**Testing:** 850-1100 LOC, 7-11 hours
**Total:** 1300-1700 LOC, 15-21 hours

---

## Phase 6: Classes (Simple) (24-33 hours, ~3-4 days)

### Sub-tasks

#### 6.1 RecordHandler Extensions (4-6 hours)
- **6.1.1** Write unit tests (2-3 hours, 125-175 LOC)
  - 10 tests: class → struct

- **6.1.2** Implement extensions (2-3 hours, 100-150 LOC)
  - Class → struct conversion
  - Access specifier removal

#### 6.2 MethodHandler Implementation (7-10 hours)
- **6.2.1** Write unit tests (3-4 hours, 200-250 LOC)
  - 15 tests: methods → functions

- **6.2.2** Implement handler (4-6 hours, 250-350 LOC)
  - Method translation
  - `this` parameter addition
  - Name mangling

#### 6.3 ConstructorHandler Implementation (5-7 hours)
- **6.3.1** Write unit tests (2-3 hours, 125-175 LOC)
  - 10 tests: constructors → init functions

- **6.3.2** Implement handler (3-4 hours, 200-250 LOC)
  - Constructor translation
  - Initialization logic

#### 6.4 DestructorHandler Implementation (4-6 hours)
- **6.4.1** Write unit tests (2-3 hours, 100-150 LOC)
  - 8 tests: destructors → destroy functions

- **6.4.2** Implement handler (2-3 hours, 100-150 LOC)
  - Destructor translation
  - Auto-injection logic

#### 6.5 ExpressionHandler Extensions (3-4 hours)
- **6.5.1** Write unit tests (1-2 hours, 75-100 LOC)
  - 5 tests: `this` pointer

- **6.5.2** Implement extensions (2 hours, 100-150 LOC)
  - `this` expression handling

#### 6.6 Integration Testing (8-11 hours)
- **6.6.1** Write integration tests (4-5 hours, 350-450 LOC)
  - 20 integration tests

- **6.6.2** Write E2E tests (3-4 hours, 250-350 LOC)
  - 8 E2E tests

- **6.6.3** Debug and fix issues (1-2 hours)

### Phase 6 Totals
**Implementation:** 750-1050 LOC, 13-18 hours
**Testing:** 1225-1600 LOC, 11-15 hours
**Total:** 1975-2650 LOC, 24-33 hours

---

## Phase 7: Method Calls (14-19 hours, ~2-3 days)

### Sub-tasks

#### 7.1 ExpressionHandler Extensions (6-8 hours)
- **7.1.1** Write unit tests (3-4 hours, 200-250 LOC)
  - 15 tests: method calls

- **7.1.2** Implement extensions (3-4 hours, 250-350 LOC)
  - Method call translation
  - Overload name mangling

#### 7.2 MethodHandler Extensions (3-4 hours)
- **7.2.1** Write unit tests (1-2 hours, 75-100 LOC)
- **7.2.2** Implement overload mangling (2 hours, 100-150 LOC)

#### 7.3 Integration Testing (5-7 hours)
- **7.3.1** Write integration tests (2-3 hours, 250-300 LOC)
- **7.3.2** Write E2E tests (2-3 hours, 200-250 LOC)
- **7.3.3** Debug (1 hour)

### Phase 7 Totals
**Implementation:** 350-500 LOC, 6-8 hours
**Testing:** 725-900 LOC, 8-11 hours
**Total:** 1075-1400 LOC, 14-19 hours

---

## Phase 8: Enums (10-15 hours, ~1-2 days)

### Sub-tasks

#### 8.1 EnumHandler Implementation (5-7 hours)
- **8.1.1** Write unit tests (2-3 hours, 175-225 LOC)
  - 15 tests: unscoped, scoped enums

- **8.1.2** Implement handler (3-4 hours, 200-250 LOC)
  - Enum translation
  - Scoped enum prefixing

#### 8.2 ExpressionHandler Extensions (2-3 hours)
- **8.2.1** Write unit tests (1 hour, 50-75 LOC)
- **8.2.2** Implement extensions (1-2 hours, 50-100 LOC)
  - Enum constant references

#### 8.3 Integration Testing (3-5 hours)
- **8.3.1** Write integration tests (2-3 hours, 150-200 LOC)
- **8.3.2** Write E2E tests (1-2 hours, 150-200 LOC)

### Phase 8 Totals
**Implementation:** 250-350 LOC, 4-6 hours
**Testing:** 525-700 LOC, 6-9 hours
**Total:** 775-1050 LOC, 10-15 hours

---

## Phase 9: Inheritance (Single) (19-26 hours, ~2.5-3.5 days)

### Sub-tasks

#### 9.1 RecordHandler Extensions (5-7 hours)
- **9.1.1** Write unit tests (2-3 hours, 125-175 LOC)
  - 10 tests: inheritance embedding

- **9.1.2** Implement extensions (3-4 hours, 200-250 LOC)
  - Base class embedding
  - Single inheritance checks

#### 9.2 ConstructorHandler & DestructorHandler Extensions (4-6 hours)
- **9.2.1** Write unit tests (2-3 hours, 75-100 LOC)
- **9.2.2** Implement constructor chaining (1-2 hours, 100-150 LOC)
- **9.2.3** Implement destructor chaining (1 hour, 50-100 LOC)

#### 9.3 ExpressionHandler Extensions (5-7 hours)
- **9.3.1** Write unit tests (2-3 hours, 100-150 LOC)
  - 8 tests: base field/method access

- **9.3.2** Implement extensions (3-4 hours, 150-200 LOC)
  - Base field access rewriting
  - Base method call rewriting

#### 9.4 Integration Testing (5-6 hours)
- **9.4.1** Write integration tests (3-4 hours, 300-350 LOC)
- **9.4.2** Write E2E tests (2 hours, 250-300 LOC)

### Phase 9 Totals
**Implementation:** 500-650 LOC, 9-12 hours
**Testing:** 850-1075 LOC, 10-14 hours
**Total:** 1350-1725 LOC, 19-26 hours

---

## Phase 10: Templates (Monomorphization) (25-33 hours, ~3-4 days)

### Sub-tasks

#### 10.1 TemplateMonomorphizer Extensions (10-13 hours)
- **10.1.1** Write unit tests (4-5 hours, 300-400 LOC)
  - 20 tests: class & function templates

- **10.1.2** Implement extensions (6-8 hours, 400-500 LOC)
  - Template instantiation detection
  - Monomorphization
  - Name mangling

#### 10.2 RecordHandler & FunctionHandler Integration (3-4 hours)
- **10.2.1** Write unit tests (1-2 hours, 100-150 LOC)
- **10.2.2** Implement integration (2 hours, 100-150 LOC)

#### 10.3 Integration Testing (12-16 hours)
- **10.3.1** Write integration tests (4-5 hours, 400-500 LOC)
- **10.3.2** Write E2E tests (3-4 hours, 300-400 LOC)
- **10.3.3** Debug complex template cases (5-7 hours)

### Phase 10 Totals
**Implementation:** 600-800 LOC, 12-15 hours
**Testing:** 1100-1450 LOC, 13-18 hours
**Total:** 1700-2250 LOC, 25-33 hours

---

## Phase 11: Virtual Methods (Advanced) (29-38 hours, ~4-5 days)

### Sub-tasks

#### 11.1 VirtualMethodHandler Implementation (13-17 hours)
- **11.1.1** Write unit tests (5-7 hours, 350-450 LOC)
  - 25 tests: vtables, virtual calls, abstract classes

- **11.1.2** Implement handler (8-10 hours, 500-700 LOC)
  - Vtable generation
  - Virtual call translation
  - Abstract class handling

#### 11.2 RecordHandler, ConstructorHandler, ExpressionHandler Extensions (6-8 hours)
- **11.2.1** Write unit tests (2-3 hours, 125-175 LOC)
- **11.2.2** Implement vtable integration (4-5 hours, 250-350 LOC)

#### 11.3 Integration Testing (10-13 hours)
- **11.3.1** Write integration tests (4-5 hours, 400-500 LOC)
- **11.3.2** Write E2E tests (3-4 hours, 300-400 LOC)
- **11.3.3** Debug polymorphism (3-4 hours)

### Phase 11 Totals
**Implementation:** 750-1050 LOC, 13-17 hours
**Testing:** 1175-1525 LOC, 16-21 hours
**Total:** 1925-2575 LOC, 29-38 hours

---

## Phase 12: Namespaces (12-17 hours, ~1.5-2 days)

### Sub-tasks

#### 12.1 NamespaceHandler Implementation (5-7 hours)
- **12.1.1** Write unit tests (2-3 hours, 175-225 LOC)
  - 15 tests: namespaces, using directives

- **12.1.2** Implement handler (3-4 hours, 200-300 LOC)
  - Namespace tracking
  - Name prefixing

#### 12.2 All Handlers Integration (3-4 hours)
- **12.2.1** Write unit tests (1-2 hours, 75-100 LOC)
- **12.2.2** Implement namespace prefix integration (2 hours, 150-200 LOC)

#### 12.3 Integration Testing (4-6 hours)
- **12.3.1** Write integration tests (2-3 hours, 200-250 LOC)
- **12.3.2** Write E2E tests (1-2 hours, 150-200 LOC)
- **12.3.3** Final integration testing (1 hour)

### Phase 12 Totals
**Implementation:** 350-500 LOC, 6-8 hours
**Testing:** 600-775 LOC, 6-9 hours
**Total:** 950-1275 LOC, 12-17 hours

---

## Grand Totals

### By Category

**Implementation LOC:** 6150-8850 LOC
**Testing LOC:** 11,350-13,250 LOC
**Total LOC:** 17,500-22,100 LOC

**Implementation Hours:** 103-147 hours
**Testing Hours:** 101-134 hours
**Total Hours:** 204-281 hours

### By Phase

| Phase | Implementation | Testing | Total | Days |
|-------|---------------|---------|-------|------|
| 1 | 10-14h | 11-15h | 21-29h | 3-4 |
| 2 | 5-7h | 9-12h | 14-19h | 2-3 |
| 3 | 4-6h | 6-9h | 10-15h | 1-2 |
| 4 | 5-7h | 6-9h | 11-16h | 1.5-2 |
| 5 | 8-10h | 7-11h | 15-21h | 2-3 |
| 6 | 13-18h | 11-15h | 24-33h | 3-4 |
| 7 | 6-8h | 8-11h | 14-19h | 2-3 |
| 8 | 4-6h | 6-9h | 10-15h | 1-2 |
| 9 | 9-12h | 10-14h | 19-26h | 2.5-3.5 |
| 10 | 12-15h | 13-18h | 25-33h | 3-4 |
| 11 | 13-17h | 16-21h | 29-38h | 4-5 |
| 12 | 6-8h | 6-9h | 12-17h | 1.5-2 |
| **Total** | **103-147h** | **101-134h** | **204-281h** | **26-35** |

---

## Parallelization Strategy

### Maximum Parallelism by Phase

**Phase 1:** 4 developers (infrastructure, 4 handlers)
- Calendar time: ~7-10 days

**Phase 2-3:** 2-3 developers (extensions in parallel)
- Calendar time: ~2-3 days each

**Phase 4-5:** 2 developers (RecordHandler, ExpressionHandler)
- Calendar time: ~2-3 days each

**Phase 6:** 4 developers (RecordHandler, MethodHandler, ConstructorHandler, DestructorHandler)
- Calendar time: ~7-10 days

**Phase 7-8:** 2 developers
- Calendar time: ~2-3 days each

**Phase 9-12:** Sequential (complex interdependencies)
- Calendar time: ~15-20 days

### Optimized Calendar Time

**With 4 developers working in parallel:**
- Total calendar time: ~35-50 days (~7-10 weeks)

**With 2 developers:**
- Total calendar time: ~50-70 days (~10-14 weeks)

**Solo developer:**
- Total calendar time: ~26-35 working days (~6-8 weeks with breaks)

---

## Risk Assessment

### High-Risk Items (Complexity 5)

1. **Phase 10: Templates** (25-33 hours)
   - Risk: Template metaprogramming edge cases
   - Mitigation: Start with simple templates, add complexity incrementally
   - Contingency: +10-15 hours for edge cases

2. **Phase 11: Virtual Methods** (29-38 hours)
   - Risk: Vtable generation complexity
   - Mitigation: Study existing vtable implementations
   - Contingency: +15-20 hours for debugging

### Medium-Risk Items (Complexity 3-4)

3. **Phase 6: Classes** (24-33 hours)
   - Risk: Method transformation complexity
   - Mitigation: TDD with many small tests

4. **Phase 9: Inheritance** (19-26 hours)
   - Risk: Base class access rewriting
   - Mitigation: Clear separation of concerns

### Contingency Buffer

**Recommended buffer:** 20% of total time
- Total estimate: 204-281 hours
- With buffer: 245-337 hours (~30-42 working days)

---

## Verification Gates

### After Phase 3
- **Checkpoint:** Basic C functionality complete
- **Criteria:** All procedural C++ programs transpile correctly
- **Review:** Architecture, test coverage, code quality
- **Decision:** Proceed to OOP features or refactor

### After Phase 8
- **Checkpoint:** Direct-mapping features complete
- **Criteria:** C-style C++ programs work
- **Review:** Performance, generated code quality
- **Decision:** Proceed to advanced features

### After Phase 12
- **Checkpoint:** All features complete
- **Criteria:** Full C++ subset supported
- **Review:** Final quality, documentation, release readiness
- **Decision:** Release 1.0 or add features

---

## Success Metrics

### Code Quality
- [ ] 100% handler test coverage
- [ ] All E2E tests passing
- [ ] No compiler warnings
- [ ] Clean valgrind runs

### Performance
- [ ] Transpilation < 1s for small files (<1000 LOC)
- [ ] Transpilation < 10s for large files (<10,000 LOC)
- [ ] Memory usage reasonable

### Generated Code Quality
- [ ] Compiles with `-Wall -Werror`
- [ ] Readable and maintainable
- [ ] Similar performance to hand-written C
- [ ] No unnecessary allocations

---

## Timeline Assumptions

**Working Hours:**
- 8 hours/day productive work
- 5 days/week
- Account for meetings, breaks, context switches

**Velocity:**
- New code: 20-30 LOC/hour (with tests)
- Test code: 30-40 LOC/hour
- Debugging: 2-4 hours per phase

**Learning Curve:**
- First few phases slower (learning Clang API)
- Later phases faster (patterns established)

---

## Next Steps

1. Begin Phase 1 implementation immediately
2. Track actual time vs estimates
3. Adjust estimates for future phases
4. Maintain daily progress log
5. Review and adjust at each verification gate
