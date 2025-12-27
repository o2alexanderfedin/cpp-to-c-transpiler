# Missing C++ Features - Implementation Roadmap

**Created**: 2025-12-26
**Status**: ACTIVE
**Approach**: Kanban - Prioritize low-hanging fruit, minimize dependencies

---

## Executive Summary

Analysis of 14 missing C++ features reveals:
- **4 features** ready for immediate implementation (low dependencies)
- **6 features** require moderate effort (some dependencies)
- **4 features** are complex/low-priority (defer to later)

---

## Feature Analysis Summary

| # | Feature | Current % | Effort (hrs) | Dependencies | Priority | Phase |
|---|---------|-----------|--------------|--------------|----------|-------|
| 7 | Scoped Enums | 85% | 6-8 | None | **HIGH** | 47 |
| 2 | Namespaces | 70% | 6-8 | None | **HIGH** | 48 |
| 4 | Static Members | 35% | 24-36 | None | **HIGH** | 49 |
| 3 | Operator Overloading | 35% | 235-365 | None | **MEDIUM** | 50-52 |
| 6 | Using Declarations | 0% | 12-18 | Namespaces | **MEDIUM** | 53 |
| 8 | Range-For Loops | 0% | 20-30 | Iterators | **MEDIUM** | 54 |
| 5 | Friend Declarations | 0% | 8-12 | Access control | **LOW** | 55 |
| 1 | Virtual Inheritance | 0% | 40-60 | Phase 46 | **MEDIUM** | 56 |
| 10 | Move Semantics | 0% | 50-80 | Rvalue refs | **LOW** | 57 |
| 9 | constexpr/consteval | 0% | 80-120 | Complex | **LOW** | 58 |
| 11 | Variadic Templates | 0% | 60-90 | Templates | **LOW** | 59 |
| 12 | Concepts | 0% | 100-150 | Templates | **VERY LOW** | 60 |
| 13 | Modules | 0% | 150-200 | Build system | **VERY LOW** | 61 |
| 14 | SFINAE | 0% | 120-180 | Templates | **VERY LOW** | 62 |

---

## Kanban Prioritization

### 🟢 **READY** (Can Start Immediately)

#### Phase 47: Complete Scoped Enum Support (6-8 hrs)
- **Current**: 85% complete
- **Remaining**:
  - Add enum type specifications (`enum class X : uint8_t`)
  - Create comprehensive test suite
  - Extract dedicated EnumHandler
- **Dependencies**: None
- **Value**: High (common feature, nearly done)
- **Risk**: Low (mostly tests and polish)

#### Phase 48: Complete Namespace Support (6-8 hrs)
- **Current**: 70% complete
- **Remaining**:
  - Document existing support
  - Add using directives (simplified version)
  - Anonymous namespace support
  - Enhanced test coverage
- **Dependencies**: None
- **Value**: High (fundamental C++ feature)
- **Risk**: Low (core already working)

#### Phase 49: Static Data Members (24-36 hrs)
- **Current**: 35% complete (methods work, data doesn't)
- **Remaining**:
  - Static data member declarations
  - Static member initialization
  - Static member access
- **Dependencies**: None (name mangling exists)
- **Value**: High (common OOP pattern)
- **Risk**: Medium (AST complexity)

---

### 🟡 **NEXT** (After READY Features)

#### Phases 50-52: Operator Overloading (235-365 hrs total)
- **Current**: 35% (static operators done)
- **Split into 3 phases**:
  - **Phase 50**: Arithmetic operators (+, -, *, /, %) - 80-120 hrs
  - **Phase 51**: Comparison & logical (==, !=, <, &&, etc.) - 50-80 hrs
  - **Phase 52**: Special operators (=, ->, [], etc.) - 105-165 hrs
- **Dependencies**: None (framework exists)
- **Value**: High (operator overloading is common)
- **Risk**: High (large scope, many edge cases)

#### Phase 53: Using Declarations (12-18 hrs)
- **Current**: 0%
- **Scope**:
  - Type aliases (`using MyType = ...`)
  - Using directives (`using namespace`)
  - Namespace aliases (`namespace alias = ...`)
- **Dependencies**: Phase 48 (namespaces)
- **Value**: Medium (convenience feature)
- **Risk**: Medium (namespace interaction)

#### Phase 54: Range-Based For Loops (20-30 hrs)
- **Current**: 0%
- **Scope**:
  - `for (auto x : container)` syntax
  - Iterator protocol translation
  - Array and STL container support
- **Dependencies**: Iterators, auto type deduction
- **Value**: High (modern C++ idiom)
- **Risk**: Medium (requires iterator infrastructure)

---

### 🔴 **LATER** (Lower Priority)

#### Phase 55: Friend Declarations (8-12 hrs)
- **Current**: 0%
- **Value**: Low (access control bypass, rare)
- **Risk**: Low (simple concept, limited impact)

#### Phase 56: Virtual Inheritance (40-60 hrs)
- **Current**: 0% (infrastructure exists)
- **Scope**: Diamond pattern, virtual base class tables
- **Dependencies**: Phase 46 (multiple inheritance)
- **Value**: Medium (less common, but important for completeness)
- **Risk**: High (complex vtable management)

#### Phase 57: Move Semantics (50-80 hrs)
- **Current**: 0%
- **Scope**: Rvalue references, move constructors/assignment
- **Dependencies**: References, constructors
- **Value**: Medium (performance optimization)
- **Risk**: High (ownership semantics complex)

#### Phase 58: constexpr/consteval (80-120 hrs)
- **Current**: 0%
- **Scope**: Compile-time evaluation
- **Dependencies**: Expression evaluation engine
- **Value**: Low (optimization feature)
- **Risk**: Very High (requires interpreter)

---

### ⚫ **DEFERRED** (Very Low Priority)

#### Phase 59: Variadic Templates (60-90 hrs)
- **Current**: 0%
- **Value**: Low (advanced template feature)

#### Phase 60: Concepts (100-150 hrs)
- **Current**: 0%
- **Value**: Very Low (C++20 feature, not widespread)

#### Phase 61: Modules (150-200 hrs)
- **Current**: 0%
- **Value**: Very Low (build system overhaul)

#### Phase 62: SFINAE (120-180 hrs)
- **Current**: 0%
- **Value**: Very Low (advanced metaprogramming)

---

## Implementation Strategy

### Parallel Execution Plan

**Sprint 1 (Week 1-2): Quick Wins**
- ✅ Phase 47 (Scoped Enums) - 6-8 hrs
- ✅ Phase 48 (Namespaces) - 6-8 hrs
- **Total**: 12-16 hrs, **2 features complete**

**Sprint 2 (Week 3-4): Medium Features**
- ✅ Phase 49 (Static Members) - 24-36 hrs
- **Total**: 24-36 hrs, **1 feature complete**

**Sprint 3 (Weeks 5-8): Operator Overloading**
- ✅ Phase 50 (Arithmetic) - 80-120 hrs
- ✅ Phase 51 (Comparison) - 50-80 hrs
- **Total**: 130-200 hrs, **2 phases complete**

**Sprint 4 (Weeks 9-10): Modern C++ Features**
- ✅ Phase 53 (Using) - 12-18 hrs
- ✅ Phase 54 (Range-For) - 20-30 hrs
- **Total**: 32-48 hrs, **2 features complete**

---

## Task Breakdown (Map-Reduce Approach)

### Phase 47: Scoped Enums (Parallel Tasks)

**Task 1: Enum Type Specifications** (2-3 hrs)
- Extract underlying type from `EnumDecl`
- Generate C typedef with type annotation
- Test with uint8_t, uint16_t, int32_t

**Task 2: Comprehensive Test Suite** (3-4 hrs)
- Create EnumHandlerTest.cpp
- 15+ test cases for edge cases
- Integration tests with switch/case

**Task 3: Extract EnumTranslator** (1-2 hrs)
- Create dedicated EnumTranslator class
- Follow handler pattern (SOLID)
- Update CppToCVisitor integration

*All 3 tasks can run in parallel, merge at end*

---

### Phase 48: Namespaces (Parallel Tasks)

**Task 1: Documentation** (2-3 hrs)
- User-facing namespace guide
- Supported features list
- Migration guide

**Task 2: Anonymous Namespace Support** (2-3 hrs)
- Detect anonymous namespaces
- Generate unique internal names
- Test file-local linkage

**Task 3: Enhanced Testing** (2-3 hrs)
- 10+ new test cases
- Edge cases (deeply nested, scoped enums)
- Integration with templates

*All 3 tasks independent and parallel*

---

### Phase 49: Static Members (Sequential with Parallel Subtasks)

**Stage 1: Detection & Declaration** (8-12 hrs)
- **Task 1A**: Detect static members in RecordHandler (parallel)
- **Task 1B**: Generate static member declarations (parallel)
- **Task 1C**: Name mangling for static members (parallel)
- Test: Basic static int, const, array

**Stage 2: Initialization** (8-12 hrs)
- **Task 2A**: Out-of-class definition detection (parallel)
- **Task 2B**: Global variable generation (parallel)
- **Task 2C**: Initializer expression translation (parallel)
- Test: Static member with complex initializers

**Stage 3: Access & References** (8-12 hrs)
- **Task 3A**: Scope-resolved DeclRefExpr (parallel)
- **Task 3B**: Member access through class name (parallel)
- **Task 3C**: Integration with ExpressionHandler (sequential after 3A, 3B)
- Test: Read/write static members

*Sequential stages, but tasks within each stage run in parallel*

---

### Phase 50: Arithmetic Operators (Map-Reduce)

**Map Phase**: Implement individual operators in parallel (10 tasks)
- Task 1: Binary + operator (8 hrs)
- Task 2: Binary - operator (8 hrs)
- Task 3: Binary * operator (8 hrs)
- Task 4: Binary / operator (8 hrs)
- Task 5: Binary % operator (8 hrs)
- Task 6: Unary - operator (6 hrs)
- Task 7: Prefix ++ operator (8 hrs)
- Task 8: Postfix ++ operator (8 hrs)
- Task 9: Prefix -- operator (8 hrs)
- Task 10: Postfix -- operator (8 hrs)

**Reduce Phase**: Integration & testing (8-12 hrs)
- Merge all operator handlers
- Create unified OperatorTranslator
- Comprehensive integration tests
- Edge cases (chaining, mixed types)

*All 10 operators can be implemented in parallel by different agents*

---

## Success Criteria

### Phase Completion Checklist

Each phase must meet:
- ✅ All unit tests passing (100%)
- ✅ Integration tests created and passing
- ✅ TDD followed (tests before implementation)
- ✅ SOLID principles adhered to
- ✅ Documentation updated
- ✅ Code reviewed by separate agent
- ✅ No regressions in existing tests
- ✅ Committed to git with proper message

---

## Dependencies Graph

```
Phase 47 (Enums) ────────┐
                          ├──> Phase 53 (Using) ──> Phase 54 (Range-For)
Phase 48 (Namespaces) ───┘

Phase 49 (Static) ────────> [All other OOP features]

Phase 50-52 (Operators) ─> Phase 54 (Range-For)
                          ├──> Phase 57 (Move Semantics)
                          └──> Phase 58 (constexpr)

Phase 46 (Multiple) ─────> Phase 56 (Virtual Inheritance)

Phase 11 (Templates) ────> Phase 59 (Variadic Templates)
                          ├──> Phase 60 (Concepts)
                          └──> Phase 62 (SFINAE)
```

---

## Resource Allocation

### Optimal Parallelization

**Week 1-2**: 3 parallel agents
- Agent 1: Phase 47 (Enums)
- Agent 2: Phase 48 (Namespaces)
- Agent 3: Test infrastructure prep

**Week 3-4**: 3 parallel agents
- Agent 1: Phase 49 Stage 1 (Detection)
- Agent 2: Phase 49 Stage 2 (Init)
- Agent 3: Phase 49 Stage 3 (Access)

**Week 5-8**: 10 parallel agents (Map-Reduce)
- Agents 1-10: Individual arithmetic operators
- Agent 11 (Reduce): Integration & testing

---

## Estimated Timeline

**Optimistic** (100% parallel, no blockers): 8-10 weeks
**Realistic** (75% parallel, some blockers): 12-16 weeks
**Conservative** (50% parallel, many blockers): 20-24 weeks

**First 7 features complete** (through Phase 54): 10-14 weeks

---

## Next Steps

1. **Immediate**: Create Phase 47 detailed plan (scoped enums)
2. **Day 2**: Create Phase 48 detailed plan (namespaces)
3. **Day 3**: Create Phase 49 detailed plan (static members)
4. **Week 2**: Begin Phase 47 & 48 execution in parallel
5. **Week 4**: Begin Phase 49 execution
6. **Week 6**: Begin Phase 50 (arithmetic operators) with map-reduce

---

## Notes

- Phases 60-62 (Concepts, Modules, SFINAE) deferred indefinitely
- Virtual inheritance (Phase 56) deferred until after operator overloading
- Move semantics (Phase 57) requires significant architectural work
- constexpr (Phase 58) requires compile-time evaluator (major undertaking)

**Recommendation**: Focus on Phases 47-54 for next 3-4 months to achieve 80%+ C++ feature coverage.
