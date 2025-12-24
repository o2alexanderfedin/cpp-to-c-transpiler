# C++23 Feature Support Implementation Plan Summary

**One-liner**: 6-phase roadmap (16 weeks) to incrementally add C++23 feature support through visitor-pattern transformations, targeting 20-25% coverage via 8 language features with 100+ new tests.

**Version**: v1

## Key Findings

### Feature Prioritization (8 features across 3 tiers)

**Priority 1 (Must Have)**:
- Multidimensional subscript operator (P2128R6) - 16 tests, low complexity
- Deducing this (P0847R7) - 22 tests, medium complexity, high impact
- if consteval (P1938R3) - 13 tests, high complexity

**Priority 2 (Should Have)**:
- Static operator() and operator[] (P1169R4) - 8 tests, low complexity
- auto(x) decay-copy (P0849R8) - 22 tests (partial), medium complexity

**Priority 3 (Nice to Have)**:
- [[assume]] attribute (P1774R8) - 13 tests, very low complexity
- Constexpr enhancements - 19 tests, high complexity, partial support only
- CTAD with inherited constructors (P2582R1) - 10 tests, medium complexity

### Phase Structure (6 phases, 2-4 weeks each)

1. **Phase 1 (Weeks 1-2)**: Multidimensional subscript - simplest feature, validates workflow
2. **Phase 2 (Weeks 3-4)**: Static operators - builds on Phase 1 operator knowledge
3. **Phase 3 (Weeks 5-6)**: [[assume]] attribute - low complexity, high test coverage
4. **Phase 4 (Weeks 7-10)**: Deducing this - most impactful, highest complexity
5. **Phase 5 (Weeks 11-13)**: if consteval - complex, may require runtime fallback
6. **Phase 6 (Weeks 14-16)**: Partial constexpr + auto(x) - mop-up phase

### Technical Approach

**Architecture foundation** (already proven):
- Three-stage pipeline: Clang parsing → C AST transformation → C99 emission
- RecursiveASTVisitor pattern for AST traversal
- Handler classes (Translator/Transformer) for feature-specific logic
- CNodeBuilder for C AST node construction

**Implementation pattern** (per feature):
```
1. Add Visit method to CppToCVisitor
2. Create {Feature}Translator class
3. Implement transform() using CNodeBuilder
4. Write unit tests + integration tests
5. A/B test for correctness
```

**Expected improvements**:
- Phase 1: +3-4% (multidim subscript)
- Phase 2: +1-2% (static operators)
- Phase 3: +2% ([[assume]])
- Phase 4: +3-4% (deducing this)
- Phase 5: +2% (if consteval)
- Phase 6: +4-5% (constexpr + auto(x))
- **Total: 20-25% C++23 support**

### Risk Assessment

**High risks**:
- Deducing this (Phase 4): Overload expansion complexity - mitigate with 4-week budget, minimal support fallback
- if consteval (Phase 5): Compile-time evaluation hard in C - accept runtime fallback as valid

**Medium risks**:
- Header file skipping (70% of Phase 33 failures) - out of scope, document limitation
- Template interaction - ensure monomorphization before C++23 transformation

**Low risks**:
- CNodeBuilder insufficient - easy to extend following existing patterns
- Build time impact - incremental, <15% total expected

### Timeline Summary

| Phase | Duration | Features | Tests | Cumulative % |
|-------|----------|----------|-------|--------------|
| 1 | Weeks 1-2 | Multidim subscript | 16 | 3-4% |
| 2 | Weeks 3-4 | Static operators | 8 | 5-6% |
| 3 | Weeks 5-6 | [[assume]] | 13 | 7-8% |
| 4 | Weeks 7-10 | Deducing this | 22 | 10-12% |
| 5 | Weeks 11-13 | if consteval | 13 | 12-14% |
| 6 | Weeks 14-16 | Constexpr + auto(x) | ~20 | **20-25%** |

**Total: 16 weeks (4 months)**

### Success Metrics

**Overall goals**:
- C++23 support: 0% → 20-25%
- Test pass rate: 0/~150 → 30-40/~150
- New test coverage: 100-150 unit tests, 80%+ coverage
- Zero regressions: All existing tests still pass

**Per-phase gates**:
- Functionality: Feature works for documented use cases
- Testing: Unit tests ≥75% coverage, integration tests pass
- Quality: Code review approved, no critical bugs
- Documentation: README/FAQ updated
- Stability: No regressions

## Decisions Needed

### Immediate Decisions
1. **Approve feature prioritization**: Are the 8 selected features correct for initial implementation?
2. **Approve timeline**: Is 16 weeks (4 months) acceptable for 20-25% coverage?
3. **Approve partial support strategy**: Accept runtime fallback for if consteval and constexpr enhancements?

### Phase 4 Decision Point (Week 7)
- If deducing this exceeds complexity estimates:
  - Option A: Reduce to minimal support (auto& and const auto& only)
  - Option B: Extend Phase 4 by 1-2 weeks
  - Option C: Defer complex cases (recursive lambdas, CRTP) to future work

### Phase 5 Decision Point (Week 11)
- If if consteval compile-time evaluation proves infeasible:
  - Option A: Accept runtime-only fallback as valid outcome
  - Option B: Implement macro-based dual-path strategy
  - Option C: De-scope feature entirely (move to future work)

### Header File Skipping (Orthogonal Decision)
- **Current status**: 70% of Phase 33 failures due to header file declarations being skipped by isInMainFile() guard
- **Decision**: Address header translation separately or accept limitation?
  - Option A: Keep main-file-only approach (current design)
  - Option B: Implement header transformation (separate project, high effort)
  - **Recommendation**: Option A - document limitation, focus on language features

## Blockers

**None identified for Phase 1 start**.

Potential blockers for later phases:
- Phase 4: Recursive lambda extraction may require new infrastructure (mitigate: simplified approach or defer)
- Phase 5: Clang constant evaluator API complexity (mitigate: runtime fallback acceptable)
- Phase 6: Constexpr evaluation engine (mitigate: partial support acceptable)

**All blockers have mitigation strategies defined** - no hard blockers preventing progress.

## Next Step

**Begin Phase 1 implementation immediately**: Multidimensional Subscript Operator support

**Concrete actions**:
1. Create feature branch: `feature/phase-1-multidim-subscript`
2. Create files:
   - `include/MultidimSubscriptTranslator.h`
   - `src/MultidimSubscriptTranslator.cpp`
   - `tests/MultidimSubscriptTranslatorTest.cpp`
3. Modify files:
   - `include/CppToCVisitor.h` (add VisitCXXOperatorCallExpr or enhance)
   - `src/CppToCVisitor.cpp` (route multidim subscript calls)
   - `CMakeLists.txt` (add new files)
4. Implement AST pattern detection for `operator[](arg1, arg2, ...)`
5. Transform to C function: `{Class}__subscript_multidim(&obj, idx1, idx2, ...)`
6. Write unit tests for 2D, 3D, const/non-const, lvalue/rvalue cases
7. Run gcc-adapted/multidim-subscript-P2128 tests (target: 14/16 pass)
8. A/B test for correctness
9. Update documentation (README.md, FAQ.md)
10. Code review and merge to develop

**Expected duration**: 2 weeks
**Expected outcome**: +3-4% C++23 support, 16 tests passing, validation of entire workflow

---

## Plan Quality Assessment

**Completeness**:
- 8 features documented with full transformation strategies
- 6 phases with detailed implementation steps
- Testing strategy defined for all levels
- Risk mitigation for all identified risks
- Documentation requirements specified

**Actionability**:
- Implementer can start Phase 1 immediately with no ambiguity
- Each phase has clear success criteria
- File-level changes specified for each phase
- Code examples provided for key transformations

**Realism**:
- Timeline accounts for complexity (2-4 weeks per phase)
- Accepts partial support where full support is infeasible
- Risk mitigation strategies pragmatic (fallbacks, deferrals)
- Builds on proven existing patterns

**Alignment**:
- Targets 20-25% coverage (pipeline research identified 25% gap from missing visitors)
- Incremental phases minimize risk
- No dependencies on header file skipping (70% factor addressed separately)
- Follows SOLID, TDD, KISS principles from project guidelines

This plan is **ready for execution** with high confidence of achieving 20-25% C++23 support in 16 weeks.
