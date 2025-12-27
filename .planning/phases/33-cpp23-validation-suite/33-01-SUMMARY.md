# Phase 33: C++23 Validation Suite Integration - Summary

## Quick Reference

**Status**: PLANNED
**Priority**: HIGH
**Effort**: 3-5 days
**Dependencies**: Phase 32 (Template AST), Phase 28 (Header Separation)

---

## What This Phase Delivers

### Primary Deliverables
1. **GCC C++23 Test Suite Integration** (~100-130 tests)
   - Adapted from GCC's comprehensive 261-test suite
   - Focus on language features (not library)
   - Organized by C++23 feature category

2. **External Reference Projects**
   - `scivision/Cpp23-examples` (MIT licensed, git submodule)
   - Educational examples and multi-compiler validation

3. **A/B Testing Framework**
   - Automated C++ → C transpilation validation
   - Output comparison (C vs C++)
   - Pass/fail reporting with detailed diffs

4. **Feature Support Documentation**
   - `FEATURE-MATRIX.md` - What works, what doesn't
   - `GAPS.md` - Known limitations
   - `ROADMAP.md` - Future support plans

5. **Baseline Metrics**
   - Current transpiler compliance percentage
   - Feature-by-feature pass rates
   - HTML compliance report card

---

## Why This Matters

### Current Situation
- **Existing tests**: 6 C++23 feature tests in `tests/real-world/cpp23-validation/`
- **Known issues**: README states transpiler outputs C++ code, not C99
- **No validation**: Manual inspection only, no automated A/B testing

### After Phase 33
- **100+ tests**: Comprehensive C++23 coverage
- **Automated validation**: Push-button A/B testing
- **Clear metrics**: Know exactly what % of C++23 works
- **Documented gaps**: No surprises about limitations

---

## Integration Approach

### Hybrid Strategy
```
Primary: GCC g++.dg/cpp23 → Language features (261 tests available)
         ├─ Extract & adapt ~130 most relevant tests
         └─ Strip GCC-specific directives

Reference: scivision/Cpp23-examples → Build system integration
          └─ Git submodule (MIT licensed, 17 items)

Future: MSVC/LLVM STL → Library features (deferred)
        └─ std::expected, std::mdspan, etc.
```

### Directory Structure
```
tests/real-world/cpp23-validation/
├── external-projects/     # NEW: Git submodules
├── gcc-tests/             # NEW: Adapted GCC tests
├── ab-test/               # NEW: Testing framework
├── docs/                  # NEW: Feature docs
├── scripts/               # NEW: Automation
├── cpp/                   # EXISTING: Our tests
└── transpiled/            # EXISTING: C output
```

---

## Key Features Tested

### Language Features (GCC Suite)
| Feature | Tests | Priority |
|---------|-------|----------|
| Deducing this (P0847) | 60 | HIGH |
| if consteval (P1938) | 13 | HIGH |
| Multidimensional subscript (P2128) | 15 | HIGH |
| Static operators (P1169) | 8 | MEDIUM |
| auto(x)/auto{x} (P0849) | 18 | MEDIUM |
| Constexpr enhancements | 19 | MEDIUM |

**Total**: ~130 language feature tests (from 261 available)

### Current Baseline (Expected)
- **Build success rate**: ~45% (C code compiles)
- **Output match rate**: ~10% (C output matches C++)
- **Feature pass rate**: Very low initially (expected)

**Goal**: Establish honest baseline, improve incrementally

---

## Implementation Phases

### 33.1: External Projects Setup (1 day)
- Add scivision/Cpp23-examples git submodule
- Extract GCC g++.dg/cpp23 tests (selective)
- Document licenses and attributions

### 33.2: GCC Test Adaptation (2 days)
- Build Python adaptation script
- Convert ~130 GCC tests to standalone C++
- Create per-feature CMakeLists.txt

### 33.3: A/B Testing Framework (1 day)
- Build test runner (`run-tests.sh`)
- Create output comparison tool
- Generate pass/fail reports

### 33.4: Feature Documentation (0.5 days)
- Write FEATURE-MATRIX.md
- Document known gaps
- Create roadmap

### 33.5: Baseline Metrics (0.5 days)
- Generate JSON metrics
- Create HTML compliance report
- Commit baseline results

---

## Success Metrics

### Must Have ✅
- [ ] 100+ GCC tests integrated
- [ ] A/B framework runs end-to-end
- [ ] Baseline metrics documented
- [ ] Feature matrix complete

### Should Have ⭐
- [ ] scivision/Cpp23-examples integrated
- [ ] Automated test runner scripts
- [ ] HTML compliance report

### Nice to Have 💎
- [ ] CI/CD integration
- [ ] Performance benchmarks
- [ ] Coverage badges

---

## Risk Management

### Key Risks
1. **GCC test complexity** → Start simple, document failures
2. **GPL licensing** → Fair use test extraction, document sources
3. **Low initial pass rate** → Expected, document honestly
4. **Repository bloat** → Selective extraction, not full GCC repo

### Mitigation
- Incremental approach (phase deliverables)
- Clear documentation of limitations
- Realistic expectations (baseline, not perfection)

---

## Dependencies

### Technical
- Git submodules
- Python 3.8+
- CMake 3.20+
- GCC 13+ or Clang 16+ (C++23 support)
- C99 compiler (validation)

### Project
- Existing transpiler
- Phase 32 (Template AST)
- Phase 28 (Header separation)

---

## Next Steps

1. **Review this plan** with stakeholders
2. **Approve Phase 33.1** (External Projects Setup)
3. **Begin implementation** following 5-day timeline
4. **Generate baseline report** after Phase 33.5

---

## References

- **Full Plan**: `33-01-PLAN.md` (this directory)
- **Research**: Agent adbd0a9 findings
- **Existing Tests**: `../../tests/real-world/cpp23-validation/README.md`
- **GCC Suite**: [gcc/testsuite/g++.dg/cpp23](https://github.com/gcc-mirror/gcc/tree/master/gcc/testsuite/g++.dg/cpp23)
- **Reference Project**: [scivision/Cpp23-examples](https://github.com/scivision/Cpp23-examples)

---

**Document Version**: 1.0
**Created**: 2025-12-24
**Status**: ✅ READY FOR IMPLEMENTATION
