# ACSL Integration & Testing Meta-Prompt Summary

**Comprehensive meta-prompt created to integrate all implemented ACSL annotators into the transpiler pipeline and create full integration/validation test suites.**

## Version
Meta-prompt v1 (created 2025-12-21)

## Critical Discovery

**Problem Identified**: All 9 ACSL annotator classes are implemented and tested in isolation (111 unit tests passing), but **ZERO integration** with the main transpiler pipeline.

### What Works ✅
- ✅ 9 ACSL annotator classes fully implemented
- ✅ 111 unit tests passing (100% success rate)
- ✅ CLI flags exist (`--generate-acsl`, `--acsl-level`, `--acsl-output`)
- ✅ Clean, well-designed interfaces following SOLID principles

### What's Broken ❌
- ❌ No annotator instantiation in transpiler code
- ❌ No annotator method calls in visitor/consumer
- ❌ No ACSL output emission
- ❌ Zero end-to-end integration tests
- ❌ Zero Frama-C validation tests
- ❌ **Users cannot actually generate ACSL annotations**

## Meta-Prompt Structure

### 5-Phase Comprehensive Plan

**Phase 1: Pipeline Integration** (CRITICAL - 2-3 days)
- Wire all 9 annotators into `CppToCVisitor`
- Add ACSL output emission in code generation
- Connect CLI flags to annotator configuration
- **Goal**: Make `./cpptoc --generate-acsl` actually work

**Phase 2: Integration Test Suite** (2-3 days)
- Create 10+ end-to-end tests
- Test programs covering all annotator features
- Verify both inline and separate output modes
- Validate CLI flag behavior
- **Goal**: Ensure transpiler pipeline works end-to-end

**Phase 3: Frama-C Validation** (3-4 days)
- 20+ Weakest Precondition (WP) tests
- 15+ Evolved Value Analysis (EVA) tests
- Automated validation scripts
- **Target**: ≥80% WP proof success, ≥50% EVA alarm reduction
- **Goal**: Objective quality metrics for ACSL generation

**Phase 4: Performance & Regression** (1-2 days)
- Benchmark suite (small/medium/large programs)
- Compare baseline (no ACSL) vs. with ACSL
- **Target**: ≤10% performance regression
- **Goal**: Ensure ACSL doesn't degrade transpiler performance

**Phase 5: Documentation & Examples** (1-2 days)
- Update README.md with ACSL features
- Create comprehensive ACSL-GUIDE.md
- 10+ real-world examples (all Frama-C validated)
- **Goal**: Users can learn and use ACSL features

---

## Key Technical Approach

### Integration Pattern

```cpp
// In CppToCVisitor.cpp
class CppToCVisitor : public RecursiveASTVisitor<CppToCVisitor> {
private:
  // Add annotator instances
  std::unique_ptr<ACSLFunctionAnnotator> m_functionAnnotator;
  std::unique_ptr<ACSLLoopAnnotator> m_loopAnnotator;
  // ... all 9 annotators

public:
  // Initialize based on CLI flags
  CppToCVisitor(/* ... */) {
    if (shouldGenerateACSL()) {
      m_functionAnnotator = std::make_unique<ACSLFunctionAnnotator>(/* ... */);
      // ... initialize all annotators
    }
  }

  // Call annotators in Visit methods
  bool VisitFunctionDecl(FunctionDecl *D) {
    // Existing transpilation logic...

    if (shouldGenerateACSL() && m_functionAnnotator) {
      std::string acsl = m_functionAnnotator->generateFunctionContract(D);
      emitACSL(acsl, getACSLOutputMode());
    }

    return true;
  }

  // Similar for loops, classes, statements, etc.
};
```

### Test Infrastructure

**Integration Tests:**
```
tests/integration/
├── test-programs/              # C++ test programs
├── expected-output/            # Expected ACSL annotations
├── integration_test_runner.cpp # Test harness
└── CMakeLists.txt
```

**Frama-C Validation:**
```
tests/framac-validation/
├── wp-tests/                   # 20+ WP tests
├── eva-tests/                  # 15+ EVA tests
├── run-framac-wp.sh           # Automation
└── run-framac-eva.sh          # Automation
```

**Performance Benchmarks:**
```
tests/benchmarks/
├── small/                      # < 100 LOC (20 programs)
├── medium/                     # 100-1000 LOC (10 programs)
├── large/                      # > 1000 LOC (5 programs)
└── benchmark_runner.cpp        # Automated benchmarking
```

---

## Annotators to Integrate

All 9 annotator classes need integration:

1. **ACSLFunctionAnnotator** (15 unit tests) - Function contracts
2. **ACSLLoopAnnotator** (12 unit tests) - Loop invariants
3. **ACSLClassAnnotator** (10 unit tests) - Class invariants
4. **ACSLStatementAnnotator** (18 unit tests) - Assert/assume/check
5. **ACSLTypeInvariantGenerator** (12 unit tests) - Type invariants
6. **ACSLAxiomaticBuilder** (12 unit tests) - Axioms and lemmas
7. **ACSLGhostCodeInjector** (10 unit tests) - Ghost variables
8. **ACSLBehaviorAnnotator** (15 unit tests) - Function behaviors
9. **ACSLGenerator** (7 unit tests) - Base class

**Total: 111 unit tests already passing** ✅

---

## Success Criteria (Comprehensive)

### Integration (Phase 1)
- [x] All 9 annotators wired into pipeline
- [x] CLI flags functional
- [x] ACSL output in both inline and separate modes
- [x] No regressions in existing functionality

### Testing (Phases 2-3)
- [x] 10+ integration tests passing
- [x] 20+ Frama-C WP tests (≥80% proof success)
- [x] 15+ Frama-C EVA tests (≥50% alarm reduction)
- [x] All test infrastructure automated

### Performance (Phase 4)
- [x] Benchmark suite complete
- [x] Performance regression ≤10%
- [x] Memory usage increase ≤10%
- [x] Results documented

### Documentation (Phase 5)
- [x] README.md updated
- [x] ACSL-GUIDE.md created
- [x] 10+ examples (all Frama-C validated)
- [x] All features documented

---

## Dependencies

### External Tools Required
- **Frama-C 27.0+** with WP and EVA plugins
- **Why3 1.7+** (WP backend)
- **Alt-Ergo 2.5+** or **Z3 4.12+** (SMT solvers)
- **GoogleTest** (for integration tests)

### Install Commands
```bash
# macOS
brew install frama-c why3 alt-ergo z3

# Linux (Ubuntu/Debian)
apt-get install frama-c why3 alt-ergo z3

# Verify
frama-c -version
```

---

## Risks & Mitigation

### High-Priority Risks

**Risk 1: Low WP Proof Success Rate**
- Impact: High (affects ACSL quality metric)
- Probability: Medium
- Mitigation: Start simple, tune heuristics, add ghost code aids, document manual hints

**Risk 2: Integration Breaks Existing Features**
- Impact: High (transpiler regression)
- Probability: Low (clean interfaces)
- Mitigation: Run full regression suite after each step, test with/without ACSL flag

**Risk 3: Performance Regression**
- Impact: Medium (user experience)
- Probability: Medium
- Mitigation: Profile hot paths, implement caching, make ACSL generation lazy

**Risk 4: Frama-C Syntax Errors**
- Impact: Medium (validation failure)
- Probability: Low (unit tests validate syntax)
- Mitigation: Test with Frama-C parser early, follow ACSL 1.17+ spec strictly

---

## Timeline Estimate

**Sequential Execution with Verification:**

- **Phase 1** (Pipeline Integration): 2-3 days
- **Phase 2** (Integration Tests): 2-3 days
- **Phase 3** (Frama-C Validation): 3-4 days
- **Phase 4** (Performance Benchmarks): 1-2 days
- **Phase 5** (Documentation): 1-2 days

**Total: 9-14 days**

**Parallelization Opportunities:**
- Phases 2-3 can partially overlap (integration tests while setting up Frama-C)
- Phase 5 can start during Phase 4 (documentation while benchmarks run)

**Optimized Timeline: 7-10 days** (with parallel execution)

---

## Expected Deliverables

### Code Changes
- **Modified**: 5 core transpiler files (visitor, consumer, code generator, main, CMakeLists)
- **Created**: 45+ test files across integration/validation/benchmark suites
- **Created**: 10+ example programs with Frama-C validation

### Test Infrastructure
- Integration test harness with 10+ tests
- Frama-C WP validation suite (20+ tests)
- Frama-C EVA validation suite (15+ tests)
- Performance benchmark suite (35+ programs)
- Automated validation scripts

### Documentation
- README.md updated with ACSL section
- ACSL-GUIDE.md comprehensive guide
- 10+ real-world examples with explanations
- Performance characteristics documented
- Known limitations documented

---

## Impact Assessment

### User-Facing Impact
- **Before**: Users have CLI flags but cannot generate ACSL (broken feature)
- **After**: Users can generate production-quality ACSL annotations validated by Frama-C
- **Value**: Enables formal verification workflows, safety-critical certifications

### Development Impact
- **Code Quality**: Objective metrics via Frama-C validation
- **Testing**: Comprehensive test suite prevents future regressions
- **Documentation**: Users can learn and adopt ACSL features
- **Release**: Enables v2.0.0 major release with complete ACSL support

### Technical Debt Reduction
- **Eliminates**: Disconnected features sitting unused
- **Validates**: 111 unit tests translate to real-world functionality
- **Establishes**: Integration testing infrastructure for future features

---

## Recommendations

### Execution Strategy
1. **Start with Phase 1** - Pipeline integration is critical foundation
2. **Validate early** - Test each annotator integration individually
3. **Automate ruthlessly** - All validation should run via scripts
4. **Measure objectively** - Frama-C proof success is the quality metric
5. **Document thoroughly** - Examples are as important as code

### Priority Order
1. **Phase 1** (CRITICAL) - Without integration, features don't exist
2. **Phase 3** (HIGH) - Frama-C validation provides objective quality proof
3. **Phase 2** (HIGH) - Integration tests prevent regressions
4. **Phase 4** (MEDIUM) - Performance validation ensures usability
5. **Phase 5** (MEDIUM) - Documentation enables adoption

### Quality Gates
- All phases must pass before proceeding to next
- Zero regressions in existing 111 unit tests
- All linters passing throughout
- Each phase deliverables tested independently

---

## Meta-Prompt Location

- **Prompt**: `.prompts/036-acsl-integration-testing/036-acsl-integration-testing.md`
- **Summary**: `.prompts/036-acsl-integration-testing/SUMMARY.md` (this file)

---

## Conclusion

This meta-prompt provides a **complete roadmap** to transform the transpiler from "ACSL features implemented but unusable" to "production-ready ACSL generation with Frama-C validation."

**Key Achievement**: Converts 111 passing unit tests into real-world functionality that users can actually use.

**Success Metric**: ≥80% Frama-C WP proof success rate on generated ACSL annotations.

**Business Value**: Enables formal verification workflows, making the transpiler suitable for safety-critical applications requiring certification.

**Ready to Execute**: All phases detailed with concrete tasks, success criteria, and quality gates.

---

**Created**: 2025-12-21
**Status**: Ready for execution
**Estimated Duration**: 9-14 days (7-10 days with parallelization)
**Prerequisites**: Frama-C toolchain installation
**Risk Level**: Low (clean interfaces, incremental approach, comprehensive testing)
