# Phase 7 Plan: Integration & Validation (v2.0.0)

**Phase**: 7 of 7
**Roadmap**: `.planning/ROADMAP.md`
**Brief**: `.planning/BRIEF.md`
**Target Version**: v2.0.0 (MAJOR RELEASE)
**Status**: PENDING
**Prerequisite**: Phases 1-6 complete

## Phase Goal

Comprehensive Frama-C integration testing, validation, performance benchmarking, and documentation. Achieve production-ready status for complete ACSL annotation support.

## Deliverables

### Integration Tests
- [ ] `tests/integration/FramaCWPTests.cpp` (20+ tests)
- [ ] `tests/integration/FramaCEVATests.cpp` (15+ tests)
- [ ] End-to-end test corpus with diverse C++ patterns

### Performance Benchmarks
- [ ] Benchmark suite comparing v1.17.0 vs. v2.0.0
- [ ] Memory usage profiling
- [ ] Transpilation time analysis
- [ ] Annotation generation time breakdown

### Documentation
- [ ] Complete CHANGELOG.md for v2.0.0
- [ ] Comprehensive README.md update
- [ ] Website features.astro complete rewrite
- [ ] Example gallery with verified properties
- [ ] Frama-C integration guide
- [ ] Troubleshooting guide for proof failures

### Release
- [ ] Git-flow release v2.0.0 (major version)
- [ ] Release notes with upgrade guide
- [ ] Migration guide from v1.x to v2.0

## Technical Design

### Integration Test Strategy

#### Frama-C WP Tests (20+ tests)
Test that generated annotations are provable:

1. **SimpleFunction_WP** - Basic function contracts provable
2. **PointerFunction_WP** - Pointer validity provable
3. **ArrayFunction_WP** - Array bounds provable
4. **LoopFunction_WP** - Loop invariants provable
5. **RecursiveFunction_WP** - Recursive functions provable
6. **ClassMethods_WP** - Class invariants maintained
7. **MemoryAllocation_WP** - Memory safety provable
8. **PointerArithmetic_WP** - Arithmetic safety provable
9. **BufferOperations_WP** - Buffer overflow prevention
10. **TypeInvariants_WP** - Type constraints checked
11. **GhostCode_WP** - Ghost vars aid proof
12. **Behaviors_WP** - Behaviors provable independently
13. **Axiomatics_WP** - Lemmas provable from axioms
14. **ComplexAlgorithm_WP** - Multi-phase algorithm
15. **ErrorHandling_WP** - Error paths verified
16. **ResourceManagement_WP** - RAII pattern verified
17. **TemplateCode_WP** - Monomorphized templates
18. **InheritanceHierarchy_WP** - Virtual functions
19. **OperatorOverloading_WP** - Operators verified
20. **STLContainers_WP** - Container operations

#### Frama-C EVA Tests (15+ tests)
Test value analysis with annotations:

1. **ConstantPropagation_EVA** - EVA benefits from annotations
2. **RangeAnalysis_EVA** - Tighter ranges with contracts
3. **PointerAnalysis_EVA** - Separation aids analysis
4. **BufferAnalysis_EVA** - No buffer overflows detected
5. **DivisionByZero_EVA** - No division by zero
6. **NullPointer_EVA** - No null dereferences
7. **UninitializedMemory_EVA** - All memory initialized
8. **MemoryLeak_EVA** - No leaks detected
9. **ArithmeticOverflow_EVA** - No overflows
10. **SignedUnsignedMix_EVA** - Type mixing safe
11. **CastSafety_EVA** - All casts safe
12. **ArrayBounds_EVA** - All accesses in bounds
13. **FunctionPointers_EVA** - Indirect calls safe
14. **GlobalState_EVA** - Global invariants maintained
15. **ConcurrencyUnsafe_EVA** - Data races detected

### Performance Benchmarking

#### Benchmark Corpus
- Small programs (< 100 LOC): 20 samples
- Medium programs (100-1000 LOC): 10 samples
- Large programs (> 1000 LOC): 5 samples

#### Metrics Collected
- **Transpilation time**: Total time including all annotations
- **Annotation time**: Time spent generating ACSL only
- **Memory usage**: Peak RSS during transpilation
- **Annotation size**: Lines of ACSL vs. lines of C
- **Proof time**: Time for Frama-C WP to verify

#### Target Thresholds
- Transpilation time increase: ≤10% vs. v1.17.0
- Memory usage increase: ≤10% vs. v1.17.0
- Proof success rate: ≥80% with WP
- Annotation overhead: ≤30% additional lines

### Documentation Updates

#### CHANGELOG.md
Complete entry for v2.0.0:
- Summary of all 7 phases
- Breaking changes (if any)
- Migration guide from v1.x
- Performance improvements
- Known limitations
- Future roadmap

#### README.md
- Updated feature list with all ACSL capabilities
- Installation instructions (if changed)
- Quick start guide with v2.0 examples
- Link to Frama-C integration guide
- Performance characteristics

#### Website (features.astro)
Comprehensive rewrite:
- Overview of formal verification with Frama-C
- Detailed feature list with examples
- Interactive examples (if possible)
- Proof success statistics
- Comparison with manual annotation
- Integration workflow diagram

#### Example Gallery
10+ examples with Frama-C verification:
1. Bubble sort with sortedness proof
2. Binary search with correctness proof
3. Linked list with memory safety proof
4. Buffer operations with overflow prevention
5. RAII resource management
6. Factory pattern with type safety
7. Observer pattern with invariants
8. Template instantiation with monomorphization
9. Virtual dispatch with correctness
10. STL vector usage with safety

#### Integration Guide
Step-by-step Frama-C integration:
1. Install Frama-C and dependencies
2. Transpile C++ to C with ACSL annotations
3. Run Frama-C WP for verification
4. Interpret proof results
5. Handle proof failures (debugging)
6. Optimize annotation verbosity
7. Integrate into CI/CD pipeline

### Validation Process

#### Pre-Release Checklist
- [ ] All 117+ tests passing (Phases 1-6 + integration)
- [ ] Zero linting errors across all new code
- [ ] Frama-C 27.0+ compatibility verified
- [ ] Performance benchmarks meet targets
- [ ] Documentation complete and accurate
- [ ] Example gallery verified with Frama-C
- [ ] Migration guide tested with v1.17.0 projects

#### Quality Gates
- [ ] Test coverage ≥95% across all annotators
- [ ] Frama-C parsing: 100% success rate
- [ ] WP proof success: ≥80% on test corpus
- [ ] Performance: ≤10% regression
- [ ] Memory: ≤10% increase
- [ ] Code review: Passed by independent agent

#### Release Criteria
- [ ] All quality gates passed
- [ ] Documentation peer-reviewed
- [ ] Examples independently verified
- [ ] Known issues documented
- [ ] Upgrade path tested
- [ ] Backward compatibility verified (v1.17.0 behavior preserved)

## Test Plan

### Integration Test Execution
1. Generate test corpus (35+ C++ programs)
2. Transpile with v2.0.0 (all ACSL features enabled)
3. Run Frama-C WP on all programs
4. Collect proof results (success/failure/timeout)
5. Run Frama-C EVA on all programs
6. Collect analysis results (alarms/no alarms)
7. Analyze failures and refine annotations

### Performance Benchmarking
1. Select representative programs (35 total)
2. Transpile with v1.17.0 (baseline)
3. Transpile with v2.0.0 (all features)
4. Compare metrics (time, memory, size)
5. Identify performance bottlenecks
6. Optimize if targets not met
7. Re-benchmark after optimization

### Documentation Validation
1. Peer review all documentation
2. Test all code examples
3. Verify all Frama-C commands
4. Check all links and references
5. Spell check and grammar check
6. Ensure consistent terminology
7. Validate upgrade procedures

## Implementation Strategy

### Step 1: Integration Tests
1. Create test corpus (35+ programs)
2. Implement WP test harness
3. Implement EVA test harness
4. Run tests and collect results
5. Refine annotations based on failures
6. Achieve ≥80% proof success rate

### Step 2: Performance Benchmarking
1. Implement benchmark harness
2. Run baseline (v1.17.0) benchmarks
3. Run v2.0.0 benchmarks
4. Analyze results
5. Optimize if needed
6. Document performance characteristics

### Step 3: Documentation
1. Write CHANGELOG.md v2.0.0 entry
2. Update README.md
3. Rewrite website features.astro
4. Create example gallery
5. Write Frama-C integration guide
6. Write troubleshooting guide
7. Write migration guide

### Step 4: Validation
1. Execute pre-release checklist
2. Independent code review
3. Documentation peer review
4. Example verification
5. Final testing pass
6. Fix any issues found

### Step 5: Release
1. Git-flow release v2.0.0
2. Create GitHub release with notes
3. Update website (deploy)
4. Announce release
5. Monitor for issues

## Success Metrics

### Quantitative
- **Tests**: 154+ total (37 v1.17.0 + 82 Phases 1-6 + 35 integration)
- **Test pass rate**: 100%
- **WP proof success**: ≥80%
- **EVA alarm reduction**: ≥50% fewer alarms vs. no annotations
- **Performance**: ≤10% regression
- **Memory**: ≤10% increase

### Qualitative
- Annotations are human-readable and understandable
- Frama-C integration is seamless and well-documented
- Examples are compelling and demonstrate value
- Documentation is comprehensive and accurate
- Migration from v1.x is straightforward

## Dependencies

### External Dependencies
- Frama-C 27.0+ with WP and EVA plugins
- Why3 1.7+ (WP backend)
- Alt-Ergo 2.5+ or Z3 4.12+ (SMT solvers)

### Internal Dependencies
- All Phases 1-6 complete and tested
- v1.17.0 baseline for comparison

## Risks and Mitigation

### Risk 1: Low Proof Success Rate (High Impact, Medium Probability)
**Mitigation**:
- Tune annotation heuristics based on WP feedback
- Add more specific preconditions/postconditions
- Use ghost code to aid proof automation
- Document cases where manual hints needed
- Provide troubleshooting guide

### Risk 2: Performance Regression (Medium Impact, Medium Probability)
**Mitigation**:
- Profile and optimize hot paths
- Implement verbosity levels to reduce overhead
- Cache analysis results where possible
- Consider parallel annotation generation
- Target basic level for <5% impact

### Risk 3: Documentation Gaps (Medium Impact, Low Probability)
**Mitigation**:
- Peer review all documentation
- Test all examples independently
- User testing with migration guide
- Comprehensive troubleshooting section

### Risk 4: Breaking Changes (High Impact, Low Probability)
**Mitigation**:
- Preserve v1.17.0 behavior by default
- New features opt-in via CLI flags
- Extensive backward compatibility testing
- Clear migration guide

## Next Steps

1. **After Phase 6 completes**: Begin integration test development
2. **Parallel with Phase 6**: Prepare test corpus
3. **After integration tests pass**: Performance benchmarking
4. **After benchmarks**: Documentation sprint
5. **After documentation**: Validation and release

**Ready to execute**: After Phases 1-6 complete

## Major Release Notes (v2.0.0)

### Headline Features
- **Complete ACSL Support**: All Frama-C ACSL 1.17+ features
- **6 New Annotators**: Statement, TypeInvariant, Axiomatic, Ghost, Behavior, Memory
- **117+ New Tests**: Comprehensive test coverage
- **Frama-C Validated**: ≥80% proof success with WP
- **Production Ready**: Extensive testing and validation

### Upgrade Benefits
- Automatic verification of runtime safety properties
- Formal proofs of correctness for transpiled code
- Integration with Frama-C toolchain
- Reduced manual annotation effort
- Safety-critical system certification support

### Breaking Changes (if any)
- TBD based on Phases 1-6 implementation

### Migration Path
- Default behavior preserves v1.17.0 (all new features opt-in)
- See migration guide for enabling v2.0 features
- Gradual adoption recommended (enable features incrementally)
