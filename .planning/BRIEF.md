# Project Brief: Complete Frama-C ACSL Annotation Support

## Executive Summary

Extend the C++ to C transpiler's ACSL annotation capabilities to support the complete set of annotations recognized by Frama-C's verification tools (WP, EVA, etc.). Current implementation (v1.17.0) provides foundational annotations for functions, loops, and classes. This project adds advanced ACSL features to enable comprehensive formal verification of transpiled code.

## Background

### Current State (v1.17.0)
- ✅ **ACSLFunctionAnnotator**: Preconditions, postconditions, assigns clauses
- ✅ **ACSLLoopAnnotator**: Loop invariants, variants, assigns
- ✅ **ACSLClassAnnotator**: Class invariant predicates
- ✅ Test coverage: 37/37 tests (100%)

### Supported ACSL Features
- Pointer validity: `\valid`, `\valid_read`, `\fresh`
- Quantifiers: `\forall`, `\exists`
- Temporal: `\old()`, `\at()`
- Memory: `\separated()`, `\nothing`
- Termination: loop variants

### Gap Analysis
Missing ACSL features required for full Frama-C compatibility:

1. **Statement Annotations**
   - `//@ assert expr;` - Runtime assertions
   - `//@ assume expr;` - Assumptions for proof context
   - `//@ check expr;` - Proof obligations without runtime check

2. **Type Invariants**
   - Global type invariants (`type invariant name(type t) = property;`)
   - Applied automatically to all instances of a type

3. **Axiomatic Definitions**
   - Logical functions and predicates
   - Mathematical axioms for proof reasoning
   - Lemmas with proof hints

4. **Ghost Code**
   - `//@ ghost type var;` - Variables for specification only
   - Ghost statements for proof bookkeeping
   - Not compiled into executable code

5. **Function Behaviors**
   - Named contract variants
   - Complete vs. disjoint behaviors
   - Behavior selection based on preconditions

6. **Advanced Memory Predicates**
   - `\allocable()` - Memory can be allocated
   - `\freeable()` - Memory can be freed
   - `\block_length()` - Size of allocated block
   - `\base_addr()` - Base address of pointer

7. **Logic Type System**
   - `logic` type declarations
   - Polymorphic logic functions
   - Inductive predicates

## Objectives

### Primary Goals
1. Implement all ACSL statement annotations (assert, assume, check)
2. Add global type invariant generation
3. Support axiomatic definitions for mathematical properties
4. Enable ghost code generation for complex specifications
5. Implement function behaviors for conditional contracts

### Success Criteria
- All Frama-C ACSL 1.17+ features supported
- Test coverage ≥95% for new annotators
- Integration tests with Frama-C WP and EVA plugins
- Documentation with examples for each feature
- Performance impact <10% on transpilation time

### Non-Goals
- Custom ACSL extensions beyond Frama-C standard
- Interactive theorem proving (user provides hints manually)
- Automatic proof generation (leave to Frama-C solvers)

## Scope

### In Scope
- **Statement Annotator**: Insert assert/assume/check at strategic points
- **Type Invariant Generator**: Extract type invariants from class constraints
- **Axiomatic Definition Builder**: Create logical functions and axioms
- **Ghost Code Injector**: Add ghost variables and statements
- **Behavior Annotator**: Generate function behavior contracts
- **Memory Predicate Analyzer**: Advanced memory reasoning
- **CLI Integration**: Flags for controlling new annotation features
- **Frama-C Validation**: Test suite with Frama-C WP/EVA

### Out of Scope
- Proof script generation (let Frama-C handle this)
- Custom SMT solver integration
- Interactive proof refinement
- Non-ACSL specification languages (JML, Dafny, etc.)
- Runtime assertion checking (separate concern)

## Constraints

### Technical Constraints
- Must use Clang LibTooling infrastructure
- Must maintain AST traversal performance
- ACSL output must parse with Frama-C 27.0+
- Backward compatible with existing v1.17.0 annotations

### Resource Constraints
- Single developer (solo project)
- Must follow TDD (test-first development)
- Must use git-flow for releases
- All tests must pass before commits

### Quality Constraints
- SOLID principles mandatory
- Type safety enforced (strong typing)
- Linting required before all commits
- Integration tests with actual Frama-C tools

## Dependencies

### External Dependencies
- **Frama-C 27.0+**: Validation of generated annotations
- **Why3**: Backend prover for WP plugin
- **Alt-Ergo/Z3/CVC4**: SMT solvers for proof obligations

### Internal Dependencies
- Existing ACSLFunctionAnnotator (v1.17.0)
- Existing ACSLLoopAnnotator (v1.17.0)
- Existing ACSLClassAnnotator (v1.17.0)
- Clang/LLVM 15+ infrastructure
- Test framework (Google Test)

## Risks

### Technical Risks
| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| ACSL complexity explosion | High | Medium | Implement verbosity levels (basic/medium/full) |
| Performance degradation | Medium | Medium | Profile and optimize hot paths |
| Frama-C version incompatibility | High | Low | Test against multiple Frama-C versions |
| AST traversal edge cases | Medium | High | Comprehensive test suite with corner cases |

### Project Risks
| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| Scope creep | Medium | Medium | Strict adherence to ACSL standard only |
| Incomplete testing | High | Low | TDD mandatory, 95%+ coverage required |
| Integration complexity | Medium | Medium | Incremental rollout, feature flags |

## Timeline Estimates

**Note**: Per project guidelines, no time estimates provided. Work breakdown into phases:

### Phase 1: Statement Annotations
- Statement annotator foundation
- Assert/assume/check generation
- Control flow analysis integration
- Test suite (15+ tests)

### Phase 2: Type Invariants
- Global type invariant generator
- Type system integration
- Invariant synthesis from constraints
- Test suite (10+ tests)

### Phase 3: Axiomatic Definitions
- Axiomatic definition builder
- Logical function extraction
- Axiom and lemma generation
- Test suite (12+ tests)

### Phase 4: Ghost Code
- Ghost variable analyzer
- Ghost statement injector
- Proof bookkeeping automation
- Test suite (10+ tests)

### Phase 5: Function Behaviors
- Behavior contract generator
- Precondition-based behavior selection
- Completeness/disjointness checking
- Test suite (15+ tests)

### Phase 6: Advanced Memory Predicates
- Memory predicate analyzer
- Allocation/deallocation tracking
- Block size and base address reasoning
- Test suite (10+ tests)

### Phase 7: Integration & Validation
- Frama-C WP integration tests
- Frama-C EVA integration tests
- Performance benchmarking
- Documentation and examples

## Success Metrics

### Quantitative Metrics
- **Test Coverage**: ≥95% for all new annotators
- **Frama-C Compatibility**: 100% of generated ACSL parses without errors
- **Proof Success Rate**: ≥80% of generated annotations provable by WP
- **Performance**: Transpilation time increase ≤10%
- **Code Quality**: Zero linting errors, strong typing 100%

### Qualitative Metrics
- Generated annotations are human-readable
- Annotations aid in understanding code behavior
- Integration with Frama-C is seamless
- Documentation is comprehensive and clear

## Stakeholders

- **Primary User**: Solo developer (alexanderfedin)
- **End Users**: Developers using C++ to C transpiler for safety-critical systems
- **Validators**: Frama-C verification community
- **Beneficiaries**: Safety-critical software engineers (aerospace, automotive, medical)

## Deliverables

1. **Source Code**
   - ACSLStatementAnnotator class
   - ACSLTypeInvariantGenerator class
   - ACSLAxiomaticBuilder class
   - ACSLGhostCodeInjector class
   - ACSLBehaviorAnnotator class
   - ACSLMemoryPredicateAnalyzer class

2. **Tests**
   - Unit tests for each annotator (≥10 tests per annotator)
   - Integration tests with Frama-C
   - Performance benchmarks

3. **Documentation**
   - CHANGELOG.md updates
   - README.md feature updates
   - Website features.astro updates
   - Example gallery with verified code

4. **Build Artifacts**
   - Git-flow releases (v1.18.0, v1.19.0, etc.)
   - Tagged releases on GitHub
   - Updated CI/CD workflows

## References

- **ACSL 1.17 Specification**: https://frama-c.com/download/acsl.pdf
- **Frama-C Manual**: https://frama-c.com/download/frama-c-user-manual.pdf
- **Clang LibTooling**: https://clang.llvm.org/docs/LibTooling.html
- **Existing Implementation**: `src/ACSL*Annotator.{cpp,h}` (v1.17.0)
- **Project Roadmap**: EPICS.md (Epic #15: Frama-C Compatibility, Weeks 39-42)

## Approval

**Created**: 2025-12-20
**Status**: DRAFT
**Next Step**: Create detailed ROADMAP.md with phase breakdown
