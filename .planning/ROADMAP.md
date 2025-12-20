# Roadmap: Complete Frama-C ACSL Annotation Support

**Project**: Extend ACSL annotation system to full Frama-C compatibility
**Brief**: `.planning/BRIEF.md`
**Created**: 2025-12-20
**Status**: ACTIVE

## Overview

Transform the C++ to C transpiler from basic ACSL support (v1.17.0) to complete Frama-C ACSL 1.17+ compatibility through 7 incremental phases. Each phase delivers working, tested functionality with git-flow releases.

## Phase Strategy

### Execution Approach
- **Incremental delivery**: Each phase produces releasable feature
- **TDD mandatory**: Tests written before implementation
- **Parallel execution**: Use parallel agents for independent subtasks
- **Git-flow releases**: Version bump after each phase completion
- **Integration validation**: Test with Frama-C after each phase

### Quality Gates
- All tests passing (100%)
- All linters passing (zero errors/warnings)
- Frama-C parses generated annotations
- Performance regression <10%
- Code review by separate agent

---

## Phase 1: Statement Annotations (v1.18.0)

**Goal**: Enable assert, assume, and check annotations throughout transpiled code

### Deliverables
- `ACSLStatementAnnotator` class implementation
- Control flow analysis for strategic annotation placement
- Statement annotation test suite (15+ tests)
- CLI flag: `--acsl-statements={none,basic,full}`

### Technical Approach
- **Assert placement**: After pointer dereferences, array accesses, division operations
- **Assume placement**: After validated input, constructor initialization
- **Check placement**: Before complex operations, at function boundaries

### Key Challenges
- Determining optimal assertion placement (avoid annotation spam)
- Balancing completeness vs. proof complexity
- Avoiding redundant assertions with existing function contracts

### Verification Criteria
- Generated assertions provable by Frama-C WP
- No false positives (assertions that fail incorrectly)
- Coverage of common safety properties (null checks, bounds, overflow)

### Dependencies
- None (independent of other phases)

---

## Phase 2: Type Invariants (v1.19.0)

**Goal**: Generate global type invariants for user-defined types

### Deliverables
- `ACSLTypeInvariantGenerator` class implementation
- Type constraint analysis and synthesis
- Type invariant test suite (10+ tests)
- Integration with existing class annotator

### Technical Approach
- Extract type invariants from class invariant predicates
- Promote common constraints to type-level
- Handle inheritance hierarchy (invariant strengthening)
- Support both `type invariant` and `predicate` forms

### Key Challenges
- Distinguishing type-level vs. instance-level invariants
- Handling polymorphic types (templates)
- Avoiding circular dependencies in invariant definitions

### Verification Criteria
- Type invariants automatically checked at type boundaries
- No conflicts with existing class invariants
- Proper scoping (global vs. local invariants)

### Dependencies
- Requires ACSLClassAnnotator (v1.17.0)
- Optional enhancement by Phase 1 assertions

---

## Phase 3: Axiomatic Definitions (v1.20.0)

**Goal**: Generate axiomatic definitions for mathematical properties

### Deliverables
- `ACSLAxiomaticBuilder` class implementation
- Logical function and predicate extraction
- Axiom and lemma generation
- Axiomatic definition test suite (12+ tests)

### Technical Approach
- Identify pure functions suitable for logical abstraction
- Generate `logic` type declarations for mathematical functions
- Create axioms from function properties (commutativity, associativity, etc.)
- Add lemmas for common proof patterns

### Key Challenges
- Determining which functions warrant axiomatic treatment
- Ensuring axiom soundness (no contradictions)
- Balancing abstraction level (too abstract = unprovable)

### Verification Criteria
- Axioms are consistent (no contradictions)
- Lemmas are provable from axioms
- Logical functions match C implementations

### Dependencies
- None (independent of other phases)
- Synergy with Phase 1 (assertions can reference logical functions)

---

## Phase 4: Ghost Code (v1.21.0)

**Goal**: Inject ghost variables and statements for complex specifications

### Deliverables
- `ACSLGhostCodeInjector` class implementation
- Ghost variable analysis and placement
- Ghost statement generation for proof bookkeeping
- Ghost code test suite (10+ tests)

### Technical Approach
- Identify proof-relevant values not in original code
- Insert ghost variables for tracking (e.g., max value seen, sum of elements)
- Generate ghost assignments for maintaining invariants
- Ensure ghost code doesn't affect runtime behavior

### Key Challenges
- Determining when ghost code is necessary vs. nice-to-have
- Maintaining ghost variable consistency across control flow
- Avoiding ghost code explosion (specification larger than code)

### Verification Criteria
- Ghost code compiles with Frama-C (not executable)
- Ghost invariants aid proof automation
- Performance impact negligible (ghost code not compiled)

### Dependencies
- Synergy with Phase 2 (ghost vars can enforce type invariants)
- Synergy with Phase 1 (ghost vars can strengthen assertions)

---

## Phase 5: Function Behaviors (v1.22.0)

**Goal**: Generate named function behaviors for conditional contracts

### Deliverables
- `ACSLBehaviorAnnotator` class implementation
- Behavior extraction from conditional logic
- Completeness and disjointness checking
- Behavior annotation test suite (15+ tests)

### Technical Approach
- Analyze function control flow for distinct behaviors
- Extract behavior-specific preconditions (assumes)
- Generate behavior-specific postconditions (ensures)
- Check completeness (all cases covered) and disjointness (no overlap)

### Key Challenges
- Behavior extraction from complex control flow (nested if/switch)
- Ensuring completeness without manual annotations
- Balancing number of behaviors (too many = complex)

### Verification Criteria
- Behaviors are complete (cover all input cases)
- Behaviors are disjoint (no ambiguous case)
- Each behavior provable independently

### Dependencies
- Enhances ACSLFunctionAnnotator (v1.17.0)
- Synergy with Phase 1 (behaviors can include assertions)

---

## Phase 6: Advanced Memory Predicates (v1.23.0)

**Goal**: Add advanced memory reasoning predicates

### Deliverables
- `ACSLMemoryPredicateAnalyzer` class implementation
- Support for `\allocable`, `\freeable`, `\block_length`, `\base_addr`
- Memory lifecycle tracking (alloc → use → free)
- Memory predicate test suite (10+ tests)

### Technical Approach
- Track memory allocation sites (malloc, new, alloca)
- Generate `\allocable` preconditions for allocators
- Generate `\freeable` preconditions for deallocators
- Add `\block_length` ensures clauses for allocations
- Use `\base_addr` for pointer arithmetic verification

### Key Challenges
- Tracking memory through function calls (inter-procedural)
- Handling custom allocators (pools, arenas)
- Reasoning about partially-allocated structures

### Verification Criteria
- Memory safety properties provable (no double-free, use-after-free)
- Allocation size tracking accurate
- Pointer arithmetic verified within bounds

### Dependencies
- Enhances ACSLFunctionAnnotator (v1.17.0)
- Synergy with Phase 1 (assertions for memory operations)

---

## Phase 7: Integration & Validation (v2.0.0)

**Goal**: Comprehensive Frama-C integration and validation

### Deliverables
- Frama-C WP integration test suite (20+ tests)
- Frama-C EVA integration test suite (15+ tests)
- Performance benchmarking suite
- Complete documentation and examples
- Major version release (v2.0.0)

### Technical Approach
- Create test corpus with diverse C++ patterns
- Run Frama-C WP on transpiled code, measure proof success rate
- Run Frama-C EVA for value analysis validation
- Benchmark transpilation time vs. v1.17.0
- Generate example gallery with verified properties

### Key Challenges
- Achieving high proof success rate (target: ≥80%)
- Managing proof complexity (timeout, memory)
- Documenting failure cases (when Frama-C can't prove)

### Verification Criteria
- ≥80% of generated annotations provable by WP
- 100% of annotations parse without Frama-C errors
- Performance regression ≤10%
- Documentation complete and accurate

### Dependencies
- Requires all previous phases (1-6)
- Final integration and release

---

## Release Plan

| Phase | Version | Annotator | Tests | Release Criteria |
|-------|---------|-----------|-------|------------------|
| 1 | v1.18.0 | ACSLStatementAnnotator | 15+ | Assertions provable, zero false positives |
| 2 | v1.19.0 | ACSLTypeInvariantGenerator | 10+ | Type invariants checked, no conflicts |
| 3 | v1.20.0 | ACSLAxiomaticBuilder | 12+ | Axioms consistent, lemmas provable |
| 4 | v1.21.0 | ACSLGhostCodeInjector | 10+ | Ghost code aids proofs, zero overhead |
| 5 | v1.22.0 | ACSLBehaviorAnnotator | 15+ | Behaviors complete/disjoint, provable |
| 6 | v1.23.0 | ACSLMemoryPredicateAnalyzer | 10+ | Memory safety provable |
| 7 | v2.0.0 | Integration | 35+ | ≥80% proof success, <10% perf impact |

**Total estimated tests**: 117+ new tests (plus existing 37 = 154+ total)

---

## Success Criteria Summary

### Functional Requirements
- ✅ All ACSL 1.17+ statement annotations supported
- ✅ Global type invariants generated
- ✅ Axiomatic definitions for mathematical properties
- ✅ Ghost code for complex specifications
- ✅ Function behaviors for conditional contracts
- ✅ Advanced memory predicates (allocable, freeable, etc.)

### Quality Requirements
- ✅ Test coverage ≥95% across all annotators
- ✅ 100% ACSL parsing success with Frama-C
- ✅ ≥80% proof success rate with Frama-C WP
- ✅ Performance impact ≤10%
- ✅ Zero linting errors
- ✅ Strong typing enforced (100%)

### Documentation Requirements
- ✅ CHANGELOG.md updated for each release
- ✅ README.md feature list complete
- ✅ Website features.astro updated
- ✅ Example gallery with verified code
- ✅ Integration guide for Frama-C users

---

## Risk Mitigation

### Technical Risks
- **ACSL complexity explosion**: Implement verbosity levels (none/basic/medium/full)
- **Performance degradation**: Profile after each phase, optimize hot paths
- **Proof failures**: Tune annotation heuristics based on WP feedback
- **Edge cases**: Comprehensive test suite with corner cases

### Project Risks
- **Scope creep**: Strict adherence to ACSL standard, no custom extensions
- **Testing gaps**: TDD mandatory, 95%+ coverage enforced
- **Integration issues**: Frama-C validation after each phase

---

## Next Steps

1. **Create Phase 1 plan**: `.planning/phases/01-statement-annotations/PLAN.md`
2. **Execute Phase 1**: Implement ACSLStatementAnnotator with TDD
3. **Release v1.18.0**: Git-flow release after Phase 1 completion
4. **Iterate**: Repeat for Phases 2-7

**Ready to begin**: Phase 1 planning and execution
