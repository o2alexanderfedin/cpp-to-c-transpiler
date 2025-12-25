# Roadmap: Complete ACSL Support + Core C++ Feature Implementation

**Project**: Extend ACSL annotation system AND implement critical C++ language features
**Brief**: `.planning/BRIEF.md`
**Created**: 2025-12-20
**Updated**: 2025-12-24 (added Workstream E: C++23 Transpiler Fixes, Phases 32-40)
**Status**: ACTIVE

## Overview

Five parallel workstreams to transform the transpiler:

**Workstream A: ACSL Annotation Completion (v1.17.0 → v2.0.0)**
- Phases 1-7: Complete Frama-C ACSL 1.17+ compatibility
- Status: Phases 1-5 ✅ COMPLETE | Phase 6-7 ⏳ PLANNED

**Workstream B: Core C++ Feature Implementation (v2.1.0 → v3.0.0)**
- Phases 8-17: Implement 25 unsupported C++ features identified in analysis
- Status: All phases ⏳ PLANNED | Can run in parallel with ACSL work

**Workstream C: Validation & Utilities**
- Phase 30: Transpile real-world test projects for validation
- Phase 33: C++23 validation suite integration
- Status: Phase 30 ⏳ IN PROGRESS | Phase 33 ✅ COMPLETE

**Workstream D: Architecture Enhancements**
- Phase 31: COM-style vtable architecture
- Phase 32: Transpiler architecture fix (C++ AST routing)
- Status: Phase 31 ✅ COMPLETE | Phase 32 ✅ COMPLETE

**Workstream E: C++23 Transpiler Fixes (v2.5.0 → v3.0.0)**
- Phases 34-40: Fix critical gaps blocking production C++23 support
- Status: All phases ⏳ PLANNED | **CRITICAL PRIORITY**

## Phase Strategy

### Execution Approach
- **Parallel workstreams**: ACSL (6-7) can run alongside C++ features (8-16)
- **Incremental delivery**: Each phase produces releasable feature
- **TDD mandatory**: Tests written before implementation
- **Parallel execution**: Use parallel agents for independent subtasks
- **Git-flow releases**: Version bump after each phase completion
- **Integration validation**: Test with Frama-C (ACSL) and real C++ programs (features)

### Quality Gates
- All tests passing (100%)
- All linters passing (zero errors/warnings)
- Frama-C parses generated annotations (ACSL phases)
- Real C++ programs transpile correctly (feature phases)
- Performance regression <10%
- Code review by separate agent

---

# WORKSTREAM A: ACSL ANNOTATION COMPLETION

## Phase 1: Statement Annotations (v1.18.0) ✅ COMPLETE

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

## Phase 2: Type Invariants (v1.19.0) ✅ COMPLETE

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

## Phase 3: Axiomatic Definitions (v1.20.0) ✅ COMPLETE

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

## Phase 4: Ghost Code (v1.21.0) ✅ COMPLETE

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

## Phase 5: Function Behaviors (v1.22.0) ✅ COMPLETE

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

## Phase 6: Advanced Memory Predicates (v1.23.0) ⏳ PLANNED

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

**Parallel Execution**: Can run alongside Phases 8, 9, 11, 12, 13 (no dependencies)

---

## Phase 7: ACSL Integration & Validation (v2.0.0 - MAJOR) ⏳ PLANNED

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
- Requires all previous ACSL phases (1-6)
- Final ACSL integration and release

**Parallel Execution**: Can run alongside Phases 8-16 (separate workstream)

---

# WORKSTREAM B: CORE C++ FEATURE IMPLEMENTATION

**Motivation**: Analysis of UNSUPPORTED_FEATURES.md revealed 25 critical C++ features missing or not integrated. These phases address the gaps systematically.

**Priority Tiers**:
- **TIER 1 (Critical)**: Blocking basic usage - standalone functions, lambdas, virtual methods
- **TIER 2 (High-Value)**: Infrastructure exists, needs integration - templates, exceptions, RTTI
- **TIER 3 (Important)**: Medium priority - operators, static members, enums
- **TIER 4 (Integration)**: Validate all features work together

---

## Phase 8: Standalone Function Translation (v2.1.0) ⏳ PLANNED

**Goal**: Enable translation of standalone functions (non-member functions)

**Status**: CRITICAL - Currently only class methods are translated

### Deliverables
- `VisitFunctionDecl` implementation for code generation (currently only RAII analysis)
- Function naming and signature translation
- Function call translation
- Standalone function test suite (12+ tests)
- CLI flag integration

### Technical Approach
- Extend existing `VisitFunctionDecl` (line 463 in CppToCVisitor.cpp)
- Generate C function declarations and definitions
- Handle function overloading (name mangling)
- Translate function calls (direct, pointer, reference)
- Support `main()` function translation

### Key Challenges
- Distinguishing class methods from free functions (already handled)
- Function overloading requires name mangling (infrastructure exists in NameMangler.cpp)
- Global function initialization order (static initialization fiasco)

### Verification Criteria
- `main()` function translates correctly
- Free functions with same name (overloading) translate uniquely
- Function calls resolve correctly
- Linkage preserved (static, extern, inline)

### Dependencies
- None (independent)
- Infrastructure: NameMangler.cpp exists

**Parallel Execution**: ✅ Can run with Phases 6, 7, 9, 11, 12, 13

---

## Phase 9: Virtual Method Support (v2.2.0) ⏳ PLANNED

**Goal**: Integrate virtual method translation (infrastructure exists but skipped)

**Status**: CRITICAL - Virtual methods explicitly skipped (CppToCVisitor.cpp:68-72)

### Deliverables
- Remove virtual method skip (line 68-72)
- Integrate VtableGenerator and VirtualMethodAnalyzer
- Virtual method call translation (indirect through vtable)
- Virtual method test suite (15+ tests)

### Technical Approach
- Remove skip condition: `if (MD->isVirtual()) { return true; }`
- Use existing VtableGenerator.cpp to emit vtables
- Use existing VirtualMethodAnalyzer.h for method resolution
- Generate vtable initialization in constructors
- Translate virtual calls to vtable lookups

### Key Challenges
- Vtable layout for inheritance hierarchies
- Virtual destructor chaining
- Covariant return types
- Pure virtual functions (abstract classes)

### Verification Criteria
- Virtual method calls dispatch correctly at runtime
- Inheritance hierarchies have correct vtable layout
- Virtual destructors call chain correctly
- Pure virtual functions prevent instantiation

### Dependencies
- None (independent)
- Infrastructure: VtableGenerator.cpp, VirtualMethodAnalyzer.h exist

**Parallel Execution**: ✅ Can run with Phases 6, 7, 8, 11, 12, 13

---

## Phase 10: Lambda Expression Translation (v2.3.0) ⏳ PLANNED

**Goal**: Translate C++ lambda expressions to C function pointers + closure structs

**Status**: CRITICAL - No visitor method exists (VisitLambdaExpr missing)

### Deliverables
- `VisitLambdaExpr` implementation
- Capture analysis (by value, by reference, implicit)
- Closure struct generation
- Function pointer generation for lambda body
- Lambda test suite (18+ tests)

### Technical Approach
- Add `VisitLambdaExpr(LambdaExpr *E)` visitor method
- Analyze capture list (variables captured from enclosing scope)
- Generate closure struct with captured variables
- Generate C function taking closure struct as parameter
- Translate lambda calls to function pointer invocations

### Key Challenges
- Capture semantics (value vs. reference vs. move)
- Generic lambdas (template instantiation)
- Lambda lifetime management (dangling references)
- Mutable lambdas (const correctness)

### Verification Criteria
- Captured variables accessible in lambda body
- Lambda calls execute correctly
- Closure lifetime managed correctly
- Generic lambdas instantiate for all used types

### Dependencies
- **Requires Phase 8** (standalone function generation)
- Lambda body becomes standalone C function

**Parallel Execution**: ❌ Sequential after Phase 8

---

## Phase 11: Template Integration (v2.4.0) ⏳ PLANNED

**Goal**: Integrate template monomorphization (infrastructure exists)

**Status**: HIGH-VALUE - TemplateMonomorphizer.cpp and TemplateExtractor.cpp exist but not called

### Deliverables
- Integrate TemplateMonomorphizer into CppToCVisitor
- Template instantiation tracking
- Monomorphized code generation
- Template integration test suite (12+ tests)

### Technical Approach
- Call TemplateMonomorphizer::monomorphize() in visitor
- Use TemplateExtractor to find all template instantiations
- Generate C code for each concrete instantiation
- Handle template specializations

### Key Challenges
- Finding all instantiations (explicit + implicit)
- Handling partial specializations
- Template friend functions
- Dependent names resolution

### Verification Criteria
- Template classes instantiate correctly
- Template functions generate for each type used
- Specializations override primary template
- All instantiations link correctly

### Dependencies
- None (infrastructure complete)
- Infrastructure: TemplateMonomorphizer.cpp, TemplateExtractor.cpp

**Parallel Execution**: ✅ Can run with Phases 6, 7, 8, 9, 12, 13

---

## Phase 12: Exception Handling Integration (v2.5.0) ⏳ PLANNED

**Goal**: Integrate exception translation (infrastructure exists)

**Status**: HIGH-VALUE - TryCatchTransformer.cpp, ThrowTranslator.cpp, exception_runtime.cpp exist

### Deliverables
- `VisitCXXTryStmt` implementation
- `VisitCXXThrowExpr` implementation
- Integrate TryCatchTransformer and ThrowTranslator
- Exception runtime linking
- Exception handling test suite (15+ tests)

### Technical Approach
- Add `VisitCXXTryStmt(CXXTryStmt *S)` visitor method
- Add `VisitCXXThrowExpr(CXXThrowExpr *E)` visitor method
- Call TryCatchTransformer::transform() for try-catch blocks
- Call ThrowTranslator::translate() for throw expressions
- Link exception_runtime.cpp into final executable

### Key Challenges
- Stack unwinding simulation in C (setjmp/longjmp)
- Exception type matching (catch handlers)
- Resource cleanup during unwinding (RAII integration)
- Nested try-catch blocks

### Verification Criteria
- Thrown exceptions caught by matching handlers
- Stack unwinding calls destructors correctly
- Uncaught exceptions propagate to outer scopes
- Performance impact acceptable (<20% overhead)

### Dependencies
- None (infrastructure complete)
- Infrastructure: TryCatchTransformer.cpp, ThrowTranslator.cpp, exception_runtime.cpp

**Parallel Execution**: ✅ Can run with Phases 6, 7, 8, 9, 11, 13

---

## Phase 13: RTTI Integration (v2.6.0) ⏳ PLANNED

**Goal**: Integrate RTTI translation (infrastructure exists)

**Status**: HIGH-VALUE - TypeidTranslator.cpp, DynamicCastTranslator.cpp, rtti_runtime.c exist

### Deliverables
- `VisitCXXTypeidExpr` implementation
- `VisitCXXDynamicCastExpr` implementation
- Integrate TypeidTranslator and DynamicCastTranslator
- RTTI runtime linking
- RTTI test suite (10+ tests)

### Technical Approach
- Add `VisitCXXTypeidExpr(CXXTypeidExpr *E)` visitor method
- Add `VisitCXXDynamicCastExpr(CXXDynamicCastExpr *E)` visitor method
- Call TypeidTranslator::translate() for typeid expressions
- Call DynamicCastTranslator::translate() for dynamic_cast expressions
- Link rtti_runtime.c into final executable

### Key Challenges
- Type information generation (type_info structs)
- Inheritance hierarchy representation for dynamic_cast
- RTTI overhead (data size, runtime cost)
- Integration with virtual methods (Phase 9)

### Verification Criteria
- typeid() returns correct type information
- dynamic_cast succeeds/fails correctly based on runtime type
- Polymorphic types support RTTI
- Non-polymorphic types handled (compile-time errors preserved)

### Dependencies
- **Synergy with Phase 9** (virtual methods enable RTTI)
- Infrastructure: TypeidTranslator.cpp, DynamicCastTranslator.cpp, rtti_runtime.c

**Parallel Execution**: ✅ Can run with Phases 6, 7, 8, 9, 11, 12

---

## Phase 14: Operator Overloading (v2.7.0) ⏳ PLANNED

**Goal**: Translate operator overloading to C function calls

**Status**: IMPORTANT - No visitor methods for operator expressions

### Deliverables
- `VisitCXXOperatorCallExpr` implementation
- Operator function name mangling
- Member vs. non-member operator handling
- Operator overloading test suite (15+ tests)

### Technical Approach
- Add `VisitCXXOperatorCallExpr(CXXOperatorCallExpr *E)` visitor method
- Generate C function names for operators (e.g., `operator+` → `ClassName_op_add`)
- Handle member operators (implicit `this` parameter)
- Handle non-member operators (friend operators)
- Translate operator calls to function calls

### Key Challenges
- Operator precedence preservation
- Assignment operator chaining
- Conversion operators (implicit/explicit)
- Increment/decrement operators (pre vs. post)

### Verification Criteria
- All standard operators translate correctly (+, -, *, /, ==, <, etc.)
- Operator chaining works (a + b + c)
- Assignment operators return correct values
- Stream operators (<<, >>) work for I/O

### Dependencies
- None (independent)
- Infrastructure: NameMangler.cpp handles operator name mangling

**Parallel Execution**: ✅ Can run with other phases

---

## Phase 15: Static Members & Assignment Operators (v2.8.0) ⏳ PLANNED

**Goal**: Complete static member support and finish assignment operator translation

**Status**: IMPORTANT - Static members not handled, assignment operators partially implemented

### Deliverables
- Static member variable translation (global C variables)
- Static member function translation
- Copy assignment operator completion (CppToCVisitor.cpp:95-101 TODO)
- Move assignment operator storage fix (CppToCVisitor.cpp:84-93 TODO)
- Static + assignment test suite (12+ tests)

### Technical Approach
- **Static Members**: Generate global C variables with mangled names
- **Static Initialization**: Use __attribute__((constructor)) or init functions
- **Copy Assignment**: Complete TODO at line 95-101, store generated code
- **Move Assignment**: Complete TODO at line 84-93, store generated code

### Key Challenges
- Static initialization order (same as Phase 8 global functions)
- Static member access across translation units (linkage)
- Assignment operator self-assignment check
- Move assignment resource transfer semantics

### Verification Criteria
- Static variables accessible from all translation units
- Static initialization happens before first use
- Copy assignment works correctly (deep copy when needed)
- Move assignment transfers ownership correctly

### Dependencies
- None (independent)

**Parallel Execution**: ✅ Can run with other phases

---

## Phase 16: Enums & Range-For Loops (v2.9.0) ⏳ PLANNED

**Goal**: Add enum translation and range-based for loop expansion

**Status**: IMPORTANT - No explicit enum visitor, range-for only tracks nesting

### Deliverables
- `VisitEnumDecl` implementation (scoped and unscoped)
- Enum value translation
- `VisitCXXForRangeStmt` expansion (currently only tracks nesting)
- Iterator protocol expansion (begin/end/operator++)
- Enum + range-for test suite (12+ tests)

### Technical Approach
- **Enums**: Add `VisitEnumDecl(EnumDecl *D)` visitor method
- **Scoped Enums**: Generate C enum with prefixed names
- **Unscoped Enums**: Generate C enum directly
- **Range-For**: Expand to traditional for loop with iterators
- **Iterator Protocol**: Call begin()/end() and expand operator++ and operator*

### Key Challenges
- Scoped enum name scoping in C (prefix with enum name)
- Underlying type for enums (C++11 feature)
- Range-for on arrays vs. containers (different expansion)
- Iterator type deduction (auto)

### Verification Criteria
- Scoped enums don't pollute namespace
- Enum values have correct underlying types
- Range-for loops iterate correctly over arrays and containers
- Iterator protocol expanded correctly

### Dependencies
- **Synergy with Phase 14** (operator overloading for iterators)

**Parallel Execution**: ✅ Can run with other phases (minimal synergy with Phase 14)

---

## Phase 17: Comprehensive Feature Integration & Testing (v3.0.0 - MAJOR) ⏳ PLANNED

**Goal**: Validate all features work together in real-world C++ programs

**Status**: INTEGRATION - Final validation and v3.0.0 release

### Deliverables
- Comprehensive integration test suite (50+ tests)
- Real-world C++ program corpus (10+ programs)
- Feature interaction testing (lambdas + templates, virtual + RTTI, etc.)
- Performance benchmarking (v1.17.0 → v3.0.0)
- Complete feature documentation
- Major version release (v3.0.0)

### Technical Approach
- Create test corpus with diverse C++ patterns (STL usage, design patterns, etc.)
- Test all pairwise feature combinations
- Measure transpilation time, generated code size, runtime performance
- Document known limitations
- Generate example gallery

### Key Challenges
- Feature interaction bugs (Phase X works alone but fails with Phase Y)
- Performance regression across all phases (target: <20% cumulative)
- Comprehensive documentation for 25+ features
- Migration guide from v1.17.0 to v3.0.0

### Verification Criteria
- All 50+ integration tests pass
- Real-world programs transpile and run correctly
- Performance regression <20% vs. v1.17.0
- Documentation complete and accurate
- All linters passing

### Dependencies
- **Requires Phases 8-16** (all C++ features)
- **Synergy with Phase 7** (ACSL + features)

**Parallel Execution**: ❌ Sequential after all other phases

---

## Complete Release Plan

### ACSL Workstream (Phases 1-7)

| Phase | Version | Component | Tests | Status | Release Criteria |
|-------|---------|-----------|-------|--------|------------------|
| 1 | v1.18.0 | ACSLStatementAnnotator | 15+ | ✅ COMPLETE | Assertions provable, zero false positives |
| 2 | v1.19.0 | ACSLTypeInvariantGenerator | 10+ | ✅ COMPLETE | Type invariants checked, no conflicts |
| 3 | v1.20.0 | ACSLAxiomaticBuilder | 12+ | ✅ COMPLETE | Axioms consistent, lemmas provable |
| 4 | v1.21.0 | ACSLGhostCodeInjector | 10+ | ✅ COMPLETE | Ghost code aids proofs, zero overhead |
| 5 | v1.22.0 | ACSLBehaviorAnnotator | 15+ | ✅ COMPLETE | Behaviors complete/disjoint, provable |
| 6 | v1.23.0 | ACSLMemoryPredicateAnalyzer | 10+ | ⏳ PLANNED | Memory safety provable |
| 7 | v2.0.0 | ACSL Integration | 35+ | ⏳ PLANNED | ≥80% proof success, <10% perf impact |

**ACSL Tests**: 117+ new tests (plus existing 37 = 154+ total)

### C++ Feature Workstream (Phases 8-17)

| Phase | Version | Feature | Tests | Status | Release Criteria |
|-------|---------|---------|-------|--------|------------------|
| 8 | v2.1.0 | Standalone Functions | 12+ | ⏳ PLANNED | main() + free functions work |
| 9 | v2.2.0 | Virtual Methods | 15+ | ⏳ PLANNED | Vtable dispatch correct |
| 10 | v2.3.0 | Lambda Expressions | 18+ | ⏳ PLANNED | Closures work correctly |
| 11 | v2.4.0 | Templates | 12+ | ⏳ PLANNED | Instantiation correct |
| 12 | v2.5.0 | Exceptions | 15+ | ⏳ PLANNED | Stack unwinding + RAII |
| 13 | v2.6.0 | RTTI | 10+ | ⏳ PLANNED | typeid + dynamic_cast work |
| 14 | v2.7.0 | Operator Overloading | 15+ | ⏳ PLANNED | All operators translate |
| 15 | v2.8.0 | Static + Assignment | 12+ | ⏳ PLANNED | Statics + copy/move work |
| 16 | v2.9.0 | Enums + Range-For | 12+ | ⏳ PLANNED | Enums + range loops work |
| 17 | v3.0.0 | Feature Integration | 50+ | ⏳ PLANNED | All features work together |

### Validation Workstream

| Phase | Version | Component | Tests | Status | Release Criteria |
|-------|---------|-----------|-------|--------|------------------|
| 30 | - | Real-World Transpilation | 5+ | ⏳ IN PROGRESS | Real projects transpile correctly |

### Architecture Enhancement Workstream

| Phase | Version | Component | Tests | Status | Release Criteria |
|-------|---------|-----------|-------|--------|------------------|
| 31-02 | v2.2.0 | COM-Style Vtable (Virtual) | 5+ | ⏳ PLANNED | Virtual methods type-safe |
| 31-03 | v2.3.0 | COM-Style All Methods | 5+ | ⏳ PLANNED | All methods type-safe |
| 31-04 | v2.4.0 | Cleanup & Optimization | - | ⏳ PLANNED | Code clean, optimized |

**Feature Tests**: 171+ new tests

**Combined Total**: 117 (ACSL) + 171 (Features) + 37 (existing) = **325+ tests**

---

## Parallel Execution Strategy

### Independent Phases (Can Run Simultaneously)

**Batch 1**: ACSL + Critical Features
- Phase 6 (Memory Predicates)
- Phase 8 (Standalone Functions)
- Phase 9 (Virtual Methods)
- Phase 11 (Templates)
- Phase 12 (Exceptions)
- Phase 13 (RTTI)

**Batch 2**: Sequential Dependencies
- Phase 10 (Lambdas) - AFTER Phase 8

**Batch 3**: Important Features (Independent)
- Phase 14 (Operators)
- Phase 15 (Static + Assignment)
- Phase 16 (Enums + Range-For)

**Batch 4**: Final Integration (Sequential)
- Phase 7 (ACSL Integration) - AFTER Phases 1-6
- Phase 17 (Feature Integration) - AFTER Phases 8-16

### Recommended Execution Order

**Week 1-2**: Batch 1 (6 phases in parallel)
- 6, 8, 9, 11, 12, 13 → 6 parallel agents

**Week 3**: Sequential + Independent
- Phase 10 (depends on 8) → 1 agent
- Phase 14, 15, 16 → 3 parallel agents

**Week 4**: Final Integration
- Phase 7 → 1 agent
- Phase 17 → 1 agent

**Total Timeline**: 4 weeks (aggressive parallelization)

---

## Success Criteria Summary

### ACSL Functional Requirements (Phases 1-7)
- ✅ All ACSL 1.17+ statement annotations supported
- ✅ Global type invariants generated
- ✅ Axiomatic definitions for mathematical properties
- ✅ Ghost code for complex specifications
- ✅ Function behaviors for conditional contracts
- ⏳ Advanced memory predicates (allocable, freeable, etc.)

### C++ Feature Requirements (Phases 8-17)
- ⏳ Standalone functions (main + free functions)
- ⏳ Virtual methods (OOP polymorphism)
- ⏳ Lambda expressions (closures)
- ⏳ Templates (generics)
- ⏳ Exception handling (try-catch-throw)
- ⏳ RTTI (typeid, dynamic_cast)
- ⏳ Operator overloading
- ⏳ Static members + assignment operators
- ⏳ Enums + range-based for loops

### Quality Requirements (All Phases)
- Test coverage ≥95% across all features
- 100% ACSL parsing success with Frama-C (ACSL phases)
- ≥80% proof success rate with Frama-C WP (ACSL phases)
- Real C++ programs transpile correctly (feature phases)
- Performance impact ≤20% (cumulative across all phases)
- Zero linting errors
- Strong typing enforced (100%)

### Documentation Requirements
- CHANGELOG.md updated for each release
- README.md feature list complete (ACSL + C++ features)
- Website features.astro updated
- Example gallery with verified code (ACSL) and real programs (features)
- Integration guide for Frama-C users (ACSL)
- Migration guide from v1.17.0 to v3.0.0

---

# WORKSTREAM C: VALIDATION & UTILITIES

## Phase 30: Transpile Real-World Test Projects ⏳ IN PROGRESS

**Goal**: Create comprehensive transpiled C versions of all real-world test projects for validation and demonstration

**Version**: Utility (no version bump)

**Status**: Phase 30-02 complete (pointer recursion fix), Phase 30-01 planned

---

# WORKSTREAM D: ARCHITECTURE ENHANCEMENTS

## Phase 31: COM-Style Vtable Architecture ⏳ PLANNED

**Goal**: Implement COM/DCOM-style strongly-typed virtual method tables with explicit static declarations for compile-time type safety

**Research**: Complete - See `.planning/phases/31-com-vmt-architecture/31-01-FINDINGS.md`

**Recommendation**: ADOPT (hybrid approach) - Strong type safety with zero runtime cost

### Phase 31-02: COM-Style for Virtual Methods (v2.2.0) ✅ COMPLETE

**Goal**: Add static function declarations for all virtual methods

**Deliverables**:
- ✅ `VtableGenerator::generateStaticDeclarations()` method
- ✅ Static declarations in generated headers
- ✅ ComStyleVtableTest suite (8 tests - exceeded target)
- ✅ Documentation: VTABLE_IMPLEMENTATION.md (400+ lines)
- ✅ Fixed pre-existing bugs in VtableGeneratorTest

**Benefits**:
- ✅ Compile-time type safety (catches signature mismatches)
- ✅ Better debugging (function names in stack traces)
- ✅ Zero runtime overhead
- ✅ Self-documenting code

**Actual Effort**: ~4 hours

**Completed**: 2025-12-23

**Summary**: `.planning/phases/31-com-vmt-architecture/31-02-SUMMARY.md`

**Dependencies**: None (independent phase)

---

### Phase 31-03: Extend to All Methods (v2.3.0) ✅ COMPLETE

**Goal**: Extend COM-style pattern from virtual methods to ALL methods

**Deliverables**:
- ✅ `CppToCVisitor::generateAllMethodDeclarations()` method
- ✅ MethodSignatureHelper shared utility (DRY)
- ✅ ComStyleAllMethodsTest suite (8 tests)
- ✅ Documentation: METHOD_GENERATION.md

**Benefits**:
- ✅ Universal type safety (all methods verified)
- ✅ Consistent code style
- ✅ Simplified generator (one pattern for everything)

**Completed**: 2025-12-23
**Summary**: `.planning/phases/31-com-vmt-architecture/31-03-SUMMARY.md`

**Dependencies**: Requires Phase 31-02 complete

---

### Phase 31-04: Cleanup & Optimization (v2.4.0) ⏳ PLANNED

**Goal**: Remove legacy code, optimize performance, finalize COM-style as standard

**Deliverables**:
- Remove legacy vtable generation code paths
- Optimize signature generation (~25% faster)
- Comprehensive inline documentation
- Performance benchmarks
- Updated architecture docs

**Benefits**:
- ✅ Clean, maintainable codebase
- ✅ Better performance
- ✅ Complete documentation

**Effort**: ~1-2 hours

**Dependencies**: Requires Phase 31-02 and 31-03 complete

**Completes**: Phase 31 series (COM-Style Vtable Architecture)

---

## Phase 30 (continued): Transpile Real-World Test Projects ⏳ PLANNED

**Version**: Utility (no version bump)

### Deliverables
- Transpilation script: `scripts/transpile-real-world.sh`
- Transpiled projects in: `tests/real-world/transpiled/<project>/`
  - json-parser (transpiled C code)
  - logger (transpiled C code)
  - resource-manager (transpiled C code)
  - string-formatter (transpiled C code)
  - test-framework (transpiled C code)
- CMakeLists.txt for each transpiled project
- Comprehensive documentation and validation reports

### Technical Approach
- Use `build_working/transpiler-api-cli` to transpile all source files
- Maintain directory structure (src/, include/, tests/)
- Parse JSON output to extract transpiled .c and .h files
- Create build configuration for C99 compilation
- Validate transpiled code compiles
- Document success rates and limitations

### Success Criteria
- All 5 projects transpiled (50+ files)
- Transpilation success rate >= 90%
- At least 3 out of 5 projects compile successfully
- Complete documentation and reports

### Dependencies
- Requires transpiler-api-cli built and functional
- Runtime library available

---

## Risk Mitigation

### ACSL Technical Risks
- **ACSL complexity explosion**: Implement verbosity levels (none/basic/medium/full)
- **Performance degradation**: Profile after each phase, optimize hot paths
- **Proof failures**: Tune annotation heuristics based on WP feedback
- **Edge cases**: Comprehensive test suite with corner cases

### C++ Feature Technical Risks
- **Feature interaction bugs**: Phase 17 comprehensive integration testing
- **Performance cumulative regression**: Target ≤20% total, profile after each phase
- **Template instantiation explosion**: Limit depth, detect infinite recursion
- **Exception unwinding overhead**: Benchmark, optimize setjmp/longjmp usage
- **Closure memory management**: Careful lifetime analysis, memory leak detection

### Project Risks
- **Scope creep**: Strict adherence to identified 25 features, no additions
- **Testing gaps**: TDD mandatory, 95%+ coverage enforced
- **Integration issues**: Frama-C validation (ACSL) + real program corpus (features)
- **Parallel workstream conflicts**: Clear phase independence, git-flow for isolation

---

## Milestone Markers

| Version | Milestone | Description |
|---------|-----------|-------------|
| v2.0.0 | ACSL Complete | All ACSL 1.17+ features + Frama-C validation |
| v3.0.0 | Full C++ Support | Critical C++ features + comprehensive integration |

---

## Next Steps

### Immediate Actions (Choose Based on Priority)

**Option A: Complete ACSL First**
1. Execute Phase 6 (Memory Predicates)
2. Execute Phase 7 (ACSL Integration)
3. Release v2.0.0
4. Then start C++ features (Phase 8+)

**Option B: Parallel Execution (Recommended)**
1. Execute Batch 1 in parallel (Phases 6, 8, 9, 11, 12, 13)
2. Execute Phase 10 after Phase 8 completes
3. Execute Batch 3 in parallel (Phases 14, 15, 16)
4. Execute Phase 7 after Phase 6 completes
5. Execute Phase 17 after all features complete
6. Release v2.0.0 (ACSL) and v3.0.0 (Features)

**Option C: Critical Features First**
1. Execute Phases 8, 9, 10 (standalone functions, virtual methods, lambdas)
2. Release v2.1.0, v2.2.0, v2.3.0
3. Then complete ACSL (Phases 6-7)
4. Then high-value features (Phases 11-13)
5. Then important features (Phases 14-16)
6. Then integration (Phase 17)

**Recommended**: **Option B (Parallel Execution)** - maximizes velocity, delivers both workstreams

---

**Ready to plan**: Choose execution strategy and plan first phase(s)

---

# WORKSTREAM E: C++23 TRANSPILER FIXES (CRITICAL PRIORITY)

**Motivation**: Comprehensive gaps analysis (`.prompts/045-cpp23-gaps-analysis/`) revealed critical blockers preventing production C++23 support:
- **70% of integration tests blocked** by header file skipping architecture issue
- **Phase 4 completely broken** due to Clang API mismatch (Clang 17 vs 18+)
- **0% real-world test pass rate** despite 88% unit test success
- **Actual C++23 coverage: 10-12%** (not 20-25% claimed)

**User Mandate**: "Unacceptable to customers" - requires PRODUCTION-READY transpiler with comprehensive C++23 support.

**Priority**: **CRITICAL** - Blocks all other work until foundation is stable.

---

## Phase 32: Transpiler Architecture Fix ✅ COMPLETE

**Goal**: Fix critical C++ AST routing bug preventing template monomorphization

**Version**: v2.3.0 (patch release)

**Completed**: 2025-12-24

### Problem Identified
Phase 32 discovered transpiler was routing templates through C++ AST printer instead of C AST transformation, breaking all template-based C++23 features.

### Fix Applied
- Routed all C++ constructs through proper C AST transformation pipeline
- Fixed template monomorphization to generate C AST nodes (not strings)
- Validated with AdvancedTemplateIntegrationTest A/B comparison

### Impact
- ✅ Template monomorphization now generates valid C code
- ✅ Foundation stable for C++23 feature integration
- ✅ Critical blocker resolved

### Dependencies
- None (architecture fix)

**Summary**: `.planning/phases/32-transpiler-architecture-fix/32-01-SUMMARY.md`

---

## Phase 33: C++23 Validation Suite Integration ✅ COMPLETE

**Goal**: Establish comprehensive C++23 validation framework with baseline metrics

**Version**: Utility (no version bump)

**Completed**: 2025-12-24

### Deliverables Completed
- ✅ Integrated 130 GCC C++23 tests across 9 categories
- ✅ Created A/B testing framework (run-tests.sh, compare.py)
- ✅ Generated baseline metrics: **0.0% C++23 support** (honest assessment)
- ✅ Documented architectural gaps in GAPS.md, FEATURE-MATRIX.md, ROADMAP.md

### Baseline Metrics
```
Total Tests:           130
C++ Build Success:     0.0%
Transpile Success:     0.0%
C Build Success:       0.0%
Output Match:          0.0%
Overall Pass Rate:     0.0%
```

### Critical Findings
- Header file skipping blocks ~91/130 tests (70%)
- Phase 4 API blocker (Clang 17 vs 18)
- No integration testing infrastructure
- CTAD inherited constructors not implemented

### Impact
- ✅ Clear baseline established for measuring progress
- ✅ Comprehensive test infrastructure ready
- ✅ All gaps documented with severity levels
- ✅ Roadmap for Phases 34-40 informed by data

**Summary**: `tests/real-world/cpp23-validation/PHASE-33-SUMMARY.md`

**Dependencies**: Requires Phase 32 complete (architecture fix)

---

## Phase 34: Fix Header File Skipping (v2.5.0) ⏳ PLANNED

**Goal**: Enable multi-file transpilation by removing isInMainFile() guards

**Status**: **CRITICAL** - Blocks 70% of C++23 tests (~91/130)

**Estimated Effort**: 2-3 weeks

### Problem Statement
CppToCVisitor systematically skips ALL declarations from included headers using `isInMainFile()` checks at 12 locations. This architectural decision breaks real-world C++23 code which properly separates declarations (headers) from implementations (.cpp files).

**Impact**:
- Multi-file projects cannot be transpiled
- Library code in headers silently ignored
- Phase 33 tests compile but produce ZERO output
- No error messages - silent failure mode

### Deliverables
- ✅ Multi-file transpilation architecture
- ✅ File origin tracking (main vs header)
- ✅ Separate .h and .c output generation
- ✅ Include guard generation enhancements
- ✅ Cross-file dependency handling
- ✅ Declaration order preservation
- ✅ Integration validation with Phase 33 subset

### Technical Approach

**Phase 34-01: Architecture Research** (2-3 days)
- Analyze FileOutputManager current behavior
- Document all 12 isInMainFile() usage sites
- Design FileOriginTracker system
- Create multi-file test cases

**Phase 34-02: Remove Guards from Class Visitors** (2-3 days)
- Remove isInMainFile() from VisitCXXRecordDecl (line 136)
- Remove isInMainFile() from VisitCXXMethodDecl (line 273)
- Add basic FileOriginTracker infrastructure
- Test with simple class in header

**Phase 34-03: Remove Guards from Remaining Visitors** (2-3 days)
- Remove 10 remaining isInMainFile() guards
- Implement full FileOriginTracker class
- Update all visitors to use tracker
- Test with complex multi-file example

**Phase 34-04: Separate Header/Implementation Output** (3-4 days)
- Modify FileOutputManager for dual output
- Implement declaration/definition splitting logic
- Handle forward declarations
- Test with Phase 33 subset (multidim-subscript)

**Phase 34-05: Enhanced Include Guards** (2 days)
- Extend IncludeGuardGenerator
- Add cross-file dependency tracking
- Preserve declaration order across files
- Test with full multi-file project

**Phase 34-06: Integration Validation** (1-2 days)
- Run Phase 33 multidim-subscript category (16 tests)
- Validate output compiles and runs
- Measure pass rate improvement (expect 12-14/16, 75-85%)
- Document remaining failures

### Key Challenges
- Distinguishing declarations vs definitions across files
- Handling template instantiations in headers
- Preserving correct include order
- Avoiding duplicate symbol definitions
- Managing circular header dependencies

### Verification Criteria
- ✅ At least 12/16 multidim-subscript tests passing (75%+)
- ✅ Multi-file projects transpile without manual inlining
- ✅ Generated .h files valid C headers
- ✅ Generated .c files compile and link
- ✅ No duplicate symbol errors
- ✅ Include dependencies correct

### Dependencies
- None (independent architecture fix)

### Expected Impact
- **Unblocks ~91/130 Phase 33 tests** (70% of validation suite)
- Enables real-world multi-file project transpilation
- Foundation for remaining C++23 feature validation

**Parallel Execution**: ❌ Sequential (foundation must be stable first)

---

## Phase 35: Upgrade Clang and Activate Phase 4 (v2.6.0) ⏳ PLANNED

**Goal**: Upgrade to Clang 18+ and activate deducing this translator

**Status**: **HIGH** - Phase 4 completely non-functional (10/12 tests failing)

**Estimated Effort**: 1-2 days

### Problem Statement
Phase 4 (Deducing This / Explicit Object Parameters) implementation is complete with comprehensive infrastructure, but blocked by missing `isExplicitObjectMemberFunction()` API in Clang 17. This API was introduced in Clang 18+.

**Current State**:
- ✅ DeducingThisTranslator class implemented (326 lines)
- ✅ 12 comprehensive tests written
- ✅ Integration with CppToCVisitor complete
- ❌ API unavailable in current Clang 17
- ⚠️ 2/12 tests passing (logic-only, no AST dependency)
- ❌ 10/12 tests failing (require Clang 18+ API)

### Deliverables
- ✅ LLVM/Clang upgraded to version 18+
- ✅ Phase 4 tests rerun and passing (expect 12/12)
- ✅ CMake configuration updated if needed
- ✅ Documentation updated with Clang version requirement
- ✅ CI/CD updated to use Clang 18+

### Technical Approach

**Phase 35-01: Clang Upgrade** (1 day)
```bash
# macOS (Homebrew)
brew upgrade llvm

# Verify version
clang --version  # Should show 18.0.0 or higher

# Update CMakeLists.txt if needed
find_package(LLVM 18 REQUIRED)
```

**Phase 35-02: Rerun Phase 4 Tests** (few hours)
```bash
cd build_working
ctest -R DeducingThisTranslatorTest --verbose
```

Expected result: **12/12 tests passing** (infrastructure auto-activates)

### Key Challenges
- System Clang vs Homebrew Clang path conflicts
- CMake finding correct LLVM installation
- Potential ABI compatibility issues

### Verification Criteria
- ✅ Clang version 18+ confirmed
- ✅ All 12 DeducingThisTranslatorTest tests passing (100%)
- ✅ No regressions in other tests
- ✅ Build system finds correct Clang automatically

### Dependencies
- **Requires Phase 34 complete** (header skipping fixed)
- Otherwise Phase 4 features won't be testable in real code

### Expected Impact
- **Activates Phase 4 (Deducing This)** - major C++23 feature
- Improves C++23 coverage: 10-12% → 15-18%
- Validates infrastructure investment

**Parallel Execution**: ❌ Sequential after Phase 34

---

## Phase 36: Add Integration Tests (v2.7.0) ⏳ PLANNED

**Goal**: Create standalone integration tests validating Phase 1-6 features in real C++23 code

**Status**: **HIGH** - Zero integration testing currently (0/130 Phase 33 pass rate)

**Estimated Effort**: 2-3 days

### Problem Statement
Unit tests pass (70/80, 87.5%) but integration tests fail (0/130, 0%). This gap reveals:
- Features may have edge cases not caught by unit tests
- Phase 1-6 never tested in real C++23 code contexts
- Template interaction untested
- False confidence from unit test success

### Deliverables
- ✅ `tests/integration/cpp23/` directory with single-file tests
- ✅ 30+ integration tests covering Phase 1-6 features
- ✅ Template interaction tests (C++23 features + templates)
- ✅ Combined feature tests (multidim subscript + static operators, etc.)
- ✅ Real-world usage patterns
- ✅ CMakeLists.txt for integration test suite

### Technical Approach

**Phase 36-01: Single-File Integration Tests** (1-2 days)
Create `tests/integration/cpp23/*.cpp` with all code inline (bypasses header skipping):

```cpp
// multidim_subscript_integration.cpp
template<typename T>
class Matrix {  // All code in one file
    T& operator[](int i, int j) { /* ... */ }
};

int main() {
    Matrix<int> m;
    m[0, 1] = 42;  // C++23 multidim subscript
    return 0;
}
```

Categories:
- Multidim subscript (6 tests)
- Static operators (4 tests)
- [[assume]] attribute (4 tests)
- Deducing this (6 tests)
- if consteval (4 tests)
- auto(x) decay-copy (4 tests)
- Constexpr enhancements (4 tests)

**Phase 36-02: Feature Interaction Tests** (1 day)
Test combinations:
- Multidim subscript on template class
- Static operator in template
- auto(x) with template parameter
- [[assume]] in template function
- if consteval in constexpr template
- Deducing this with virtual methods

### Verification Criteria
- ✅ At least 25/30 integration tests passing (83%+)
- ✅ Template interaction tests validate monomorphization
- ✅ Combined features work together
- ✅ No silent failures (errors reported clearly)

### Dependencies
- **Requires Phase 34 complete** (for multi-file tests later)
- **Requires Phase 35 complete** (for Phase 4 deducing this tests)

### Expected Impact
- Validates Phase 1-6 implementation quality
- Discovers edge cases missed by unit tests
- Provides regression protection
- Builds confidence in C++23 support

**Parallel Execution**: ❌ Sequential after Phases 34-35

---

## Phase 37: Implement CTAD Inherited Constructors (v2.8.0) ⏳ PLANNED

**Goal**: Complete Feature #8 from original C++23 plan (P2582R1)

**Status**: **MEDIUM** - Unimplemented feature from Phase 1-6 plan

**Estimated Effort**: 1-2 weeks

### Problem Statement
CTAD (Class Template Argument Deduction) with Inherited Constructors was Feature #8 in original plan but never implemented. Phase 33 has 10 tests waiting for this feature.

**Current State**:
- ❌ No CTADInheritedTranslator class
- ❌ No source files
- ❌ No tests
- ⚠️ Basic CTAD works (earlier implementation)
- ❌ Inherited constructor cases fail

### Deliverables
- ✅ `CTADInheritedTranslator` class (header + implementation)
- ✅ Constructor inheritance analysis
- ✅ CTAD deduction guide generation for inherited ctors
- ✅ Test suite (12+ tests)
- ✅ Integration with CppToCVisitor
- ✅ Documentation

### Technical Approach

**Phase 37-01: Infrastructure** (3-4 days)
```cpp
// include/CTADInheritedTranslator.h
class CTADInheritedTranslator {
public:
    std::string translateInheritedConstructor(
        const CXXConstructorDecl *CD,
        const CXXRecordDecl *Derived
    );
    
    std::string generateDeductionGuide(
        const CXXConstructorDecl *BaseCtor,
        const CXXRecordDecl *Derived
    );
};
```

**Phase 37-02: Test Suite** (2-3 days)
Create `tests/CTADInheritedTranslatorTest.cpp` with 12+ tests:
- Simple inheritance CTAD
- Multiple inheritance CTAD
- Virtual inheritance CTAD
- Template base class CTAD
- Constructor forwarding
- Deduction guide edge cases

**Phase 37-03: Integration** (2-3 days)
- Add to CppToCVisitor
- Hook into template instantiation
- Test with Phase 33 CTAD category (10 tests)

### Key Challenges
- Deduction guide synthesis for inherited constructors
- Multiple inheritance scenarios
- Template parameter forwarding
- Virtual base class handling

### Verification Criteria
- ✅ 12/12 unit tests passing
- ✅ 8/10 Phase 33 CTAD tests passing (80%+)
- ✅ Integration with existing CTAD infrastructure
- ✅ No regressions in basic CTAD

### Dependencies
- **Requires Phase 34 complete** (multi-file transpilation)
- **Synergy with Phase 11** (Template Integration from Workstream B)

### Expected Impact
- Completes original 8-feature C++23 plan
- Improves C++23 coverage: 15-18% → 20-22%
- Satisfies Phase 33 CTAD category

**Parallel Execution**: ❌ Sequential after Phase 36

---

## Phase 38: Enhanced Constexpr Evaluation (v2.9.0) ⏳ PLANNED

**Goal**: Expand compile-time evaluation beyond simple literals

**Status**: **MEDIUM** - Phase 6 only handles simple cases

**Estimated Effort**: 2-3 weeks

### Problem Statement
Phase 6 constexpr support is limited to simple cases:
- ✅ Return literal: `constexpr int f() { return 42; }`
- ✅ Return expression: `constexpr int f(int x) { return x + 1; }`
- ❌ Loops: `constexpr int fib(int n) { for... }`
- ❌ Control flow: `constexpr int max(int a, int b) { if (a > b)... }`
- ❌ Multiple statements
- ❌ Recursive functions

**Current Fallback**: Runtime evaluation with silent degradation

### Deliverables
- ✅ Extended ConstexprEnhancementHandler
- ✅ APValue evaluator integration (Clang's compile-time evaluator)
- ✅ Loop evaluation support
- ✅ Control flow evaluation (if/else/switch)
- ✅ Multiple statement support
- ✅ Recursive constexpr function support
- ✅ Test suite expansion (20+ tests)
- ✅ Warning system for fallback cases

### Technical Approach

**Phase 38-01: APValue Integration** (1 week)
Leverage Clang's existing APValue evaluator:
```cpp
// Expand ConstexprEnhancementHandler
bool evaluateConstexpr(const FunctionDecl *FD, 
                       APValue &Result) {
    Expr::EvalResult ER;
    if (FD->getBody()->EvaluateAsRValue(ER, Context)) {
        Result = ER.Val;
        return true;
    }
    return false;
}
```

**Phase 38-02: Pattern Expansion** (1 week)
- Loops (for, while, do-while)
- Control flow (if, else, switch, ternary)
- Multiple statements (sequencing)
- Local variables

**Phase 38-03: Warning System** (few days)
- Emit warning when fallback to runtime
- Document unsupported patterns
- Provide workarounds

### Key Challenges
- Clang APValue evaluator integration complexity
- Recursive function evaluation (stack depth limits)
- Memory allocation during constexpr (not allowed in C)
- UB detection in constexpr context

### Verification Criteria
- ✅ 15/19 Phase 33 constexpr-enhancements tests passing (80%+)
- ✅ Loops and control flow evaluate at compile-time
- ✅ Warnings emitted for fallback cases
- ✅ No performance regression

### Dependencies
- None (independent enhancement)

### Expected Impact
- Improves C++23 coverage: 20-22% → 25-30%
- Better semantic fidelity (compile-time → compile-time)
- Performance improvement (fewer runtime evaluations)

**Parallel Execution**: ✅ Can run with Phase 39 (documentation)

---

## Phase 39: Update User Documentation (v3.0.0-rc) ⏳ PLANNED

**Goal**: Provide comprehensive user-facing documentation for C++23 support

**Status**: **MEDIUM** - Documentation lags implementation

**Estimated Effort**: 1-2 days

### Problem Statement
Gaps analysis identified 5 documentation gaps:
1. User-facing feature support matrix missing
2. Limitations not user-accessible (buried in code comments)
3. Migration guide missing (no practical C++23 → C advice)
4. Warning messages undocumented (users don't know meanings)
5. FEATURE-MATRIX.md outdated (shows 0% despite implementations)

### Deliverables
- ✅ Updated `tests/real-world/cpp23-validation/docs/FEATURE-MATRIX.md`
- ✅ New `docs/CPP23_LIMITATIONS.md`
- ✅ New `docs/CPP23_MIGRATION_GUIDE.md`
- ✅ New `docs/WARNING_REFERENCE.md`
- ✅ Updated `README.md` with C++23 support section
- ✅ Updated website `features.astro` (if applicable)

### Technical Approach

**Phase 39-01: Feature Matrix Update** (2-3 hours)
Update FEATURE-MATRIX.md with actual coverage:
```markdown
| Feature | Unit Tests | Integration | Phase 33 | Status |
|---------|-----------|-------------|----------|--------|
| Multidim subscript | 12/12 (100%) | 6/6 (100%) | 14/16 (87%) | ✅ Complete |
| Static operators | 10/10 (100%) | 4/4 (100%) | 7/8 (87%) | ✅ Complete |
| [[assume]] | 12/12 (100%) | 4/4 (100%) | 11/13 (85%) | ✅ Complete |
| Deducing this | 12/12 (100%) | 6/6 (100%) | 8/10 (80%) | ✅ Complete (Clang 18+) |
| if consteval | 12/12 (100%) | 4/4 (100%) | 9/13 (69%) | ⚠️ Partial (runtime fallback) |
| auto(x) | 12/12 (100%) | 4/4 (100%) | 10/22 (45%) | ⚠️ Partial (simple cases) |
| Constexpr | 10/10 (100%) | 4/4 (100%) | 7/19 (37%) | ⚠️ Partial (enhanced in Phase 38) |
| CTAD inherited | 12/12 (100%) | 4/4 (100%) | 8/10 (80%) | ✅ Complete |
```

**Phase 39-02: Limitations Guide** (2-3 hours)
Create CPP23_LIMITATIONS.md documenting:
- Architectural impossibilities (concepts, modules, ranges)
- Runtime fallback features (constexpr, consteval)
- Known edge cases
- Workarounds and alternatives

**Phase 39-03: Migration Guide** (2-3 hours)
Create CPP23_MIGRATION_GUIDE.md with practical advice:
- Which C++23 features transpile well
- Which require code changes
- Common patterns and their C equivalents
- Performance considerations

**Phase 39-04: Warning Reference** (1-2 hours)
Document all warning messages with:
- What triggered the warning
- What it means
- How to address it
- Whether it's safe to ignore

### Verification Criteria
- ✅ All 5 documentation gaps addressed
- ✅ User-facing docs complete and accurate
- ✅ Examples provided for all features
- ✅ Migration guide tested on real code

### Dependencies
- **Requires Phases 34-38 complete** (feature set finalized)

### Expected Impact
- Users understand what's supported
- Realistic expectations set
- Migration path clear
- Support burden reduced (self-service docs)

**Parallel Execution**: ✅ Can run with Phase 38 (independent)

---

## Phase 40: Rerun Phase 33 Validation (v3.0.0) ⏳ PLANNED

**Goal**: Execute full Phase 33 validation suite and generate final compliance report

**Status**: **FINAL VALIDATION** - Measures success of Phases 34-39

**Estimated Effort**: 1 day

### Problem Statement
Phase 33 established 0.0% baseline. After fixing all gaps (Phases 34-39), we need final metrics to measure success and declare v3.0.0 release.

**Expected Results** (conservative):
- Overall pass rate: **60-70%** (from 0%)
- Multidim subscript: 14/16 (87%)
- Static operators: 7/8 (87%)
- [[assume]]: 11/13 (85%)
- Deducing this: 8/10 (80% - with Clang 18)
- if consteval: 9/13 (69% - runtime fallback acceptable)
- auto(x): 10/22 (45% - simple cases only)
- Constexpr: 12/19 (63% - after Phase 38 enhancements)
- CTAD inherited: 8/10 (80%)
- Attributes: 8/13 (60%)
- Miscellaneous: 10/19 (50%)
- Ranges: 0/10 (0% - architectural blocker, documented)

### Deliverables
- ✅ Full Phase 33 test suite execution
- ✅ Updated baseline-metrics.json
- ✅ Updated compliance-report.html
- ✅ Comparison report (baseline vs final)
- ✅ v3.0.0 release notes
- ✅ CHANGELOG.md update

### Technical Approach

**Phase 40-01: Execute Test Suite** (3-4 hours)
```bash
cd tests/real-world/cpp23-validation/ab-test
./run-tests.sh --all --output results/final-metrics.json
```

**Phase 40-02: Generate Reports** (2-3 hours)
```bash
python3 scripts/generate-baseline-metrics.py \
    --input results/final-metrics.json \
    --output results/v3.0.0-compliance-report.html \
    --compare results/baseline-metrics.json
```

### Verification Criteria
- ✅ Overall pass rate ≥60% (10x improvement from 0%)
- ✅ At least 5 categories with ≥70% pass rate
- ✅ Zero regressions (no previously passing tests now failing)
- ✅ All metrics documented and explained

### Dependencies
- **Requires ALL Phases 34-39 complete**

### Expected Impact
- **Validates Workstream E success**
- Provides data-driven release decision
- Demonstrates 10x improvement (0% → 60-70%)
- Justifies v3.0.0 major version bump
- Production-ready C++23 transpiler achieved

**Parallel Execution**: ❌ Sequential (final validation)

---

## Workstream E Summary

### Timeline

| Phase | Effort | Dependency | Can Parallel? |
|-------|--------|------------|---------------|
| 34 | 2-3 weeks | None | ❌ (foundation) |
| 35 | 1-2 days | Phase 34 | ❌ |
| 36 | 2-3 days | Phases 34,35 | ❌ |
| 37 | 1-2 weeks | Phase 36 | ❌ |
| 38 | 2-3 weeks | None | ✅ (with 39) |
| 39 | 1-2 days | Phases 34-38 | ✅ (with 38) |
| 40 | 1 day | ALL above | ❌ (final) |

**Total Timeline**: **6-8 weeks** (sequential + some parallelization)

### Success Metrics

**Coverage Improvement**:
- Baseline: 0% Phase 33 pass rate, 10-12% actual coverage
- Target: 60-70% Phase 33 pass rate, 60-70% actual coverage
- **Improvement: 6-7x coverage increase**

**Test Statistics**:
- Unit tests: 70/80 → 94/106 (88% → 89%, +26 tests from Phases 37-38)
- Integration tests: 0/130 → 78-91/130 (0% → 60-70%, Phase 33 validation)
- **Total improvement: +104-117 passing tests**

**User-Facing Impact**:
- Multi-file projects: BROKEN → ✅ WORKS
- Real-world C++23 code: 0% → 60-70% transpiles correctly
- Production readiness: UNACCEPTABLE → PRODUCTION-READY

### Quality Gates

Before declaring v3.0.0:
- ✅ All Phases 34-39 complete with SUMMARY.md
- ✅ Phase 40 validation ≥60% pass rate
- ✅ Zero critical bugs in issue tracker
- ✅ All unit tests passing (100%)
- ✅ Documentation complete and accurate
- ✅ Code review completed
- ✅ Performance regression ≤20% vs v2.4.0
- ✅ User acceptance testing successful

### Milestone: v3.0.0 - Production C++23 Transpiler

**Release Criteria**:
- 60-70% C++23 validation suite pass rate
- Multi-file transpilation working
- 8 C++23 features fully implemented
- Comprehensive documentation
- Proven real-world usage

**Breaking Changes**:
- Header file skipping removed (may affect single-file workflows)
- Requires Clang 18+ for deducing this feature
- constexpr/consteval runtime fallback (semantic change)

**Migration Guide**: See `docs/CPP23_MIGRATION_GUIDE.md`

---

**Ready to execute**: Phase 34-01 (Multi-file Architecture Research)

