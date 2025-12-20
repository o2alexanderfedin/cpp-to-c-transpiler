# Phase 2 Plan: Type Invariants (v1.19.0)

**Phase**: 2 of 7
**Roadmap**: `.planning/ROADMAP.md`
**Brief**: `.planning/BRIEF.md`
**Target Version**: v1.19.0
**Status**: PENDING
**Prerequisite**: Phase 1 (v1.18.0) complete

## Phase Goal

Implement global type invariants for user-defined types to automatically verify type constraints at all type boundaries. Extract common invariants from class predicates and promote to type-level specifications.

## Deliverables

### Source Code
- [ ] `include/ACSLTypeInvariantGenerator.h`
- [ ] `src/ACSLTypeInvariantGenerator.cpp`
- [ ] Integration with ACSLClassAnnotator

### Tests
- [ ] `tests/ACSLTypeInvariantGeneratorTest.cpp` (10+ tests)

### CLI Integration
- [ ] Add `--acsl-type-invariants={off,on}` flag

### Documentation
- [ ] Update `docs/CHANGELOG.md` for v1.19.0
- [ ] Update `README.md`
- [ ] Update `website/src/pages/features.astro`

### Release
- [ ] Git-flow release v1.19.0

## Technical Design

### Type Invariant Syntax
```c
/*@ type invariant ValidBuffer(Buffer b) =
  @   \valid(b.data + (0..b.capacity-1)) &&
  @   b.size <= b.capacity &&
  @   b.capacity > 0;
  @*/
```

### Key Features
1. Extract invariants from class predicates
2. Handle inheritance (invariant strengthening)
3. Support template types (monomorphized invariants)
4. Avoid circular dependencies
5. Integration with function contracts (automatic checking)

### Test Cases (10+)
1. BasicTypeInvariant - Simple struct with constraints
2. InheritanceInvariant - Derived class strengthening
3. TemplateTypeInvariant - Monomorphized template
4. PointerMemberInvariant - Valid pointer constraints
5. SizeCapacityInvariant - Relational constraints
6. CircularDependencyAvoidance - No mutual recursion
7. ArrayMemberInvariant - Array bounds
8. OptionalMemberInvariant - Nullable fields
9. EnumTypeInvariant - Enum range constraints
10. NestedTypeInvariant - Composed types

## Dependencies
- ACSLClassAnnotator (v1.17.0)
- Optional: Phase 1 assertions for validation

## Verification Criteria
- [ ] 10+ tests passing (100%)
- [ ] No conflicts with class invariants
- [ ] Frama-C type checks automatically
- [ ] Performance impact ≤5%
