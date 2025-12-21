# Phase 5 Plan: Function Behaviors (v1.22.0)

**Phase**: 5 of 7
**Roadmap**: `.planning/ROADMAP.md`
**Brief**: `.planning/BRIEF.md`
**Target Version**: v1.22.0
**Status**: PENDING
**Prerequisite**: Phase 1 recommended (behaviors can include assertions)

## Phase Goal

Generate named function behaviors for conditional contracts, enabling separate verification of different code paths based on preconditions.

## Deliverables

### Source Code
- [ ] `include/ACSLBehaviorAnnotator.h`
- [ ] `src/ACSLBehaviorAnnotator.cpp`
- [ ] Enhancement to ACSLFunctionAnnotator

### Tests
- [ ] `tests/ACSLBehaviorAnnotatorTest.cpp` (15+ tests)

### CLI Integration
- [ ] Add `--acsl-behaviors={off,on}` flag

### Documentation
- [ ] Update `docs/CHANGELOG.md` for v1.22.0
- [ ] Update `README.md`
- [ ] Update `website/src/pages/features.astro`

### Release
- [ ] Git-flow release v1.22.0

## Technical Design

### Behavior Syntax
```c
/*@ requires \valid(p);
  @ behavior null_input:
  @   assumes p == \null;
  @   ensures \result == -1;
  @ behavior valid_input:
  @   assumes p != \null;
  @   ensures \result == *p;
  @ complete behaviors;
  @ disjoint behaviors;
  @*/
int getValue(int *p) {
  if (p == NULL) return -1;
  return *p;
}
```

### Key Features
1. Extract behaviors from control flow (if/switch)
2. Generate behavior-specific assumes clauses
3. Generate behavior-specific ensures clauses
4. Check completeness (all cases covered)
5. Check disjointness (no overlap)

### Test Cases (15+)
1. SimpleBehaviorExtraction - If/else → 2 behaviors
2. SwitchBehaviors - Switch → N behaviors
3. CompletenessCheck - Complete behaviors verified
4. DisjointnessCheck - Disjoint behaviors verified
5. NestedConditionBehaviors - Nested if/else
6. ErrorBehavior - Error return path
7. NormalBehavior - Success path
8. MultipleReturnBehaviors - Multiple return points
9. GuardedPointerBehaviors - Null check patterns
10. RangeBehaviors - Value range conditions
11. FlagBehaviors - Boolean flag conditions
12. EnumBehaviors - Enum-based dispatch
13. OverlappingBehaviorsWarning - Detect overlap
14. IncompleteBehaviorsWarning - Detect gaps
15. BehaviorInheritance - Virtual function behaviors

## Dependencies
- Enhances ACSLFunctionAnnotator (v1.17.0)
- Synergy: Phase 1 (behaviors include assertions)

## Verification Criteria
- [ ] 15+ tests passing (100%)
- [ ] Behaviors complete (all cases)
- [ ] Behaviors disjoint (no overlap)
- [ ] Each behavior provable independently
