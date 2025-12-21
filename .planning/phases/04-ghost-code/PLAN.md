# Phase 4 Plan: Ghost Code (v1.21.0)

**Phase**: 4 of 7
**Roadmap**: `.planning/ROADMAP.md`
**Brief**: `.planning/BRIEF.md`
**Target Version**: v1.21.0
**Status**: PENDING
**Prerequisite**: Phase 2 recommended (for ghost type invariants)

## Phase Goal

Inject ghost variables and statements for complex specifications that require proof-only bookkeeping. Enable tracking of properties not present in original code.

## Deliverables

### Source Code
- [ ] `include/ACSLGhostCodeInjector.h`
- [ ] `src/ACSLGhostCodeInjector.cpp`

### Tests
- [ ] `tests/ACSLGhostCodeInjectorTest.cpp` (10+ tests)

### CLI Integration
- [ ] Add `--acsl-ghost={off,on}` flag

### Documentation
- [ ] Update `docs/CHANGELOG.md` for v1.21.0
- [ ] Update `README.md`
- [ ] Update `website/src/pages/features.astro`

### Release
- [ ] Git-flow release v1.21.0

## Technical Design

### Ghost Variable Syntax
```c
void findMax(int *arr, int n) {
  //@ ghost int max_seen = INT_MIN;

  int max = arr[0];
  for (int i = 1; i < n; i++) {
    if (arr[i] > max) {
      max = arr[i];
      //@ ghost max_seen = max;
    }
    //@ assert max_seen >= arr[i];
  }
}
```

### Ghost Statement Syntax
```c
//@ ghost {
//@   int sum = 0;
//@   for (int i = 0; i < n; i++) sum += arr[i];
//@ }
```

### Key Features
1. Identify proof-relevant values not in code
2. Insert ghost variables for tracking
3. Generate ghost assignments
4. Ensure ghost code doesn't affect runtime
5. Integration with assertions and invariants

### Test Cases (10+)
1. GhostVariableDeclaration - Simple ghost var
2. GhostAssignment - Ghost var update
3. GhostInLoopInvariant - Ghost var in invariant
4. GhostMaxTracking - Track maximum value
5. GhostSumTracking - Track accumulator
6. GhostCounterTracking - Track occurrences
7. GhostBlockStatement - Multi-statement ghost block
8. GhostConditionalUpdate - Ghost in branch
9. GhostArrayCopy - Ghost array for tracking
10. GhostNoRuntimeImpact - Verify no codegen

## Dependencies
- Synergy: Phase 2 (ghost vars enforce type invariants)
- Synergy: Phase 1 (ghost vars strengthen assertions)

## Verification Criteria
- [ ] 10+ tests passing (100%)
- [ ] Ghost code compiles with Frama-C
- [ ] Ghost code not in executable
- [ ] Performance impact negligible
