# Phase 6 Plan: Advanced Memory Predicates (v1.23.0)

**Phase**: 6 of 7
**Roadmap**: `.planning/ROADMAP.md`
**Brief**: `.planning/BRIEF.md`
**Target Version**: v1.23.0
**Status**: PENDING
**Prerequisite**: Phase 1 recommended (assertions for memory ops)

## Phase Goal

Add advanced memory reasoning predicates (`\allocable`, `\freeable`, `\block_length`, `\base_addr`) to enable verification of memory lifecycle and pointer arithmetic safety.

## Deliverables

### Source Code
- [ ] `include/ACSLMemoryPredicateAnalyzer.h`
- [ ] `src/ACSLMemoryPredicateAnalyzer.cpp`
- [ ] Enhancement to ACSLFunctionAnnotator

### Tests
- [ ] `tests/ACSLMemoryPredicateAnalyzerTest.cpp` (10+ tests)

### CLI Integration
- [ ] Add `--acsl-memory-predicates={off,on}` flag

### Documentation
- [ ] Update `docs/CHANGELOG.md` for v1.23.0
- [ ] Update `README.md`
- [ ] Update `website/src/pages/features.astro`

### Release
- [ ] Git-flow release v1.23.0

## Technical Design

### Memory Predicate Syntax

#### Allocable
```c
/*@ requires \allocable(size);
  @ ensures \valid(\result + (0..size-1));
  @ ensures \fresh(\result, size);
  @ ensures \block_length(\result) == size;
  @*/
void* allocate(size_t size) {
  return malloc(size);
}
```

#### Freeable
```c
/*@ requires \freeable(ptr);
  @ ensures !\valid(ptr);
  @*/
void deallocate(void *ptr) {
  free(ptr);
}
```

#### Block Length
```c
/*@ requires \valid(ptr);
  @ requires offset < \block_length(ptr);
  @ ensures \valid(\result);
  @*/
void* offset_pointer(void *ptr, size_t offset) {
  return (char*)ptr + offset;
}
```

#### Base Address
```c
/*@ requires \valid(ptr);
  @ ensures \result == \base_addr(ptr);
  @ ensures \valid(\result);
  @*/
void* get_base(void *ptr) {
  return ptr - ((uintptr_t)ptr % alignment);
}
```

### Key Features
1. Track memory allocation sites
2. Generate `\allocable` preconditions for allocators
3. Generate `\freeable` preconditions for deallocators
4. Add `\block_length` ensures clauses
5. Use `\base_addr` for pointer arithmetic
6. Inter-procedural tracking (when possible)

### Test Cases (10+)
1. AllocablePrecondition - malloc/new requires
2. FreeablePrecondition - free/delete requires
3. BlockLengthPostcondition - Allocation size tracking
4. BaseAddressComputation - Base pointer reasoning
5. PointerArithmeticSafety - Offset within bounds
6. CustomAllocator - Pool/arena allocators
7. PartialAllocation - Struct member allocation
8. ReallocTracking - Reallocation size update
9. DoubleFreeDetection - Freeable only once
10. UseAfterFreeDetection - Not valid after free

## Dependencies
- Enhances ACSLFunctionAnnotator (v1.17.0)
- Synergy: Phase 1 (assertions for memory ops)

## Verification Criteria
- [ ] 10+ tests passing (100%)
- [ ] Memory safety provable (no double-free, use-after-free)
- [ ] Allocation size tracking accurate
- [ ] Pointer arithmetic verified within bounds
