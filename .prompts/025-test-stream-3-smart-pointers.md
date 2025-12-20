<objective>
Implement comprehensive unit tests for C++ smart pointers (unique_ptr, shared_ptr, weak_ptr) and RAII patterns in the C++ to C transpiler.

This is Stream 3 of the parallel test expansion plan, targeting 80-100 high-quality unit tests. This is the largest stream requiring 2 mid-level developers working together to cover smart pointer translation, reference counting, and RAII resource management.
</objective>

<context>
**Project**: C++ to C Transpiler
**Work Stream**: Stream 3 - Smart Pointers & RAII
**Owners**: 2 Mid-Level Developers
**Timeline**: Week 1-4 (days 3-28)
**Current State**: 492 test functions, RAII tests exist but need smart pointer coverage
**Target**: Add 80-100 tests (largest stream)

Read @docs/TEST_PARALLEL_EXECUTION_PLAN.md for coordination strategy.
Read @docs/TEST_SUITE.md for existing RAII test patterns.
Read @tests/unit/raii/ for existing RAII integration tests to extend.

**Why This Matters**: Smart pointers are the foundation of modern C++ memory safety. Transpiling requires implementing reference counting, unique ownership, and weak references in C - complex logic that must be tested exhaustively.
</context>

<requirements>
Create test files (split between 2 developers):

**Developer A** - `tests/unit/smart_pointers/UniquePtrTest.cpp` (25-30 tests):
1. unique_ptr creation and ownership (5-7 tests)
2. unique_ptr moves (no copies) (8-10 tests)
3. make_unique support (5-7 tests)
4. Custom deleters (5-7 tests)

**Developer B** - `tests/unit/smart_pointers/SharedPtrTest.cpp` (35-40 tests):
1. shared_ptr creation and ref counting (10-12 tests)
2. make_shared support (8-10 tests)
3. Cyclic references and weak_ptr (10-12 tests)
4. Thread-safe ref counting (7-10 tests)

**Both Developers** - `tests/unit/smart_pointers/RaiiIntegrationTest.cpp` (20-30 tests):
1. Smart pointers with RAII (file, network, locks) (10-15 tests)
2. Exception safety with smart pointers (10-15 tests)

Total: 80-100 tests across 3 files
</requirements>

<implementation>
**Test Organization**:
```cpp
// Developer A focuses on unique_ptr
void test_unique_ptr_creation_takes_ownership() {}
void test_unique_ptr_move_constructor() {}
void test_unique_ptr_reset_deletes_resource() {}

// Developer B focuses on shared_ptr
void test_shared_ptr_ref_count_increment() {}
void test_shared_ptr_copy_increments() {}
void test_weak_ptr_breaks_cycle() {}

// Both work on integration
void test_raii_file_smart_pointer() {}
void test_exception_safety_shared_ptr() {}
```

**Key Assertions**:
- Reference counts correctly maintained
- Resources freed exactly once
- Unique ownership enforced (no copies)
- Weak pointers don't prevent deletion
- Thread-safe reference counting (atomic ops in generated C)

**WHY 2 Developers**: 80-100 tests is too much for one person in the timeline. Division by smart pointer type (unique vs shared) creates clean work separation with minimal coordination.
</implementation>

<integration>
**Work Coordination**:
- Developer A: unique_ptr + setup shared infrastructure
- Developer B: shared_ptr/weak_ptr + RAII integration
- Both: Integration tests (pair programming recommended)
- Daily sync: Resolve any fixture library conflicts
- Shared branch: `test-stream-3-smart-pointers`

**Dependencies**:
- Uses fixtures library (Day 1-2)
- Extends existing RAII tests from @tests/unit/raii/
- No conflicts with other streams
</integration>

<output>
- `./tests/unit/smart_pointers/UniquePtrTest.cpp` - 25-30 tests (Dev A)
- `./tests/unit/smart_pointers/SharedPtrTest.cpp` - 35-40 tests (Dev B)
- `./tests/unit/smart_pointers/RaiiIntegrationTest.cpp` - 20-30 tests (Both)
- Update `./CMakeLists.txt` - Add 3 test executables
- `./tests/unit/smart_pointers/README.md` - Document organization
</output>

<verification>
Before completing:
1. 80-100 test functions implemented ✓
2. All tests pass independently ✓
3. Reference counting logic verified (no leaks) ✓
4. Thread safety tests pass (if applicable) ✓
5. Integration with existing RAII tests ✓
6. Both developers' code reviewed ✓

Run verification:
```bash
cmake --build build --target UniquePtrTest SharedPtrTest RaiiIntegrationTest
./build/tests/unit/smart_pointers/UniquePtrTest
./build/tests/unit/smart_pointers/SharedPtrTest
./build/tests/unit/smart_pointers/RaiiIntegrationTest
grep -r "^void test_" tests/unit/smart_pointers/ | wc -l  # Should be 80-100
```
</verification>

<success_criteria>
- 80-100 passing tests across 3 files
- unique_ptr, shared_ptr, weak_ptr fully covered
- Reference counting correctness verified
- Memory safety guaranteed (no leaks, no double-free)
- 2 developers coordinated successfully
- Stream 3 deliverable complete (largest stream) ✓
</success_criteria>
