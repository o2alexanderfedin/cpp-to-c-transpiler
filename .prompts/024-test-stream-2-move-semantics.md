<objective>
Implement comprehensive unit tests for C++ move semantics and perfect forwarding in the C++ to C transpiler.

This is Stream 2 of the parallel test expansion plan, targeting 40-60 high-quality unit tests covering rvalue references, move constructors/assignment, std::move, std::forward, and related C++11/14 features. These tests ensure the transpiler correctly handles modern C++ performance optimizations.
</objective>

<context>
**Project**: C++ to C Transpiler
**Work Stream**: Stream 2 - Move Semantics & Perfect Forwarding
**Owner**: Senior Developer
**Timeline**: Week 1-3 (days 3-21)
**Current State**: 492 test functions exist across 66 test files
**Target**: Add 40-60 tests

Read @docs/TEST_PARALLEL_EXECUTION_PLAN.md for the full parallel execution strategy.
Read @docs/TEST_SUITE.md for existing test organization patterns.
Read @CLAUDE.md for project conventions.

**Why This Matters**: Move semantics enable zero-copy performance optimizations in C++. Transpiling to C requires careful resource transfer tracking, ownership semantics, and preventing double-free bugs. These tests validate correctness and safety.
</context>

<requirements>
Create test file `tests/unit/move_semantics/MoveSemanticTranslatorTest.cpp` with 40-60 test cases covering:

1. **Rvalue References** (8-10 tests):
   - Rvalue reference parameters: `void f(T&& x)`
   - Rvalue reference returns: `T&& get()`
   - Lvalue vs rvalue binding rules
   - Reference collapsing

2. **Move Constructor & Assignment** (10-12 tests):
   - Move constructor: `T(T&& other)`
   - Move assignment: `T& operator=(T&& other)`
   - Memberwise move for classes
   - Resource transfer validation
   - Move from temporaries

3. **std::move Usage** (10-12 tests):
   - Explicit std::move calls
   - Move in return statements
   - Move in container operations
   - Move with unique_ptr/shared_ptr
   - Conditional move

4. **Perfect Forwarding** (8-10 tests):
   - std::forward in template functions
   - Universal references (T&&)
   - Forwarding to constructors
   - Variadic template forwarding

5. **Edge Cases** (4-6 tests):
   - Move of moved-from objects
   - Self-move assignment
   - Move noexcept guarantees
   - Implicit vs explicit moves
</requirements>

<implementation>
Follow existing test patterns from @tests/unit/.

**Test Structure**:
```cpp
void test_move_constructor_resource_transfer() {
    // Setup: Class with move constructor
    // Execute: Transpile and verify resource ownership transfer
    // Assert: Original object nullified, new object owns resource
}

void test_std_move_explicit_call() {
    // Test std::move generates proper C resource transfer
}
```

**Key Assertions**:
- Resource ownership correctly transferred (pointers nullified in source)
- No double-free scenarios
- Proper cleanup in moved-from state
- Correct function signatures in generated C

**WHY Safety Matters**: Move semantics bugs cause use-after-free and double-free crashes. Tests must verify the transpiler generates safe C code that maintains ownership semantics.
</implementation>

<integration>
- Owns `tests/unit/move_semantics/` directory exclusively
- Uses shared fixtures library for test utilities
- Feature branch: `test-stream-2-move-semantics`
- No conflicts with other streams (independent directory)
</integration>

<output>
- `./tests/unit/move_semantics/MoveSemanticTranslatorTest.cpp` - 40-60 test functions
- Update `./CMakeLists.txt` - Add test executable
- `./tests/unit/move_semantics/README.md` - Documentation
</output>

<verification>
Before completing:
1. 40-60 test functions ✓
2. All tests pass ✓
3. All 5 requirement categories covered ✓
4. No memory leaks (valgrind clean if applicable) ✓
5. Code review approved ✓

Verify with:
```bash
cmake --build build --target MoveSemanticTranslatorTest
./build/tests/unit/move_semantics/MoveSemanticTranslatorTest
```
</verification>

<success_criteria>
- 40-60 passing tests for move semantics
- Coverage of rvalue refs, move ops, std::move, perfect forwarding, edge cases
- Safe C code generation verified (no double-free, use-after-free)
- Follows project conventions
- Documentation complete
- Stream 2 deliverable complete ✓
</success_criteria>
