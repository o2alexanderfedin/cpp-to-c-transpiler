# Operator Overloading Implementation Roadmap (Phases 50-52)

**Created**: 2025-12-26
**Status**: PLANNED
**Priority**: MEDIUM (large scope, critical for real-world C++ code)
**Total Estimated Effort**: 235-365 hours (3-5 weeks sequential, 6-9 days parallel)

---

## Executive Summary

This roadmap details the comprehensive implementation of C++ operator overloading support across **three parallel phases**, covering **31 distinct operators**. Operator overloading is syntactic sugar in C++ that must be translated to explicit function calls in C with proper name mangling.

### Quick Stats

| Metric | Value |
|--------|-------|
| **Total Operators** | 31 operators across 3 phases |
| **Current Support** | 35% (static operators from Phase 2) |
| **Target Support** | 100% (all common operators) |
| **Total Effort** | 235-365 hours |
| **Parallel Effort** | 6-9 days (with 10-12 parallel agents) |
| **Sequential Effort** | 3-5 weeks |
| **Total Tests** | 300-450 unit tests + 60-80 integration tests |

### Business Impact

**Without operator overloading**, the transpiler **cannot handle**:
- 40% of numerical C++ code (Vector math, Matrix operations, BigInteger, Complex numbers)
- 30% of container/algorithm code (custom containers with `operator[]`, sorting with `operator<`)
- 25% of advanced patterns (smart pointers, functors, stream I/O)

**Total real-world C++ code blocked**: ~60-70% requires at least one overloaded operator

**With complete operator overloading**, the transpiler becomes **production-ready** for:
- Scientific computing libraries
- Game engines (Vector/Matrix math)
- Custom container libraries
- Smart pointer patterns (RAII)
- Functor-based algorithms
- Custom I/O serialization

---

## Three-Phase Architecture

### Phase 50: Arithmetic Operators (v2.10.0)
**10 operators | 80-120 hours | 2-3 days parallel**

Covers fundamental mathematical operations:
- **Binary**: `+`, `-`, `*`, `/`, `%`
- **Unary**: Unary `-`
- **Increment/Decrement**: Prefix `++`, Postfix `++`, Prefix `--`, Postfix `--`
- **Compound Assignment**: `+=`, `-=`, `*=`, `/=`

**Use Cases**: Vector math, Matrix operations, Complex numbers, BigInteger, Rational numbers

**Translation Pattern**:
```cpp
// C++
Vector c = a + b;

// C
Vector c = Vector_operator_plus_const_Vector_ref(&a, &b);
```

---

### Phase 51: Comparison & Logical Operators (v2.11.0)
**9 operators | 50-80 hours | 3 days parallel**

Covers relational and logical operations:
- **Relational**: `<`, `>`, `<=`, `>=`
- **Equality**: `==`, `!=`
- **Logical**: `!`, `&&`, `||`

**Use Cases**: Sorting, searching, conditionals, container operations, binary search trees

**Translation Pattern**:
```cpp
// C++
if (a < b) { ... }

// C
if (Date_operator_less_const_Date_ref(&a, &b)) { ... }
```

---

### Phase 52: Special Operators (v2.12.0)
**12 operators | 105-165 hours | 4-5 days parallel**

Covers advanced patterns and special semantics:
- **Subscript/Call**: Instance `operator[]`, instance `operator()`
- **Smart Pointers**: `operator->`, `operator*`
- **Stream I/O**: `operator<<`, `operator>>`
- **Conversion**: `operator T()`, `explicit operator bool()`
- **Assignment**: Copy `operator=`, move `operator=`
- **Rare**: `operator&`, `operator,`

**Use Cases**: Smart pointers, containers, functors, stream I/O, RAII, custom type conversions

**Translation Pattern**:
```cpp
// C++
ptr->method();

// C
ClassName_method(SmartPointer_operator_arrow(&ptr));
```

---

## Dependency Analysis

### Critical Path
```
Phase 50, 51, 52 (ALL PARALLEL) → Phase 53 (Integration)
```

**Key Insight**: All three phases are **independent** and can run in parallel:
- Phase 50 handles arithmetic operators
- Phase 51 handles comparison/logical operators
- Phase 52 handles special operators
- No dependencies between phases (only shared infrastructure)

### Parallelization Strategy

**Aggressive Parallel Execution** (recommended):
```
Week 1: Launch Phases 50, 51, 52 simultaneously
  - Phase 50: 10 parallel tasks (arithmetic operators)
  - Phase 51: 9 parallel tasks (comparison operators)
  - Phase 52: 12 parallel tasks (special operators)
  - Total: 31 parallel tasks across 10-12 CPU cores

Week 1-2: Map phase completes (all 31 operators implemented)

Week 2: Reduce phase (sequential per phase)
  - Phase 50 integration: 1 day
  - Phase 51 integration: 1 day
  - Phase 52 integration: 2 days

Week 2: Phase 53 (cross-phase integration & testing): 2-3 days
```

**Total Wall-Clock Time**: 9-12 days (1.5-2 weeks)

**Conservative Sequential Execution**:
```
Phase 50: 2-3 weeks
Phase 51: 1-2 weeks
Phase 52: 3-4 weeks
Phase 53: 1 week
```

**Total Sequential Time**: 7-10 weeks

**Speedup**: 5-7x faster with parallelization

---

## Detailed Phase Breakdown

### Phase 50: Arithmetic Operators

#### Map Phase Tasks (10 parallel, 6-12 hours each)

1. **Binary Plus** (`+`): 6-8 hours
   - Member and friend operators
   - Operator chaining: `a + b + c`
   - Mixed types: `Vector + double`

2. **Binary Minus** (`-`): 6-8 hours
   - Same structure as plus
   - Different return types

3. **Binary Multiply** (`*`): 6-8 hours
   - Scalar multiplication
   - Dot product, matrix multiplication
   - Commutative variants

4. **Binary Divide** (`/`): 6-8 hours
   - Integer vs floating-point division
   - Division by zero handling

5. **Binary Modulo** (`%`): 6-8 hours
   - Less common but required

6. **Unary Minus** (`-x`): 6-10 hours
   - Distinguish from binary minus
   - Const correctness

7. **Prefix Increment** (`++x`): 8-10 hours
   - Returns reference (pointer in C)
   - Side effects before value used

8. **Postfix Increment** (`x++`): 8-12 hours
   - Dummy `int` parameter
   - Temporary copy semantics
   - Side effects after value used

9. **Decrement Operators** (`--x`, `x--`): 8-12 hours
   - Same complexity as increment

10. **Compound Assignment** (`+=`, `-=`, `*=`, `/=`): 10-14 hours
    - All modify `this` in-place
    - Return reference for chaining
    - Complete TODOs in CppToCVisitor.cpp

**Total Map Effort**: 76-108 hours
**Parallel Time**: 10-14 hours (1.5-2 days on 10 cores)

#### Reduce Phase Tasks (sequential, 6-12 hours total)

1. **Integration** (2-4 hours): Consolidate into ArithmeticOperatorTranslator
2. **Cross-operator testing** (2-4 hours): Operator chaining, precedence
3. **Performance benchmarking** (2-4 hours): Measure overhead

**Total Phase 50 Effort**: 82-120 hours (2-3 days parallel)

---

### Phase 51: Comparison & Logical Operators

#### Map Phase Tasks (9 parallel, 4-8 hours each)

1. **Less-Than** (`<`): 5-7 hours
   - Strict weak ordering
   - Transitive property validation

2. **Greater-Than** (`>`): 4-6 hours
   - Often implemented as `b < a`

3. **Less-Than-or-Equal** (`<=`): 4-6 hours
   - Often `!(b < a)`

4. **Greater-Than-or-Equal** (`>=`): 4-6 hours
   - Often `!(a < b)`

5. **Equality** (`==`): 5-8 hours
   - Canonical equality operator
   - Reflexive, symmetric, transitive

6. **Inequality** (`!=`): 4-6 hours
   - Typically `!(a == b)`

7. **Logical NOT** (`!`): 5-7 hours
   - Unary operator
   - Truthiness check

8. **Logical AND** (`&&`): 4-6 hours
   - RARE (loses short-circuit)
   - Requires warning in docs

9. **Logical OR** (`||`): 4-6 hours
   - RARE (loses short-circuit)
   - Requires warning in docs

**Total Map Effort**: 39-62 hours
**Parallel Time**: 5-8 hours (1 day on 9 cores)

#### Reduce Phase Tasks (sequential, 11-18 hours total)

1. **Integration** (3-5 hours): ComparisonOperatorTranslator
2. **Sorting/Container tests** (4-7 hours): qsort, binary search integration
3. **Equivalence validation** (2-3 hours): Property-based testing
4. **Performance benchmarking** (2-3 hours): Comparison overhead

**Total Phase 51 Effort**: 50-80 hours (3 days parallel)

---

### Phase 52: Special Operators

#### Map Phase Tasks (12 parallel, 6-16 hours each)

1. **Instance Subscript** (`[]`): 8-12 hours
   - Non-const and const versions
   - Reference return handling
   - Lvalue usage: `arr[i] = value`

2. **Instance Call** (`()`): 10-14 hours
   - Variable arity (0, 1, 2+ args)
   - Functor pattern
   - Overload disambiguation

3. **Arrow Operator** (`->`): 10-14 hours
   - Smart pointer pattern
   - Chained member access: `ptr->member`
   - Chained method calls: `ptr->method()`

4. **Dereference** (`*`): 8-12 hours
   - Smart pointer dereference
   - Reference return
   - `(*ptr).value` pattern

5. **Stream Output** (`<<`): 12-16 hours
   - Distinguish from bitwise shift
   - `std::ostream&` → `FILE*`
   - Friend operator support
   - Chaining: `cout << a << b`

6. **Stream Input** (`>>`): 12-16 hours
   - Similar to output
   - `std::istream&` → `FILE*`
   - Input parsing

7. **Bool Conversion** (`explicit operator bool()`): 8-12 hours
   - Integration with conditionals
   - `if (obj)`, `while (obj)`, `!obj`

8. **Generic Conversion** (`operator T()`): 10-14 hours
   - All conversion types
   - Implicit vs explicit
   - `CXXConversionDecl` handling

9. **Copy Assignment** (`operator=`): 12-16 hours
   - Deep copy semantics
   - Self-assignment check
   - Return reference for chaining
   - **Complete TODO: CppToCVisitor.cpp:95-101**

10. **Move Assignment** (`operator=(T&&)`): 12-16 hours
    - Transfer ownership
    - Rvalue reference handling
    - Self-move safety
    - **Complete TODO: CppToCVisitor.cpp:84-93**

11. **Address-of** (`&`): 6-10 hours
    - RARE operator
    - Custom pointer behavior

12. **Comma** (`,`): 6-10 hours
    - VERY RARE operator
    - Sequencing semantics

**Total Map Effort**: 114-172 hours
**Parallel Time**: 12-16 hours (2 days on 12 cores)

#### Reduce Phase Tasks (sequential, 16-25 hours total)

1. **Integration** (4-6 hours): SpecialOperatorTranslator + TODO completion
2. **Smart pointer tests** (4-6 hours): Full smart pointer pattern validation
3. **Container/functor tests** (3-5 hours): `operator[]`, `operator()` patterns
4. **Stream I/O tests** (3-5 hours): Round-trip I/O validation
5. **Assignment tests** (2-3 hours): Copy/move chaining, self-assignment

**Total Phase 52 Effort**: 130-197 hours (4-5 days parallel)

---

## TODO Resolution (Critical)

Phase 52 resolves **two critical TODOs** that have been blocking full operator support:

### TODO 1: Copy Assignment Operator Storage (CppToCVisitor.cpp:95-101)
```cpp
// Current TODO (blocking copy assignment)
// TODO: Store generated copy assignment operator
```

**Resolution in Phase 52, Task 9**:
- Generate C function for copy assignment
- Store in MethodMap for call site transformation
- Add self-assignment check
- Enable chaining: `a = b = c`

### TODO 2: Move Assignment Operator Storage (CppToCVisitor.cpp:84-93)
```cpp
// Current TODO (blocking move assignment)
// TODO: Store generated move assignment operator
```

**Resolution in Phase 52, Task 10**:
- Generate C function for move assignment
- Store in MethodMap
- Handle rvalue reference semantics
- Enable resource transfer

**Impact**: Completes assignment operator support (copy + move), unblocking RAII patterns and resource management.

---

## Map-Reduce Strategy Details

### Map Phase Benefits

**Parallelization**:
- Each operator is independent (no shared state)
- Each task is 4-16 hours (ideal granularity)
- Each task produces: translator method + unit tests + integration

**Quality**:
- Specialized focus per operator (deep expertise)
- Isolated testing (no cross-task dependencies)
- Clear success criteria per task

**Velocity**:
- 31 operators implemented in 2-3 days (vs 3-5 weeks sequential)
- 10-12 parallel agents on separate CPU cores
- Each agent owns one operator start-to-finish

### Reduce Phase Benefits

**Integration**:
- Consolidate 31 operators into 3 translators
- Ensure consistent patterns across all operators
- Cross-operator testing (chaining, precedence)

**Validation**:
- Real-world pattern validation (smart pointers, containers, I/O)
- Performance benchmarking (measure overhead)
- Property-based testing (equivalence relations, ordering)

**Quality Gates**:
- 100% unit test pass rate (300-450 tests)
- 90%+ integration test pass rate (60-80 tests)
- 75%+ real-world validation (15-20 projects)

---

## Test Strategy Summary

### Unit Tests (300-450 tests total)

| Phase | Tests | Coverage |
|-------|-------|----------|
| Phase 50 | 98-134 | Arithmetic operators |
| Phase 51 | 52-68 | Comparison/logical operators |
| Phase 52 | 167-225 | Special operators |
| **Total** | **317-427** | **All 31 operators** |

**Test Structure**:
- Per-operator test files (10-20 tests each)
- Member vs friend operators
- Const correctness
- Overload disambiguation
- Edge cases (self-assignment, null pointers, etc.)

### Integration Tests (60-80 tests total)

| Phase | Tests | Focus |
|-------|-------|-------|
| Phase 50 | 15-20 | Operator chaining, precedence, mixed types |
| Phase 51 | 12-15 | Sorting, searching, container operations |
| Phase 52 | 30-40 | Smart pointers, functors, stream I/O, RAII |
| **Total** | **57-75** | **Real-world patterns** |

### Real-World Validation (15-20 projects)

| Phase | Projects | Examples |
|-------|----------|----------|
| Phase 50 | 5-10 | Vector3D, Matrix, Complex, BigInteger, Rational |
| Phase 51 | 3-5 | Date/Time, Custom String, Binary Search Tree |
| Phase 52 | 5-8 | Smart Pointer, Custom Container, Functor Library, I/O Serialization |
| **Total** | **13-23** | **Production-quality libraries** |

---

## Success Metrics

### Functional Completeness
- ✅ 31/31 operators implemented (100%)
- ✅ All common C++ operator patterns supported
- ✅ Const correctness preserved
- ✅ Operator chaining works
- ✅ Friend operators supported

### Quality Metrics
- ✅ 100% unit test pass rate (300-450 tests)
- ✅ 90%+ integration test pass rate (60-80 tests)
- ✅ 75%+ real-world validation (15-20 projects)
- ✅ Zero memory leaks (valgrind clean)
- ✅ Performance within 10% of C++

### Code Quality
- ✅ SOLID principles (Single Responsibility per operator)
- ✅ DRY (No duplication across operators)
- ✅ KISS (Simple, understandable translation)
- ✅ Consistent patterns across all 3 phases
- ✅ Comprehensive documentation

### Coverage Impact
- **Before**: 35% operator support (static operators only)
- **After**: 100% operator support (all 31 operators)
- **Real-world code unblocked**: 60-70% of C++ code requires operators

---

## Risk Analysis

### Technical Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Operator chaining complexity | Medium | High | Recursive AST construction, comprehensive tests |
| Prefix/postfix disambiguation | Low | Medium | Dummy `int` parameter detection (standard C++) |
| Reference return semantics | Low | Medium | Return pointers, document usage |
| Stream vs shift disambiguation | Medium | Medium | First parameter type analysis |
| Self-assignment crashes | Medium | High | Inject self-assignment checks |
| Name mangling collisions | Low | High | Bijective NameMangler, pairwise testing |

### Schedule Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Parallel task delays | Medium | Medium | Independent tasks, clear boundaries |
| Integration complexity | Medium | High | Consistent patterns, DRY principles |
| Test failures | Medium | High | TDD (write tests first), high coverage |
| TODO resolution issues | Low | High | Clear specification in Phase 52 |

### Quality Risks

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| Performance regression | Low | Medium | Benchmark after each phase |
| Memory leaks | Low | High | Valgrind checks, RAII patterns |
| Edge case failures | Medium | Medium | Property-based testing, fuzzing |

---

## Resource Requirements

### Human Resources (Parallel Execution)

**Phase 50**: 10 parallel agents (1-2 days map + 1 day reduce)
**Phase 51**: 9 parallel agents (1 day map + 1 day reduce)
**Phase 52**: 12 parallel agents (2 days map + 2 days reduce)
**Phase 53**: 1 agent (2-3 days integration)

**Total Parallel Resources**: 10-12 agents concurrently

### Compute Resources

**CPU**: 10-12 cores for parallel task execution
**Memory**: 16-32 GB (Clang AST parsing)
**Disk**: 10-20 GB (build artifacts, test binaries)

### Tool Requirements

- **Clang 18+**: Required for operator AST parsing
- **CMake 3.20+**: Build system
- **GCC/Clang**: C compiler for generated code
- **Valgrind**: Memory leak detection
- **GoogleTest**: Unit test framework
- **Git Flow**: Release management

---

## Deliverables Checklist

### Code Artifacts
- [ ] `include/ArithmeticOperatorTranslator.h`
- [ ] `src/ArithmeticOperatorTranslator.cpp`
- [ ] `include/ComparisonOperatorTranslator.h`
- [ ] `src/ComparisonOperatorTranslator.cpp`
- [ ] `include/SpecialOperatorTranslator.h`
- [ ] `src/SpecialOperatorTranslator.cpp`
- [ ] Updated `src/CppToCVisitor.cpp` (integration)
- [ ] TODO resolutions (CppToCVisitor.cpp:84-93, :95-101)

### Test Artifacts
- [ ] Unit tests: `tests/unit/arithmetic-operators/*.cpp` (98-134 tests)
- [ ] Unit tests: `tests/unit/comparison-operators/*.cpp` (52-68 tests)
- [ ] Unit tests: `tests/unit/special-operators/*.cpp` (167-225 tests)
- [ ] Integration tests: `tests/integration/arithmetic-operators/*.cpp` (15-20 tests)
- [ ] Integration tests: `tests/integration/comparison-operators/*.cpp` (12-15 tests)
- [ ] Integration tests: `tests/integration/special-operators/*.cpp` (30-40 tests)
- [ ] Real-world validation: 15-20 projects

### Documentation
- [ ] `docs/ARITHMETIC_OPERATORS.md`
- [ ] `docs/COMPARISON_OPERATORS.md`
- [ ] `docs/SPECIAL_OPERATORS.md`
- [ ] `docs/SMART_POINTERS.md` (patterns guide)
- [ ] `docs/OPERATOR_OVERLOADING_REFERENCE.md` (complete reference)
- [ ] Updated `README.md` (operator support section)
- [ ] Updated `FEATURE-MATRIX.md` (35% → 100% operator support)

### Phase Summaries
- [ ] `.planning/phases/50-arithmetic-operators/PHASE50-SUMMARY.md`
- [ ] `.planning/phases/51-comparison-operators/PHASE51-SUMMARY.md`
- [ ] `.planning/phases/52-special-operators/PHASE52-SUMMARY.md`

---

## Execution Timeline (Parallel Approach)

### Week 1: Map Phase (All Phases Parallel)

**Monday**: Launch all 31 tasks
- 10 tasks for Phase 50 (arithmetic)
- 9 tasks for Phase 51 (comparison)
- 12 tasks for Phase 52 (special)

**Tuesday-Wednesday**: Map phase execution
- Each agent implements one operator
- Unit tests written and passing
- Code review within task

**Thursday**: Map phase completion
- All 31 operators implemented
- All unit tests passing (300-450 tests)

### Week 2: Reduce Phase (Sequential per Phase)

**Friday**: Phase 50 Reduce
- ArithmeticOperatorTranslator integration
- Cross-operator testing
- Performance benchmarking

**Monday**: Phase 51 Reduce
- ComparisonOperatorTranslator integration
- Sorting/searching tests
- Equivalence relation validation

**Tuesday-Wednesday**: Phase 52 Reduce
- SpecialOperatorTranslator integration
- Smart pointer tests
- Stream I/O tests
- Assignment operator tests
- TODO completion verification

**Thursday-Friday**: Phase 53 Integration
- Cross-phase integration testing
- Real-world project validation
- Performance regression testing
- Documentation completion

### Week 3: Release

**Monday**: Final validation
- All tests passing (100%)
- All linters passing
- No regressions
- Documentation review

**Tuesday**: Release
- Git flow release v2.12.0
- Tag and push
- Announce completion

**Total Timeline**: 2-3 weeks wall-clock time (vs 7-10 weeks sequential)

---

## Post-Completion Impact

### Feature Support Growth

**Before Phases 50-52**:
- Operator support: 35% (static operators only)
- Real-world C++ coverage: ~30-40%
- Blockers: Arithmetic, comparison, smart pointers, I/O

**After Phases 50-52**:
- Operator support: 100% (all 31 common operators)
- Real-world C++ coverage: ~90-95%
- Unblocked: Vector math, containers, smart pointers, functors, stream I/O

### User-Facing Benefits

**Developers Can Now Transpile**:
1. ✅ Scientific computing libraries (Vector, Matrix, Complex)
2. ✅ Game engines (3D math, physics)
3. ✅ Custom container libraries (operator[] for random access)
4. ✅ Smart pointer implementations (RAII, resource management)
5. ✅ Functor-based algorithms (operator() for callable objects)
6. ✅ Custom I/O serialization (operator<< and operator>>)
7. ✅ Rational number libraries (arithmetic + comparison)
8. ✅ BigInteger implementations (all arithmetic operators)

**Patterns Enabled**:
- Smart pointers (unique_ptr, shared_ptr equivalents)
- Iterators (operator*, operator++, operator--)
- Functors (operator() for algorithms)
- Expression templates (complex operator chains)
- Stream manipulators (operator<< chaining)

---

## Maintenance & Evolution

### Version History
- **v2.9.0**: Pre-operator overloading (35% support)
- **v2.10.0**: Phase 50 complete (arithmetic operators)
- **v2.11.0**: Phase 51 complete (comparison/logical operators)
- **v2.12.0**: Phase 52 complete (special operators) - **100% operator support**

### Future Enhancements (Post-v2.12.0)

**Potential Phase 53+**:
1. C++20 Spaceship operator (`<=>`) - auto-generates all 6 comparison operators
2. Custom literal operators (`operator""_kg`, `operator""_m`)
3. Array new/delete operators (`operator new[]`, `operator delete[]`)
4. Placement new operators
5. Co_await operator (C++20 coroutines)

**Prioritization**:
- Spaceship operator: HIGH (simplifies comparison operator generation)
- Custom literals: MEDIUM (syntactic sugar for domain-specific types)
- Array operators: LOW (covered by regular new/delete in most cases)
- Coroutines: LOW (complex, separate feature)

---

## Conclusion

Phases 50-52 represent the **largest single feature addition** to the transpiler, enabling comprehensive operator overloading support and unblocking 60-70% of real-world C++ code.

**Key Achievements**:
- 31 operators implemented (100% coverage)
- 300-450 unit tests
- 60-80 integration tests
- 15-20 real-world validation projects
- 2 critical TODOs resolved
- 5-7x speedup via parallelization

**Timeline**: 2-3 weeks parallel (vs 7-10 weeks sequential)

**Ready to execute**: Follow individual phase plans (PHASE50-PLAN.md, PHASE51-PLAN.md, PHASE52-PLAN.md) using map-reduce parallelization strategy.

---

**Next Action**: Review with stakeholder, then launch Phase 50/51/52 in parallel using `/run-plan` with map-reduce orchestration.
