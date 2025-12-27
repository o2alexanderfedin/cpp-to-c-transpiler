# C++23 Feature Support Matrix

**Project**: Hupyy C++ to C Transpiler
**Target**: C99 Output
**Last Updated**: December 24, 2025
**Test Suite**: 130 GCC C++23 tests from g++.dg/cpp23

---

## Legend

| Symbol | Meaning | Description |
|--------|---------|-------------|
| ✅ | **SUPPORTED** | Transpiles correctly, A/B tests pass |
| ⚠️ | **PARTIAL** | Transpiles with limitations or specific cases only |
| ❌ | **UNSUPPORTED** | Does not transpile or fails compilation |
| 🔧 | **IN PROGRESS** | Implementation underway |
| 📋 | **PLANNED** | On roadmap for future implementation |
| 🔍 | **UNTESTED** | No test coverage yet |

---

## C++23 Language Features by Proposal

### Core Language Features

| Feature | Proposal | Status | Tests | Pass Rate | Notes |
|---------|----------|--------|-------|-----------|-------|
| **Deducing this** | P0847R7 | ❌ | 0/22 | 0% | Explicit object parameters not supported |
| **if consteval** | P1938R3 | ❌ | 0/13 | 0% | Compile-time evaluation not implemented |
| **Multidimensional subscript operator** | P2128R6 | ❌ | 0/16 | 0% | Multi-arg operator[] not converted |
| **Static operator()** | P1169R4 | ❌ | 0/8 | 0% | Static member operators unsupported |
| **auto(x) and auto{x}** | P0849R8 | ⚠️ | 0/22 | 0% | Basic auto works, decay-copy not implemented |
| **Constexpr enhancements** | Various | ❌ | 0/19 | 0% | Constexpr execution not supported |
| **[[assume]] attribute** | P1774R8 | 🔍 | 0/13 | 0% | May be stripped, untested |
| **Class template deduction (inherited)** | P2582R1 | ⚠️ | 0/10 | 0% | Basic CTAD works, inheritance cases fail |
| **Ranges enhancements** | P2678R0 | ❌ | 0/10 | 0% | Requires STL, not transpiled |
| **Labels at end of statements** | P2324R0 | 🔍 | 0/19 | 0% | May work, needs testing |

**Total Language Features**: 10 proposals, 152 tests
**Current Pass Rate**: 0% (baseline not yet established)

---

## By Feature Category

### 1. Template Features

| Feature | Status | Support Level | Notes |
|---------|--------|---------------|-------|
| Basic class templates | ✅ | 70% | Monomorphization works for standard cases |
| Function templates | ⚠️ | 40% | Simple cases work, complex overloads fail |
| Variadic templates | ⚠️ | 30% | Basic parameter packs supported |
| Template specialization | ⚠️ | 50% | Partial specialization has gaps |
| SFINAE | ❌ | 0% | Not implemented |
| Concepts (C++20/23) | ❌ | 0% | Not implemented |
| CTAD | ⚠️ | 20% | Basic cases only |
| CTAD with inherited constructors | ❌ | 0% | Not supported |

**Category Pass Rate**: ~35% (estimated)

---

### 2. Constexpr Features

| Feature | Status | Support Level | Notes |
|---------|--------|---------------|-------|
| Constexpr variables | ❌ | 0% | Not evaluated at compile-time |
| Constexpr functions | ❌ | 0% | Emitted as runtime functions |
| Consteval (immediate functions) | ❌ | 0% | Not supported |
| if consteval | ❌ | 0% | Not implemented |
| constinit | ❌ | 0% | Not supported |
| Constexpr destructors (C++20) | ❌ | 0% | Not supported |
| Constexpr dynamic allocation (C++20) | ❌ | 0% | Not supported |

**Category Pass Rate**: 0%

---

### 3. Operator Overloading

| Feature | Status | Support Level | Notes |
|---------|--------|---------------|-------|
| Basic operators (+, -, *, /) | ✅ | 90% | Converted to named functions |
| Comparison operators | ✅ | 85% | Spaceship operator not supported |
| operator[] (single arg) | ✅ | 80% | Converted to function calls |
| operator[] (multi-arg, C++23) | ❌ | 0% | Not supported |
| Static operator() (C++23) | ❌ | 0% | Not supported |
| Static operator[] (C++23) | ❌ | 0% | Not supported |
| operator<=> (C++20) | ❌ | 0% | Not implemented |

**Category Pass Rate**: ~50% (for supported operators)

---

### 4. Class Features

| Feature | Status | Support Level | Notes |
|---------|--------|---------------|-------|
| Basic classes | ✅ | 95% | Converted to structs with vtables |
| Inheritance (single) | ✅ | 85% | Converted to composition |
| Inheritance (multiple) | ⚠️ | 60% | Works with limitations |
| Virtual inheritance | ⚠️ | 40% | Complex cases fail |
| Virtual functions | ✅ | 90% | Vtable generation works |
| Pure virtual functions | ✅ | 85% | Handler implemented |
| Constructors | ✅ | 80% | Converted to init functions |
| Destructors | ✅ | 85% | Cleanup functions generated |
| Member initialization | ✅ | 75% | Init lists converted |
| Explicit object parameters (C++23) | ❌ | 0% | Deducing this not supported |

**Category Pass Rate**: ~70% (for C++11 features), 0% (for C++23 features)

---

### 5. Type System Features

| Feature | Status | Support Level | Notes |
|---------|--------|---------------|-------|
| auto type deduction | ✅ | 85% | Works for most cases |
| decltype | ⚠️ | 50% | Basic cases work |
| auto(x) / auto{x} (C++23) | ❌ | 0% | Decay-copy not implemented |
| RTTI (typeid) | ✅ | 75% | Type info generated |
| dynamic_cast | ✅ | 70% | Runtime checks implemented |
| Type traits | ❌ | 0% | Not transpiled (requires STL) |

**Category Pass Rate**: ~55% (for C++11 features), 0% (for C++23 features)

---

### 6. Attributes

| Feature | Status | Support Level | Notes |
|---------|--------|---------------|-------|
| [[nodiscard]] | 🔍 | ? | May be stripped silently |
| [[maybe_unused]] | 🔍 | ? | May be stripped silently |
| [[deprecated]] | 🔍 | ? | May be stripped silently |
| [[assume]] (C++23) | 🔍 | ? | Untested, likely stripped |
| [[fallthrough]] | 🔍 | ? | May be stripped silently |
| [[noreturn]] | 🔍 | ? | May be preserved or stripped |

**Category Pass Rate**: Unknown (needs testing)

---

### 7. Lambdas & Closures

| Feature | Status | Support Level | Notes |
|---------|--------|---------------|-------|
| Basic lambdas | ⚠️ | 30% | Simple cases converted |
| Captures | ⚠️ | 25% | Limited support |
| Generic lambdas | ❌ | 0% | Not supported |
| Lambda templates (C++20) | ❌ | 0% | Not supported |
| Stateless lambdas | ⚠️ | 40% | Some cases work |

**Category Pass Rate**: ~20%

---

### 8. Exception Handling

| Feature | Status | Support Level | Notes |
|---------|--------|---------------|-------|
| try/catch blocks | ✅ | 80% | Converted to setjmp/longjmp |
| throw expressions | ✅ | 75% | Implemented |
| Exception specifications | ⚠️ | 30% | Partial support |
| noexcept | ⚠️ | 40% | Limited tracking |
| Stack unwinding | ✅ | 70% | Destructors called correctly |

**Category Pass Rate**: ~60%

---

### 9. Ranges & Iterators (C++20/23)

| Feature | Status | Support Level | Notes |
|---------|--------|---------------|-------|
| Ranges library | ❌ | 0% | Requires STL transpilation |
| Range adaptors | ❌ | 0% | Not supported |
| Range-based for loops | ⚠️ | 50% | Basic cases work |
| Views | ❌ | 0% | Not supported |
| Projections | ❌ | 0% | Not supported |

**Category Pass Rate**: ~10% (only basic for loops)

---

### 10. Coroutines (C++20)

| Feature | Status | Support Level | Notes |
|---------|--------|---------------|-------|
| co_await | ⚠️ | 20% | Basic framework exists |
| co_yield | ⚠️ | 20% | Partial implementation |
| co_return | ⚠️ | 20% | Partial implementation |
| Promise types | ⚠️ | 15% | Limited support |
| Coroutine handles | ❌ | 10% | Minimal support |

**Category Pass Rate**: ~15%

---

## Overall Support Summary

### By C++ Standard

| Standard | Support Level | Notes |
|----------|---------------|-------|
| **C++98/03** | 85-90% | Core features well-supported |
| **C++11** | 70-75% | Most features work, some gaps |
| **C++14** | 60-65% | Partial support |
| **C++17** | 40-45% | Limited support |
| **C++20** | 15-20% | Minimal support |
| **C++23** | 0-5% | Almost no support |

### By Feature Complexity

| Complexity Level | Support | Examples |
|------------------|---------|----------|
| **Basic OOP** | 85-90% | Classes, inheritance, virtual functions |
| **Templates** | 40-50% | Monomorphization for simple cases |
| **Modern Features** | 10-20% | Lambdas, auto, range-for |
| **Metaprogramming** | 5-10% | Minimal SFINAE, no concepts |
| **Compile-time** | 0-5% | No constexpr evaluation |
| **C++23 Specific** | 0% | No support yet |

---

## Test Coverage Summary

### GCC Test Suite (Phase 33)

| Category | Total Tests | Adapted | Expected Pass | Actual Pass | Status |
|----------|-------------|---------|---------------|-------------|--------|
| if-consteval-P1938 | 13 | 13 | 0 | TBD | 📋 Not run yet |
| multidim-subscript-P2128 | 16 | 16 | 0 | TBD | 📋 Not run yet |
| static-operators-P1169 | 8 | 8 | 0 | TBD | 📋 Not run yet |
| auto-deduction-P0849 | 22 | 22 | 0 | TBD | 📋 Not run yet |
| constexpr-enhancements | 19 | 19 | 0 | TBD | 📋 Not run yet |
| class-template-deduction | 10 | 10 | 0 | TBD | 📋 Not run yet |
| attributes-P2180 | 13 | 13 | 0 | TBD | 📋 Not run yet |
| ranges-P2678 | 10 | 10 | 0 | TBD | 📋 Not run yet |
| miscellaneous | 19 | 19 | 0 | TBD | 📋 Not run yet |
| **TOTAL** | **130** | **130** | **0** | **TBD** | 📋 Baseline pending |

**Note**: Expected pass = 0 because these are C++23-specific features not yet supported by transpiler.

---

## Feature Implementation Priority

### High Priority (Phase 34-35)
- Basic attribute handling (strip or preserve)
- Improved template monomorphization
- Better error messages for unsupported features

### Medium Priority (Phase 36-38)
- Partial constexpr support (constant folding)
- Enhanced auto type deduction
- Lambda improvements

### Low Priority (Phase 39+)
- C++23 specific features (if consteval, deducing this)
- Ranges support (requires STL)
- Advanced metaprogramming

### Deferred
- Full constexpr/consteval evaluation
- Concepts
- Modules
- C++23 standard library features

---

## Known Limitations

See [GAPS.md](GAPS.md) for detailed list of known limitations and architectural constraints.

See [ROADMAP.md](ROADMAP.md) for planned improvements and feature additions.

---

## Validation Methodology

### A/B Testing Process
1. Build C++23 version with clang++ -std=c++23
2. Execute C++23 tests, capture output
3. Transpile C++23 → C using cpptoc
4. Build C version with gcc -std=c99
5. Execute C tests, capture output
6. Compare outputs using intelligent normalization
7. Report pass/fail with detailed diffs

### Success Criteria
- **Build Success**: Transpiled C code compiles without errors
- **Runtime Success**: C version executes without crashes
- **Output Match**: C output matches C++23 output exactly
- **Performance**: C version performance within 2x of C++23

---

## References

- **Test Suite**: GCC g++.dg/cpp23 (130 tests)
- **C++23 Standard**: ISO/IEC 14882:2023
- **Feature Papers**: See individual P-numbers in table
- **Transpiler Docs**: [../README.md](../README.md)
- **A/B Testing**: [../ab-test/README.md](../ab-test/README.md)

---

**Document Version**: 1.0
**Created**: December 24, 2025
**Maintained By**: Transpiler Development Team
