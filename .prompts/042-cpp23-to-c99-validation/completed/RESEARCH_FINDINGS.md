# C++23 Compiler Validation Projects - Research Findings

**Date:** 2025-12-24
**Objective:** Identify C++23 test suites and validation projects for transpiler testing

## Executive Summary

After extensive research, I identified 5 primary candidate projects for C++23 validation, ranging from official compiler test suites to community demonstration projects. The best candidates for our transpiler are those balancing comprehensive C++23 coverage with manageable size and clear licensing.

---

## 1. GCC Test Suite (g++.dg/cpp23)

**Repository:** https://github.com/gcc-mirror/gcc
**Path:** gcc/testsuite/g++.dg/cpp23
**License:** GPL-3.0 (with runtime library exception)

### Feature Coverage
**Comprehensive - 261 test files covering:**
- Explicit object parameters (deducing this) - ~60 tests
- if consteval statements - ~13 tests
- Range-based for loop enhancements - ~10 tests
- Subscript operators (multidimensional) - ~15 tests
- Character encoding/UTF-8 - ~12 tests
- Attributes (assume) - ~12 tests
- Class template deduction from inherited constructors - ~10 tests
- Auto as function parameter (auto(x), auto{x}) - ~18 tests
- Constexpr enhancements (non-literal types) - ~19 tests
- Extended floating-point types - ~19 tests
- static operator() - ~8 tests
- Preprocessor (#elifdef, #elifndef) - tests included
- Lambda attributes - tests included
- Miscellaneous: Unicode support, narrowing rules, diagnostics

### Project Metrics
- **Size:** 261 test files (language features only)
- **Complexity:** High - integrated into full GCC build system
- **Last Update:** Continuously updated (active development)
- **Dependencies:** Full GCC build infrastructure, DejaGnu test framework

### Evaluation
**Suitability Score: 9/10**

**Strengths:**
- Most comprehensive C++23 language feature coverage
- Official compiler vendor tests - high quality
- Focused, isolated test cases per feature
- Excellent for validating edge cases and diagnostics
- Well-organized by feature

**Weaknesses:**
- GPL license may be restrictive for some uses
- Tightly coupled to GCC build system
- Tests include GCC-specific directives
- Requires extraction/adaptation for standalone use

**Recommended Integration:**
- **Copy selected tests** - Extract specific test files for features we support
- Create adaptation layer to strip GCC-specific directives
- Use as reference for test case design rather than direct inclusion

---

## 2. MSVC STL Test Suite

**Repository:** https://github.com/microsoft/STL
**License:** Apache-2.0 WITH LLVM-exception

### Feature Coverage
**Comprehensive Standard Library - focuses on C++23 library features:**
- std::expected
- std::mdspan (through libcxx tests)
- Format library enhancements
- Ranges improvements
- std::optional monadic operations
- constexpr std::unique_ptr
- All STL components with C++23 updates

### Project Metrics
- **Size:** Very large (2,652 commits on main, 10.9k stars)
- **Complexity:** Very high - enterprise-grade test infrastructure
- **Last Update:** Continuously updated (Microsoft production)
- **Dependencies:** VS 2026 Insiders, Python 3.14+, VCRuntime, VCStartup, Universal CRT

### Evaluation
**Suitability Score: 6/10**

**Strengths:**
- Excellent Apache-2.0 license with LLVM exception
- Production-quality library tests
- Comprehensive C++23 STL coverage
- Well-documented test infrastructure

**Weaknesses:**
- Massive codebase - difficult to extract specific tests
- Heavy MSVC/Windows dependencies
- Focuses on library, not language features
- Enterprise complexity may be overkill

**Recommended Integration:**
- **Reference only** - Use as validation reference for STL transpilation
- Extract specific std::expected, std::mdspan tests if needed
- Not suitable for direct integration due to size/complexity

---

## 3. scivision/Cpp23-examples

**Repository:** https://github.com/scivision/Cpp23-examples
**License:** MIT

### Feature Coverage
**Moderate - compiler/build system validation focused:**
- Various C++23 syntax features (not enumerated in detail)
- Coroutine demonstrations
- Execution policy examples
- CMake and xmake build integration tests
- Cross-compiler compatibility tests

### Project Metrics
- **Size:** Small - 17 main items, 207 commits
- **Complexity:** Low - simple, focused examples
- **Last Update:** March 8, 2025 (v1.1.0)
- **Popularity:** 116 stars, 16 forks, 3 contributors
- **Dependencies:** CMake or xmake (minimal)

### Evaluation
**Suitability Score: 8/10**

**Strengths:**
- MIT license - very permissive
- Small, manageable codebase
- Multi-compiler testing focus (GCC, Clang, MSVC)
- Clean CMake integration
- Easy to integrate/adapt
- Actively maintained

**Weaknesses:**
- Limited documentation of specific C++23 features covered
- More focused on build system validation than feature comprehensiveness
- Smaller feature coverage compared to compiler vendor suites

**Recommended Integration:**
- **Git submodule or copy** - Excellent candidate for direct integration
- Use as starting point, extend with additional feature tests
- Leverage CMake structure for our test infrastructure

---

## 4. Apress/beginning-cpp23

**Repository:** https://github.com/Apress/beginning-cpp23
**License:** Unknown (likely educational/book companion - requires verification)

### Feature Coverage
**Educational - broad C++23 introduction:**
- Comprehensive book examples covering C++23 features
- Examples and Exercises directories
- Workarounds for compiler limitations
- Practical, didactic approach

### Project Metrics
- **Size:** Medium - 519 commits
- **Complexity:** Low-medium - educational examples
- **Composition:** 97.6% C++, 1.7% C, 0.7% CMake
- **Dependencies:** CMake, modern C++23 compiler
- **Last Update:** Active (book published 2023)

### Evaluation
**Suitability Score: 7/10**

**Strengths:**
- Comprehensive educational coverage
- Practical, real-world examples
- Includes workarounds for compiler compatibility
- Well-structured with examples and exercises
- CMake build system

**Weaknesses:**
- License unclear (book companion code)
- May contain pedagogical rather than validation-focused tests
- Less systematic than compiler test suites
- Need to verify licensing for commercial transpiler use

**Recommended Integration:**
- **Reference** - Use as educational reference and inspiration
- Verify license before any direct use
- Good for understanding practical C++23 usage patterns

---

## 5. LLVM libc++ Test Suite

**Repository:** https://github.com/llvm/llvm-project
**Path:** libcxx/test/std
**License:** Apache-2.0 WITH LLVM-exception

### Feature Coverage
**Comprehensive Standard Library:**
- Organized by C++ standard section numbers
- C++23 library features under active development
- std::expected, std::mdspan, ranges, format library
- Dedicated C++23 status tracking page

### Project Metrics
- **Size:** Very large - part of LLVM monorepo
- **Complexity:** Very high - LLVM infrastructure
- **Last Update:** Continuous (LLVM development)
- **Dependencies:** LLVM build system, llvm-lit test runner
- **Test Runner:** llvm-lit (LLVM Integrated Tester)

### Evaluation
**Suitability Score: 7/10**

**Strengths:**
- Excellent Apache-2.0 license with LLVM exception
- High-quality library conformance tests
- Organized by standard sections
- Comprehensive C++23 library coverage
- Active development

**Weaknesses:**
- Massive LLVM monorepo - difficult to extract
- Complex build infrastructure
- Primarily library, not language features
- Requires significant adaptation for standalone use

**Recommended Integration:**
- **Reference** - Use for STL implementation validation
- Selective extraction for specific library features
- Not suitable for direct integration due to size

---

## Additional Notable Mentions

### kokkos/mdspan
**Repository:** https://github.com/kokkos/mdspan
**License:** Unknown (requires verification)
**Suitability:** 6/10

- Reference implementation of P0009 (std::mdspan)
- Header-only, minimal dependencies
- Excellent for mdspan-specific testing
- Limited to single feature

### martinmoene/expected-lite
**Repository:** https://github.com/martinmoene/expected-lite
**License:** MIT-like (BSL-1.0)
**Suitability:** 6/10

- Single-file header-only std::expected backport
- C++11 and later compatibility
- Good for expected-specific testing
- Limited to single feature

---

## Summary Comparison Table

| Project | License | Size | C++23 Coverage | Integration Difficulty | Suitability |
|---------|---------|------|----------------|----------------------|-------------|
| GCC g++.dg/cpp23 | GPL-3.0 | 261 files | **Excellent (Language)** | Medium | **9/10** |
| MSVC STL | Apache-2.0 | Very Large | **Excellent (Library)** | Very High | 6/10 |
| scivision/Cpp23-examples | MIT | Small | Moderate | **Very Low** | **8/10** |
| Apress/beginning-cpp23 | Unknown | Medium | Good | Low | 7/10 |
| LLVM libc++ | Apache-2.0 | Very Large | **Excellent (Library)** | Very High | 7/10 |

---

## Specific C++23 Feature Coverage Analysis

### Language Features (Priority: High)

| Feature | GCC | MSVC | scivision | Apress | LLVM |
|---------|-----|------|-----------|--------|------|
| Deducing this | ✓✓✓ (60 tests) | ✓ | ? | ✓ | N/A |
| if consteval | ✓✓✓ (13 tests) | ✓ | ? | ✓ | N/A |
| Multidimensional subscript | ✓✓✓ (15 tests) | ✓ | ? | ✓ | N/A |
| static operator() | ✓✓ (8 tests) | ✓ | ? | ✓ | N/A |
| auto(x) and auto{x} | ✓✓✓ (18 tests) | ✓ | ? | ✓ | N/A |
| Literal suffixes for size_t | ✓ | ✓ | ? | ✓ | N/A |
| #elifdef/#elifndef | ✓ | ✓ | ? | ✓ | N/A |
| Attributes on lambdas | ✓ | ✓ | ? | ✓ | N/A |

### Library Features (Priority: Medium for transpiler)

| Feature | GCC | MSVC | scivision | Apress | LLVM |
|---------|-----|------|-----------|--------|------|
| std::expected | ✓ | ✓✓✓ | ? | ✓ | ✓✓✓ |
| std::mdspan | ✓ | ✓✓✓ | ? | ✓ | ✓✓✓ |
| constexpr std::unique_ptr | ✓ | ✓✓✓ | ? | ✓ | ✓✓✓ |
| std::optional monadic ops | ✓ | ✓✓✓ | ? | ✓ | ✓✓✓ |
| Ranges improvements | ✓ | ✓✓✓ | ✓ | ✓ | ✓✓✓ |
| Format library enhancements | ✓ | ✓✓✓ | ? | ✓ | ✓✓✓ |

Legend: ✓✓✓ Comprehensive | ✓✓ Good | ✓ Basic | ? Unknown | N/A Not Applicable

---

## Key Research Sources

### Official Resources
- [ISO C++ Standard](https://isocpp.org/std/the-standard)
- [Clang C++ Status](https://clang.llvm.org/cxx_status.html)
- [GCC C++ Standards Support](https://gcc.gnu.org/projects/cxx-status.html)
- [Microsoft C++ Conformance](https://learn.microsoft.com/en-us/cpp/overview/visual-cpp-language-conformance)
- [libc++ C++23 Status](https://libcxx.llvm.org/Status/Cxx23.html)

### Test Frameworks
- [GCC Testing Documentation](https://gcc.gnu.org/onlinedocs/libstdc++/manual/test.html)
- [Testing libc++](https://libcxx.llvm.org/TestingLibcxx.html)
- [MSVC STL Testing](https://github.com/microsoft/STL)

### Educational Resources
- [C++ Stories - C++23 Examples](https://www.cppstories.com/2024/cpp23_more_examples/)
- [C++ Stories - std::expected](https://www.cppstories.com/2024/expected-cpp23/)
- [C++ Stories - std::mdspan](https://www.cppstories.com/2025/cpp23_mdspan/)
- [Sandor Dargo - Deducing This](https://www.sandordargo.com/blog/2022/02/16/deducing-this-cpp23)
- [Sandor Dargo - if consteval](https://www.sandordargo.com/blog/2022/06/01/cpp23-if-consteval)

### Community Projects
- [awesome-cpp20 (includes C++23)](https://github.com/coderonion/awesome-cpp20)
- [Modern C++ Features Cheatsheet](https://github.com/AnthonyCalandra/modern-cpp-features)

---

## Recommendations Summary

Based on this research, I recommend a **hybrid approach** combining multiple sources:

### Primary Sources (Direct Integration)
1. **GCC g++.dg/cpp23** - Core language feature validation (extracted tests)
2. **scivision/Cpp23-examples** - Build system integration and compiler compatibility

### Secondary Sources (Reference & Selective Integration)
3. **MSVC STL** - Library feature reference (if we transpile STL usage)
4. **Apress/beginning-cpp23** - Practical usage patterns (verify license)

### Tertiary Sources (Documentation Reference)
5. **LLVM libc++** - Alternative library implementation reference
6. **Community projects** - Real-world usage examples

This approach provides:
- Comprehensive C++23 language coverage (GCC)
- Easy integration and build system (scivision)
- Practical examples (Apress)
- Library validation if needed (MSVC/LLVM)
- Permissive licensing where possible (MIT, Apache-2.0)

---

## Next Steps

1. **Verify licenses** for Apress and kokkos/mdspan repositories
2. **Extract GCC tests** for priority C++23 features (deducing this, if consteval, etc.)
3. **Integrate scivision/Cpp23-examples** as git submodule or copy
4. **Create adaptation layer** to run extracted GCC tests in our build system
5. **Design test organization** following our existing test structure
6. **Implement feature-by-feature** validation starting with highest priority C++23 features
