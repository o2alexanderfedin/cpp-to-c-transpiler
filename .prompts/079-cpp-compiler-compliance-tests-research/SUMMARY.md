# C++ Compiler Compliance Test Suites - Executive Summary

**Date**: January 7, 2026
**Research Focus**: Identifying test suites for C++ compiler compliance (C++98-C++26)
**Project**: C++ to C Transpiler

---

## Key Findings

### 1. No Official ISO/WG21 Test Suite

The ISO C++ Standards Committee (WG21) **does not maintain or publish an official conformance test suite**. Standards compliance is measured through real-world code compatibility rather than standardized tests.

### 2. Three Major Open-Source Options

**GCC Test Suite**:
- **Location**: https://github.com/gcc-mirror/gcc/tree/master/gcc/testsuite
- **License**: GPL
- **Coverage**: C++11-C++26 (experimental)
- **Organization**: By standard clause (17-30) for libstdc++, by version (cpp0x, cpp1y, cpp1z, cpp2a, cpp23, cpp26) for g++.dg
- **Strengths**: Comprehensive, organized by standard sections, excellent traceability
- **Test Harness**: DejaGnu

**LLVM/Clang Test Suite**:
- **Location**: https://github.com/llvm/llvm-project/tree/main/libcxx/test
- **License**: Apache 2.0 with LLVM Exceptions
- **Coverage**: C++11-C++26 (experimental)
- **Organization**: Mirrors C++ standard structure
- **Strengths**: Modern infrastructure (LIT), permissive license, strong C++20/C++23 coverage
- **Test Harness**: LIT (LLVM Integrated Tester)

**LLVM Test Suite** (Whole Programs):
- **Location**: https://github.com/llvm/llvm-test-suite
- **Focus**: Benchmarks and whole-program tests
- **Less relevant**: Not organized by C++ standard version

### 3. Commercial Options (Most Comprehensive)

**Plum Hall Suite++** (Now owned by Solid Sands):
- **Coverage**: 7,500+ test cases
- **C++26 Support**: 421 preliminary test cases (industry-leading)
- **Focus**: Language conformance, hand-crafted tests
- **Status**: Industry-standard, trusted by major compiler vendors
- **Cost**: High (not publicly disclosed, contact vendor)

**Perennial**:
- **History**: NIST-certified (1989 contract)
- **Services**: Test suite + certification laboratory
- **Focus**: Safety-critical systems, POSIX certification
- **Cost**: Very high (includes certification services)

**Solid Sands SuperTest**:
- **History**: 40+ years tracking ISO standards, acquired Plum Hall (2021)
- **Focus**: Functional safety (ISO 26262, DO-178C, IEC 61508)
- **Features**: Extensive traceability and reporting
- **Cost**: Very high

### 4. MSVC Status

Microsoft tracks conformance internally but **does not publish a standalone test suite**. Conformance status available through documentation, but tests are not accessible.

---

## Coverage by C++ Standard

| Standard | GCC | Clang/LLVM | MSVC | Plum Hall | Assessment |
|----------|-----|------------|------|-----------|------------|
| C++98/03 | Excellent | Excellent | Excellent | Excellent | Complete |
| C++11 | Excellent | Excellent | Excellent | Excellent | Complete |
| C++14 | Excellent | Excellent | Excellent | Excellent | Complete |
| C++17 | Excellent | Excellent | Excellent | Excellent | Complete |
| C++20 | Very Good | Very Good | Good | Excellent | Mostly Complete |
| C++23 | Good | Good | Fair | Very Good | Partial (Active Development) |
| C++26 | Experimental | Experimental | Minimal | Good | Proposal Stage |

---

## Recommendations for Transpiler Project

### Primary Strategy: Use Open-Source Compiler Tests

**GCC + LLVM** provide free, comprehensive, and actively-maintained test suites:

1. **GCC libstdc++ Tests** for standard library conformance
   - Organized by standard clauses (17-30)
   - Easy traceability to C++ standard
   - Run with `GLIBCXX_TESTSUITE_STDS=11,14,17,20,23`

2. **LLVM libc++ Tests** for modern C++ features
   - Tests mirror standard organization
   - Modern test infrastructure (LIT)
   - Good C++20/C++23 coverage

3. **GCC g++.dg Tests** for language features
   - Organized by C++ version (cpp0x, cpp1y, cpp1z, cpp2a, cpp23, cpp26)
   - Extensive feature coverage

**Advantages**:
- Free and open-source
- Comprehensive coverage (thousands of tests)
- Actively maintained
- Can run full test suites
- Good documentation

**Challenges**:
- GPL license (GCC) may have restrictions
- Need to filter out compiler-specific tests
- Test harness (DejaGnu) has learning curve

### Secondary Strategy: Feature Coverage Tracking

Use **cppreference.com** (https://en.cppreference.com/w/cpp/compiler_support.html) for systematic verification:
- Comprehensive feature matrices for C++11-C++26
- Tracks GCC, Clang, MSVC, and other compilers
- Feature test macros (300+)
- Free and up-to-date

**Alternative**: **cppstat.dev** (https://cppstat.dev/) for visual interface

### Tertiary Strategy: Commercial Suite (Optional)

Consider **Plum Hall Suite++** if:
- Targeting safety-critical industries (automotive, medical, aerospace)
- Need certification documentation
- Require comprehensive C++23/C++26 coverage
- Budget allows ($10K-$100K+ estimated)

**Reasons**:
- Most comprehensive (7,500+ tests)
- Best C++26 support (421 preliminary tests)
- Industry-standard validation
- Excellent traceability for certification

---

## 3-Tier Testing Approach

**Tier 1: Open-Source Foundation** (Free, Comprehensive)
- GCC and LLVM test suites
- Automated regression testing
- Continuous integration

**Tier 2: Custom Transpiler Tests** (Targeted)
- Transpiler-specific validation
- Edge cases and integration tests
- Transformation correctness (name mangling, vtables, etc.)

**Tier 3: Feature Coverage Verification** (Systematic)
- cppreference.com feature matrices
- Systematic coverage tracking
- Gap analysis

**Optional Tier 4: Commercial Validation** (If Budget Allows)
- Plum Hall Suite++ for gold-standard validation
- Consider for v1.0 release or certification

---

## Quick Start Steps

1. **Clone GCC and LLVM repositories**:
   ```bash
   git clone https://github.com/gcc-mirror/gcc.git
   git clone https://github.com/llvm/llvm-project.git
   ```

2. **Extract relevant tests** (C++11 example):
   ```bash
   # GCC C++11 tests
   find gcc/testsuite/g++.dg/cpp0x -name "*.C" > cpp11_tests.txt

   # LLVM C++11 tests
   find llvm-project/libcxx/test/std -name "*.pass.cpp" > libcxx_tests.txt
   ```

3. **Create test harness**:
   - Transpile C++ test to C
   - Compile both C++ and C versions
   - Run and compare outputs
   - Report pass/fail rates

4. **Track coverage**:
   - Use cppreference.com to identify features
   - Create coverage matrix
   - Monitor pass rates by feature and standard

---

## Test Suite Comparison Table

| Suite | Access | License | Coverage | C++26 | Cost | Best For |
|-------|--------|---------|----------|-------|------|----------|
| GCC | Open | GPL | C++11-C++26 | Experimental | Free | Language features, standard library |
| LLVM | Open | Apache 2.0 | C++11-C++26 | Experimental | Free | Modern C++, permissive license |
| Plum Hall | Commercial | Proprietary | C++98-C++26 | 421 tests | High | Comprehensive validation, certification |
| Perennial | Commercial | Proprietary | C++98-C++20+ | Unknown | Very High | Certification, NIST-backed |
| Solid Sands | Commercial | Proprietary | C++98-C++23 | Good | Very High | Safety-critical, functional safety |
| MSVC | Internal | Proprietary | C++11-C++23 | Minimal | N/A (not available) | Reference only |

---

## Key Resources

**Test Suites**:
- GCC: https://github.com/gcc-mirror/gcc/tree/master/gcc/testsuite
- LLVM: https://github.com/llvm/llvm-project/tree/main/libcxx/test
- Plum Hall: https://plumhall.com/

**Feature Tracking**:
- cppreference: https://en.cppreference.com/w/cpp/compiler_support.html
- cppstat.dev: https://cppstat.dev/

**Compiler Status Pages**:
- GCC: https://gcc.gnu.org/projects/cxx-status.html
- Clang: https://clang.llvm.org/cxx_status.html
- MSVC: https://learn.microsoft.com/en-us/cpp/overview/visual-cpp-language-conformance

**Documentation**:
- GCC Testing: https://gcc.gnu.org/onlinedocs/libstdc++/manual/test.html
- LLVM Testing: https://llvm.org/docs/TestingGuide.html
- libc++ Testing: https://libcxx.llvm.org/TestingLibcxx.html

---

## Conclusion

For the C++ to C transpiler project, **use GCC and LLVM open-source test suites** as the primary validation method. They provide comprehensive, free, and actively-maintained coverage for C++11-C++23. Supplement with **custom transpiler-specific tests** and **cppreference.com feature matrices** for systematic verification. Consider **Plum Hall Suite++** only if targeting commercial/safety-critical markets with budget for comprehensive validation.

**Estimated Test Count Available**:
- GCC: 10,000+ tests (g++.dg + libstdc++)
- LLVM: 5,000+ tests (libc++)
- Plum Hall: 7,500+ tests (commercial)

**Next Steps**:
1. Set up GCC and LLVM test extraction pipeline
2. Create test harness for transpiler validation
3. Run initial test suite (C++11 subset)
4. Track pass rates and coverage
5. Iterate and expand to C++14, C++17, C++20

---

**For complete details, see full research report**: `cpp-compiler-compliance-tests-research.md`
