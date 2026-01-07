# C++ Compiler Compliance Test Suites - Quick Reference

**Date**: January 7, 2026

---

## Test Suite Comparison Matrix

| Suite | Type | License | Test Count | C++11 | C++14 | C++17 | C++20 | C++23 | C++26 | Cost | Access |
|-------|------|---------|------------|-------|-------|-------|-------|-------|-------|------|--------|
| **GCC libstdc++** | Open Source | GPL | 5,000+ | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓ | ✓ | Free | [GitHub](https://github.com/gcc-mirror/gcc/tree/master/libstdc++-v3/testsuite) |
| **GCC g++.dg** | Open Source | GPL | 5,000+ | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓ | ✓ | Free | [GitHub](https://github.com/gcc-mirror/gcc/tree/master/gcc/testsuite/g++.dg) |
| **LLVM libc++** | Open Source | Apache 2.0 | 5,000+ | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓ | ✓ | Free | [GitHub](https://github.com/llvm/llvm-project/tree/main/libcxx/test) |
| **LLVM test-suite** | Open Source | Apache 2.0 | 1,000+ | ✓✓ | ✓✓ | ✓✓ | ✓✓ | ✓ | ✓ | Free | [GitHub](https://github.com/llvm/llvm-test-suite) |
| **Plum Hall Suite++** | Commercial | Proprietary | 7,500+ | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓✓ | $$$ | [Contact Vendor](https://plumhall.com/) |
| **Perennial** | Commercial | Proprietary | Unknown | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓ | ✓ | ? | $$$$ | [Contact Vendor](https://www.peren.com/) |
| **Solid Sands SuperTest** | Commercial | Proprietary | Unknown | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓ | ✓✓ | $$$$ | [Contact Vendor](https://solidsands.com/) |
| **MSVC Internal** | Internal | Proprietary | Unknown | ✓✓✓ | ✓✓✓ | ✓✓✓ | ✓✓ | ✓ | ✓ | N/A | Not Available |

**Legend**:
- ✓✓✓ = Excellent coverage (comprehensive, well-tested)
- ✓✓ = Good coverage (most features tested)
- ✓ = Partial/Experimental coverage (some features tested)
- ? = Unknown
- $ = Low cost (<$1K)
- $$ = Medium cost ($1K-$10K)
- $$$ = High cost ($10K-$50K)
- $$$$ = Very high cost (>$50K)

---

## Detailed Comparison

### GCC Test Suite

| Aspect | Details |
|--------|---------|
| **Repository** | https://github.com/gcc-mirror/gcc |
| **License** | GPL (open source) |
| **Test Directories** | `gcc/testsuite/g++.dg/`, `libstdc++-v3/testsuite/` |
| **Test Count** | ~10,000+ combined |
| **Organization** | By C++ standard clause (libstdc++), by version (g++.dg) |
| **Test Harness** | DejaGnu |
| **Standards Coverage** | C++98-C++26 (experimental) |
| **Best For** | Standard library conformance, language features |
| **Strengths** | Comprehensive, organized by standard sections, excellent traceability |
| **Weaknesses** | GPL license, DejaGnu learning curve |
| **How to Run** | `make check-g++`, `make check-target-libstdc++-v3` |
| **Docs** | https://gcc.gnu.org/onlinedocs/libstdc++/manual/test.html |

---

### LLVM/Clang Test Suite

| Aspect | Details |
|--------|---------|
| **Repository** | https://github.com/llvm/llvm-project |
| **License** | Apache 2.0 with LLVM Exceptions (permissive) |
| **Test Directories** | `libcxx/test/`, `clang/test/`, `llvm-test-suite/` |
| **Test Count** | ~5,000+ libc++ tests, 1,000+ whole-program tests |
| **Organization** | Mirrors C++ standard structure |
| **Test Harness** | LIT (LLVM Integrated Tester) |
| **Standards Coverage** | C++11-C++26 (experimental) |
| **Best For** | Modern C++ features, permissive license projects |
| **Strengths** | Modern infrastructure, Apache license, strong C++20/C++23 |
| **Weaknesses** | Less organized by standard clause than GCC |
| **How to Run** | `ninja check-cxx`, `./libcxx/utils/libcxx-lit build --param std=c++20` |
| **Docs** | https://libcxx.llvm.org/TestingLibcxx.html |

---

### Plum Hall Suite++

| Aspect | Details |
|--------|---------|
| **Website** | https://plumhall.com/ (now owned by Solid Sands) |
| **License** | Commercial proprietary |
| **Test Count** | 7,500+ test cases |
| **C++26 Coverage** | 421 preliminary tests (industry-leading) |
| **Organization** | By standard clauses and features |
| **Standards Coverage** | C++98-C++26 (preliminary) |
| **Best For** | Comprehensive validation, certification, safety-critical |
| **Strengths** | Most comprehensive, hand-crafted tests, excellent traceability, industry-standard |
| **Weaknesses** | High cost, proprietary, not publicly accessible |
| **Pricing** | Contact vendor (estimated $10K-$100K+) |
| **Target Users** | Compiler vendors, safety-critical industries, certification needs |

---

### Perennial

| Aspect | Details |
|--------|---------|
| **Website** | https://www.peren.com/ |
| **License** | Commercial proprietary |
| **Test Count** | Not publicly disclosed |
| **History** | NIST-certified (1989), 35+ years |
| **Services** | Test suite + certification laboratory |
| **Standards Coverage** | C++98-C++20+ (C++23/26 status unclear) |
| **Best For** | Certification, POSIX conformance, safety-critical |
| **Strengths** | NIST-backed, official certification, accredited laboratory |
| **Weaknesses** | Very high cost, less transparent, older focus |
| **Pricing** | Contact vendor (estimated $50K+) |
| **Target Users** | Organizations needing official certification |

---

### Solid Sands SuperTest

| Aspect | Details |
|--------|---------|
| **Website** | https://solidsands.com/ |
| **License** | Commercial proprietary |
| **Test Count** | Not publicly disclosed |
| **History** | 40+ years, acquired Plum Hall (2021) |
| **Focus** | Functional safety (ISO 26262, DO-178C, IEC 61508) |
| **Standards Coverage** | C++98-C++23 (good), C++26 (likely via Plum Hall) |
| **Best For** | Safety-critical systems, functional safety certification |
| **Strengths** | Longest track record, safety-critical focus, extensive reporting |
| **Weaknesses** | Very high cost, proprietary, overkill for non-critical |
| **Pricing** | Contact vendor (estimated $50K-$100K+) |
| **Target Users** | Automotive, aerospace, medical, industrial safety systems |

---

## Feature Catalog Resources

| Resource | URL | Coverage | Features |
|----------|-----|----------|----------|
| **cppreference.com** | https://en.cppreference.com/w/cpp/compiler_support.html | C++11-C++26 | Comprehensive compiler support matrix |
| **cppstat.dev** | https://cppstat.dev/ | C++17-C++26 | Visual interface, GCC/Clang/MSVC/Xcode |
| **GCC C++ Status** | https://gcc.gnu.org/projects/cxx-status.html | C++11-C++26 | Official GCC conformance tracking |
| **Clang C++ Status** | https://clang.llvm.org/cxx_status.html | C++98-C++26 | Official Clang conformance tracking |
| **MSVC Conformance** | https://learn.microsoft.com/en-us/cpp/overview/visual-cpp-language-conformance | C++11-C++23 | Official MSVC conformance by VS version |
| **Modern C++ Features** | https://github.com/AnthonyCalandra/modern-cpp-features | C++11-C++20 | Cheatsheet with code examples |
| **Feature Test Macros** | https://en.cppreference.com/w/cpp/feature_test.html | C++11-C++26 | 300+ feature test macros |

---

## Test Organization Patterns

| Pattern | Used By | Primary Axis | Secondary Axis | Ease of Navigation |
|---------|---------|--------------|----------------|-------------------|
| **By Standard Clause** | GCC libstdc++ | Standard sections (17-30) | Test type | Medium (need standard knowledge) |
| **By Feature/Version** | GCC g++.dg | C++ version (cpp0x, cpp1y, etc.) | Feature category | Good |
| **Mirror Standard** | LLVM libc++ | Standard structure | Test type | Good |
| **By Source Count** | LLVM test-suite | Single/Multi-file | Benchmark/Test | Poor for feature search |
| **By Contributor** | GCC old-deja (deprecated) | Contributor name | None | Poor (legacy only) |

---

## Standard Version Coverage Summary

| Standard | Year | GCC | Clang | MSVC | Plum Hall | Open Source Status | Commercial Status |
|----------|------|-----|-------|------|-----------|-------------------|------------------|
| **C++98/03** | 1998/2003 | Complete | Complete | Complete | Complete | Excellent | Excellent |
| **C++11** | 2011 | Complete | Complete | Complete | Complete | Excellent | Excellent |
| **C++14** | 2014 | Complete | Complete | Complete | Complete | Excellent | Excellent |
| **C++17** | 2017 | Complete | Complete | Complete | Complete | Excellent | Excellent |
| **C++20** | 2020 | Mostly Complete | Mostly Complete | Mostly Complete | Complete | Very Good | Excellent |
| **C++23** | 2024 | Partial | Partial | Partial | Extensive | Good | Very Good |
| **C++26** | ~2026 | Experimental | Experimental | Minimal | Preliminary (421 tests) | Experimental | Good |

---

## Recommended Test Suite by Use Case

| Use Case | Recommended Suite | Rationale |
|----------|------------------|-----------|
| **Open-source transpiler** | GCC + LLVM | Free, comprehensive, permissive licenses |
| **Commercial transpiler** | GCC + LLVM + Plum Hall | Breadth (open) + certification (commercial) |
| **Safety-critical project** | Solid Sands SuperTest | Functional safety focus, traceability |
| **Certification needs** | Perennial or Plum Hall | Official certification, industry-standard |
| **C++11-C++17 focus** | GCC libstdc++ | Excellent coverage, organized by clause |
| **C++20-C++23 focus** | LLVM libc++ | Modern features, active development |
| **C++26 exploration** | Plum Hall Suite++ | Best C++26 coverage (421 tests) |
| **Learning/education** | Modern C++ Features + cppreference | Examples + feature tracking |
| **Quick validation** | LLVM test-suite | Whole-program tests, fast setup |

---

## Quick Start Commands

### GCC Tests

```bash
# Clone repository
git clone https://github.com/gcc-mirror/gcc.git
cd gcc

# Configure and build
./configure --prefix=/usr/local/gcc-test --enable-languages=c,c++
make -j$(nproc)

# Run C++ tests
make check-g++

# Run libstdc++ tests
make check-target-libstdc++-v3

# Test specific C++ standards
GLIBCXX_TESTSUITE_STDS=11,14,17,20,23 make check-target-libstdc++-v3
```

### LLVM Tests

```bash
# Clone repository
git clone https://github.com/llvm/llvm-project.git
cd llvm-project

# Build with CMake
mkdir build && cd build
cmake -G Ninja ../llvm -DLLVM_ENABLE_PROJECTS="clang;libcxx;libcxxabi"
ninja

# Run libc++ tests
ninja check-cxx

# Test specific C++ standard
../libcxx/utils/libcxx-lit . -sv libcxx/test/std --param std=c++20
```

---

## Decision Matrix

### Should you use open-source or commercial test suites?

| Factor | Open Source (GCC/LLVM) | Commercial (Plum Hall) |
|--------|----------------------|----------------------|
| **Budget** | Free | $10K-$100K+ |
| **Coverage** | Very Good (C++11-C++23) | Excellent (C++11-C++26) |
| **C++26 Support** | Experimental | Best available (421 tests) |
| **Certification** | No | Yes |
| **Traceability** | Good | Excellent |
| **License** | GPL/Apache | Proprietary |
| **Maintenance** | Community | Vendor |
| **Support** | Community | Commercial |
| **Best For** | Most projects | Safety-critical, certification |

**Decision Rule**:
- **Use open-source** unless you need C++26, certification, or are in safety-critical domain
- **Use commercial** for safety-critical (automotive, medical, aerospace) or certification needs

---

## Test Count Estimates

| Test Suite | Approximate Test Count | Test Types |
|------------|----------------------|------------|
| GCC g++.dg | ~5,000 | Language features, positive & negative |
| GCC libstdc++ | ~5,000 | Standard library conformance |
| LLVM libc++ | ~5,000 | Standard library conformance |
| LLVM test-suite | ~1,000 | Whole programs, benchmarks |
| Plum Hall Suite++ | 7,500+ | Language + library, positive & negative & undefined |
| Perennial | Unknown | Language + library |
| Solid Sands SuperTest | Unknown | Language + library + optimizer |

**Total Available (Open Source)**: ~15,000+ tests
**Total Available (with Commercial)**: ~20,000+ tests

---

## Standards Timeline

| Year | Standard | Status | Test Availability |
|------|----------|--------|------------------|
| 1998 | C++98 | Published | Excellent |
| 2003 | C++03 | Published | Excellent |
| 2011 | C++11 | Published | Excellent |
| 2014 | C++14 | Published | Excellent |
| 2017 | C++17 | Published | Excellent |
| 2020 | C++20 | Published | Very Good |
| 2024 | C++23 | Published (Feb 2024) | Good (improving) |
| 2026 | C++26 | Draft (expected 2026) | Experimental/Preliminary |

---

## Key Contacts

| Organization | Contact | URL |
|--------------|---------|-----|
| **Solid Sands** (Plum Hall) | sales@solidsands.com | https://solidsands.com/ |
| **Perennial** | info@peren.com | https://www.peren.com/ |
| **GCC Project** | gcc@gcc.gnu.org | https://gcc.gnu.org/ |
| **LLVM Project** | llvm-dev@lists.llvm.org | https://llvm.org/ |

---

## Further Reading

- **Full Research Report**: See `cpp-compiler-compliance-tests-research.md` for comprehensive analysis
- **Executive Summary**: See `SUMMARY.md` for 1-page overview
- **GCC Testing Guide**: https://gcc.gnu.org/onlinedocs/libstdc++/manual/test.html
- **LLVM Testing Guide**: https://llvm.org/docs/TestingGuide.html
- **C++ Standards**: https://isocpp.org/std

---

**Last Updated**: January 7, 2026
