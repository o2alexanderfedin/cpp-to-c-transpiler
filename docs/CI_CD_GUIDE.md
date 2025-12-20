# CI/CD Pipeline Guide

## Overview

This document describes the Continuous Integration and Continuous Deployment (CI/CD) pipeline for the C++ to C transpiler project. The pipeline is implemented using GitHub Actions and provides comprehensive automated testing, quality checks, and performance monitoring.

## Architecture

The CI/CD pipeline consists of four main workflows:

1. **Continuous Integration (`ci.yml`)** - Core test suite
2. **Code Coverage (`coverage.yml`)** - Coverage reporting and analysis
3. **Memory Safety (`sanitizers.yml`)** - Memory safety checks with sanitizers
4. **Benchmark Regression (`benchmark-regression.yml`)** - Performance monitoring

## Workflows

### 1. Continuous Integration (ci.yml)

**Purpose:** Runs comprehensive test suites on every commit to ensure code quality and catch regressions early.

**Triggers:**
- Push to `develop`, `main`, or feature branches
- Pull requests to `develop` or `main`
- Manual dispatch

**Jobs:**

#### Unit Tests (Linux)
- **Duration:** ~10-15 minutes
- **Platform:** Ubuntu Latest
- **Tests:** 70+ unit test executables covering:
  - Core transpiler components (Visitor, NameMangler, CodeGenerator)
  - Template processing (extraction, monomorphization, STL integration)
  - Header generation and dependency analysis
  - RAII and destructor injection
  - Inheritance (single, virtual, multiple)
  - Virtual functions and vtables
  - Exception handling (PNaCl SJLJ)
  - RTTI implementation (Itanium ABI)
  - Coroutines (C++20)
  - Runtime optimization modes
  - Operator overloading
  - Lambdas and closures
  - Move semantics
  - Type traits and metaprogramming
  - Smart pointers (unique_ptr, shared_ptr)

#### Integration Tests (Linux)
- **Duration:** ~5-10 minutes
- **Platform:** Ubuntu Latest
- **Tests:** Multi-component integration tests:
  - Translation integration
  - Validation suite
  - File output system integration

#### Real-World Tests (Linux)
- **Duration:** ~5-10 minutes
- **Platform:** Ubuntu Latest
- **Tests:** Complete end-to-end scenarios:
  - JSON parser
  - Logger system
  - Test framework
  - String formatter
  - Resource manager

#### Matrix Tests
- **Duration:** ~15-20 minutes
- **Platforms:** Linux, macOS, Windows
- **Purpose:** Verify cross-platform compatibility
- **Tests:** Smoke tests with critical components

**Success Criteria:**
- All unit tests must pass
- All integration tests must pass
- All real-world tests must pass
- At least smoke tests must pass on all platforms

**Artifacts:**
- Test logs and results (7 day retention)

---

### 2. Code Coverage (coverage.yml)

**Purpose:** Generates code coverage reports and uploads to Codecov for tracking test coverage over time.

**Triggers:**
- Push to `develop` or `main`
- Pull requests to `develop` or `main`
- Manual dispatch

**Process:**
1. Build project with coverage instrumentation (--coverage flags)
2. Run all test executables
3. Collect coverage data with `lcov`
4. Generate HTML reports with `genhtml`
5. Generate XML reports with `gcovr` for Codecov
6. Upload to Codecov
7. Comment coverage summary on PRs

**Tools:**
- **lcov** - Coverage data collection
- **genhtml** - HTML report generation
- **gcovr** - XML report generation
- **Codecov** - Coverage tracking and visualization

**Outputs:**
- HTML coverage report (artifact, 30 day retention)
- Coverage data files (artifact, 30 day retention)
- Codecov dashboard updates
- PR comments with coverage summary

**Coverage Threshold:**
- Minimum: 70% line coverage (warning if below)
- Target: 80%+ line coverage

**Badge:**
```markdown
[![codecov](https://codecov.io/gh/YOUR_USERNAME/hupyy-cpp-to-c/branch/develop/graph/badge.svg)](https://codecov.io/gh/YOUR_USERNAME/hupyy-cpp-to-c)
```

---

### 3. Memory Safety and Sanitizers (sanitizers.yml)

**Purpose:** Detect memory errors, undefined behavior, data races, and uninitialized memory reads using various sanitizers.

**Triggers:**
- Push to `develop` or `main`
- Pull requests to `develop` or `main`
- Scheduled nightly at 2 AM UTC
- Manual dispatch

**Jobs:**

#### AddressSanitizer (ASan)
- **Purpose:** Detect memory errors
  - Use-after-free
  - Heap buffer overflow
  - Stack buffer overflow
  - Memory leaks
- **Flags:** `-fsanitize=address -fno-omit-frame-pointer -g`
- **Tests:** Critical test suite (7 tests)
- **Status:** Required to pass

#### UndefinedBehaviorSanitizer (UBSan)
- **Purpose:** Detect undefined behavior
  - Integer overflow
  - Division by zero
  - Null pointer dereference
  - Invalid shifts
- **Flags:** `-fsanitize=undefined -fno-omit-frame-pointer -g`
- **Tests:** Critical test suite (5 tests)
- **Status:** Required to pass

#### ThreadSanitizer (TSan)
- **Purpose:** Detect data races and thread safety issues
  - Data races
  - Deadlocks
  - Thread leaks
- **Flags:** `-fsanitize=thread -fno-omit-frame-pointer -g`
- **Tests:** Thread-safety tests (1 test)
- **Status:** Required to pass

#### MemorySanitizer (MSan)
- **Purpose:** Detect uninitialized memory reads
  - Use of uninitialized variables
  - Reading uninitialized memory
- **Flags:** `-fsanitize=memory -fno-omit-frame-pointer -g`
- **Tests:** Minimal test suite (2 tests)
- **Status:** Advisory only (continue-on-error)
- **Note:** Very strict, may have false positives with LLVM libraries

#### Valgrind
- **Purpose:** Additional memory checking
  - Memory leaks
  - Invalid memory access
  - Use of uninitialized values
- **Tests:** Critical tests (2 tests)
- **Status:** Advisory only
- **Duration:** ~30 minutes (slower)

**Artifacts:**
- Sanitizer logs for each tool (7 day retention)

**Notes:**
- Sanitizers add significant overhead; tests run slower
- MSan requires rebuilding all dependencies with MSan
- TSan and ASan cannot be combined
- Valgrind is slower but catches different issues

---

### 4. Benchmark Regression Detection (benchmark-regression.yml)

**Purpose:** Monitor performance over time and detect performance regressions.

**Triggers:**
- Push to `develop` or `main`
- Pull requests to `develop` or `main`
- Manual dispatch (with configurable threshold)

**Process:**
1. Build project in Release mode with benchmarks
2. Download baseline benchmark results from previous run
3. Run current benchmarks
4. Compare with baseline using Python comparison script
5. Detect regressions beyond threshold (default 5%)
6. Comment results on PRs
7. Upload new baseline for future comparisons

**Regression Threshold:**
- Default: 5%
- Configurable via workflow dispatch input

**Benchmarks:**
- RTTI runtime performance tests
- Various transpiler performance metrics

**Artifacts:**
- Benchmark baseline (90 day retention)
- Full benchmark results (30 day retention)
- Performance history entries (365 day retention)

**Status:**
- Fails if regression detected beyond threshold
- PR comments provide detailed comparison

---

## Pipeline Flow

### For Every Commit

```
Push/PR → CI Workflow (fast)
       ├─ Unit Tests (Linux) ━━━━━━━━━━━━┓
       ├─ Integration Tests (Linux) ━━━━━┫
       ├─ Real-World Tests (Linux) ━━━━━━┫→ CI Status Report
       └─ Matrix Tests (Linux/Mac/Win) ━━┛

Push/PR → Coverage Workflow (parallel)
       └─ Generate Coverage → Upload Codecov → PR Comment

Push/PR → Sanitizers Workflow (parallel, nightly)
       ├─ AddressSanitizer ━━━━━━━━━━━━━┓
       ├─ UndefinedBehaviorSanitizer ━━━━┫
       ├─ ThreadSanitizer ━━━━━━━━━━━━━━┫→ Sanitizers Status
       ├─ MemorySanitizer ━━━━━━━━━━━━━┫
       └─ Valgrind ━━━━━━━━━━━━━━━━━━━━┛

Push/PR → Benchmark Workflow (parallel)
       └─ Run Benchmarks → Compare → PR Comment → Track Performance
```

### Total Duration

- **Fast Feedback:** ~10-15 minutes (CI core tests)
- **Full Suite:** ~20-30 minutes (all workflows)
- **With Sanitizers:** ~40-60 minutes (if run on every commit)

**Optimization:** Sanitizers run nightly or on-demand to save CI time.

---

## Configuration

### Environment Variables

All workflows use these environment variables:

```yaml
env:
  BUILD_TYPE: Release  # or Debug for coverage/sanitizers
  LLVM_VERSION: 15     # LLVM/Clang version
```

### Caching

LLVM/Clang installations are cached to speed up builds:

```yaml
- name: Cache LLVM/Clang
  uses: actions/cache@v4
  with:
    path: /usr/lib/llvm-${{ env.LLVM_VERSION }}
    key: ${{ runner.os }}-llvm-${{ env.LLVM_VERSION }}
```

### Concurrency Control

Workflows use concurrency groups to cancel in-progress runs:

```yaml
concurrency:
  group: ci-${{ github.ref }}
  cancel-in-progress: true
```

---

## Setting Up CI/CD

### Prerequisites

1. **GitHub Repository:** Push code to GitHub
2. **Codecov Account:** Sign up at https://codecov.io/
   - Link your GitHub repository
   - Get `CODECOV_TOKEN`
   - Add as repository secret: Settings → Secrets → Actions → New repository secret

### Adding Codecov Token

```bash
# Go to: https://github.com/YOUR_USERNAME/hupyy-cpp-to-c/settings/secrets/actions
# Click "New repository secret"
# Name: CODECOV_TOKEN
# Value: (paste token from codecov.io)
```

### Status Badges

Add these badges to your README.md:

```markdown
[![CI](https://github.com/YOUR_USERNAME/hupyy-cpp-to-c/workflows/Continuous%20Integration/badge.svg)](https://github.com/YOUR_USERNAME/hupyy-cpp-to-c/actions/workflows/ci.yml)
[![Coverage](https://codecov.io/gh/YOUR_USERNAME/hupyy-cpp-to-c/branch/develop/graph/badge.svg)](https://codecov.io/gh/YOUR_USERNAME/hupyy-cpp-to-c)
[![Sanitizers](https://github.com/YOUR_USERNAME/hupyy-cpp-to-c/workflows/Memory%20Safety%20and%20Sanitizers/badge.svg)](https://github.com/YOUR_USERNAME/hupyy-cpp-to-c/actions/workflows/sanitizers.yml)
```

---

## Local Testing

### Running Tests Locally

```bash
# Build project
cmake -B build -DCMAKE_BUILD_TYPE=Release
cmake --build build --parallel

# Run all tests
./run-all-tests.sh

# Run specific test
./build/CppToCVisitorTest
```

### Generate Coverage Locally

```bash
# Build with coverage
cmake -B build -DCMAKE_BUILD_TYPE=Debug -DENABLE_COVERAGE=ON
cmake --build build --parallel

# Run tests
cd build
for test in *Test; do ./$test; done

# Generate report
lcov --directory . --capture --output-file coverage.info
lcov --remove coverage.info '/usr/*' '*/tests/*' '*/build/*' --output-file coverage.info.cleaned
genhtml coverage.info.cleaned --output-directory coverage-html

# Open report
open coverage-html/index.html  # macOS
xdg-open coverage-html/index.html  # Linux
```

### Run Sanitizers Locally

```bash
# AddressSanitizer
cmake -B build-asan -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_CXX_FLAGS="-fsanitize=address -fno-omit-frame-pointer -g" \
  -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=address"
cmake --build build-asan --parallel
cd build-asan && ./CppToCVisitorTest

# UndefinedBehaviorSanitizer
cmake -B build-ubsan -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_CXX_FLAGS="-fsanitize=undefined -fno-omit-frame-pointer -g" \
  -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=undefined"
cmake --build build-ubsan --parallel
cd build-ubsan && ./CppToCVisitorTest

# ThreadSanitizer
cmake -B build-tsan -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_CXX_FLAGS="-fsanitize=thread -fno-omit-frame-pointer -g" \
  -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=thread"
cmake --build build-tsan --parallel
cd build-tsan && ./ExceptionThreadSafetyTest
```

### Run Benchmarks Locally

```bash
# Build with benchmarks
cmake -B build -DCMAKE_BUILD_TYPE=Release -DBUILD_BENCHMARKS=ON
cmake --build build --parallel

# Run benchmarks
cd benchmarks
./run_benchmarks.sh --baseline

# View results
cat ../benchmark-results/baseline.json
```

---

## Troubleshooting

### CI Failures

**Problem:** Unit tests fail on CI but pass locally
- **Cause:** Different environment (OS, LLVM version, dependencies)
- **Solution:**
  - Check workflow logs for error details
  - Try reproducing in a clean environment
  - Verify LLVM/Clang versions match

**Problem:** Timeout errors (> 15 minutes)
- **Cause:** Tests taking too long
- **Solution:**
  - Optimize slow tests
  - Increase timeout in workflow
  - Split tests into smaller groups

**Problem:** Sanitizer false positives
- **Cause:** Issues in LLVM/Clang libraries or test infrastructure
- **Solution:**
  - Review sanitizer suppressions
  - Update LLVM version
  - Use continue-on-error for advisory sanitizers

### Coverage Issues

**Problem:** Coverage not uploading to Codecov
- **Cause:** Missing or invalid `CODECOV_TOKEN`
- **Solution:**
  - Verify token is set in repository secrets
  - Check token has correct permissions
  - Review Codecov workflow logs

**Problem:** Low coverage percentage
- **Cause:** Missing tests for certain components
- **Solution:**
  - Review coverage HTML report
  - Add tests for uncovered code
  - Focus on critical paths first

### Performance Regressions

**Problem:** False positive regression detection
- **Cause:** Noisy benchmarks or inconsistent CI environment
- **Solution:**
  - Increase regression threshold
  - Run benchmarks multiple times and average
  - Use dedicated CI runners

**Problem:** Real regressions not detected
- **Cause:** Threshold too high
- **Solution:**
  - Lower regression threshold
  - Add more specific benchmarks
  - Review baseline selection logic

---

## Best Practices

### For Contributors

1. **Run Tests Locally:** Always run tests before pushing
2. **Check Coverage:** Review coverage for new code
3. **Watch CI:** Monitor CI results and fix issues promptly
4. **Review Sanitizers:** Check sanitizer results, especially for memory-related changes
5. **Performance Aware:** Run benchmarks for performance-sensitive changes

### For Maintainers

1. **Keep CI Fast:** Optimize tests, use parallel execution
2. **Monitor Trends:** Review coverage and performance trends regularly
3. **Update Dependencies:** Keep LLVM/Clang and CI actions up to date
4. **Adjust Thresholds:** Tune coverage and performance thresholds based on project needs
5. **Document Changes:** Update this guide when modifying workflows

### Workflow Optimization

1. **Parallel Jobs:** Run independent jobs in parallel
2. **Smart Caching:** Cache dependencies (LLVM, CMake builds)
3. **Fail Fast:** Run quick tests first
4. **Matrix Strategy:** Use matrices for multi-platform testing
5. **Conditional Runs:** Skip non-essential workflows for draft PRs

---

## Metrics and Monitoring

### Key Metrics

- **CI Pass Rate:** Target >95%
- **Average CI Duration:** Target <15 minutes
- **Code Coverage:** Target >80%
- **Performance Variance:** Target <5%
- **Sanitizer Issues:** Target 0 critical issues

### Dashboards

- **GitHub Actions:** https://github.com/YOUR_USERNAME/hupyy-cpp-to-c/actions
- **Codecov:** https://codecov.io/gh/YOUR_USERNAME/hupyy-cpp-to-c
- **Benchmark Trends:** View artifacts in workflow runs

---

## Future Enhancements

### Planned Improvements

1. **Docker-based CI:** Consistent environment across all platforms
2. **Parallelized Test Execution:** Further speed improvements
3. **Custom Test Reporter:** Better test result visualization
4. **Performance Dashboard:** Track benchmark trends over time
5. **Automatic Issue Creation:** File issues for failing sanitizers
6. **Fuzzing Integration:** Add continuous fuzzing with OSS-Fuzz
7. **Static Analysis:** Integrate clang-tidy, cppcheck
8. **Security Scanning:** Add dependency vulnerability scanning

### Contributing to CI/CD

To propose improvements to the CI/CD pipeline:

1. Discuss in GitHub Issues
2. Test changes in a fork first
3. Submit PR with workflow changes
4. Document changes in this guide

---

## Support

For questions or issues with CI/CD:

1. Check this guide first
2. Review workflow logs in GitHub Actions
3. Search existing GitHub Issues
4. Open a new issue with:
   - Workflow name and run ID
   - Error messages and logs
   - Steps to reproduce

---

## References

- [GitHub Actions Documentation](https://docs.github.com/en/actions)
- [Codecov Documentation](https://docs.codecov.io/)
- [LLVM Sanitizers](https://clang.llvm.org/docs/index.html)
- [CMake Coverage](https://gcovr.com/en/stable/)
- [Project README](../README.md)
- [Build Setup Guide](../BUILD_SETUP.md)

---

**Last Updated:** 2025-12-18
**Maintained by:** Development Team
