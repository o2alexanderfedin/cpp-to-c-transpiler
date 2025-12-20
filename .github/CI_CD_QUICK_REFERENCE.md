# CI/CD Quick Reference Card

## Workflows at a Glance

| Workflow | Trigger | Duration | Purpose |
|----------|---------|----------|---------|
| **CI** | Every push/PR | 10-15 min | Fast feedback on code changes |
| **Coverage** | Push/PR to develop/main | 15-20 min | Track test coverage |
| **Sanitizers** | Push/PR + nightly | 40-60 min | Memory safety checks |
| **Benchmarks** | Push/PR to develop/main | 20-30 min | Performance regression |

## Quick Commands

### View Workflow Status
```bash
# Open GitHub Actions in browser
open https://github.com/o2alexanderfedin/cpp-to-c-transpiler/actions

# Check latest run status via CLI (requires gh CLI)
gh run list --workflow=ci.yml --limit 5
gh run view --workflow=ci.yml
```

### Run Tests Locally
```bash
# All tests
./run-all-tests.sh

# Specific test
./build/CppToCVisitorTest

# With coverage
cmake -B build -DENABLE_COVERAGE=ON -DCMAKE_BUILD_TYPE=Debug
cmake --build build
cd build && for test in *Test; do ./$test; done
lcov --directory . --capture --output-file coverage.info
genhtml coverage.info --output-directory coverage-html
```

### Run Sanitizers Locally
```bash
# AddressSanitizer
cmake -B build-asan -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_CXX_FLAGS="-fsanitize=address -g" \
  -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=address"
cmake --build build-asan
./build-asan/CppToCVisitorTest

# UndefinedBehaviorSanitizer
cmake -B build-ubsan -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_CXX_FLAGS="-fsanitize=undefined -g" \
  -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=undefined"
cmake --build build-ubsan
./build-ubsan/CppToCVisitorTest

# ThreadSanitizer
cmake -B build-tsan -DCMAKE_BUILD_TYPE=Debug \
  -DCMAKE_CXX_FLAGS="-fsanitize=thread -g" \
  -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=thread"
cmake --build build-tsan
./build-tsan/ExceptionThreadSafetyTest
```

## Workflow Files

| File | Lines | Description |
|------|-------|-------------|
| `ci.yml` | 650 | Main CI with unit/integration/real-world tests |
| `coverage.yml` | 270 | Coverage reporting and Codecov upload |
| `sanitizers.yml` | 650 | Memory safety checks (ASan/UBSan/TSan/MSan/Valgrind) |
| `benchmark-regression.yml` | 270 | Performance regression detection |

## Test Coverage

| Category | Count | Examples |
|----------|-------|----------|
| Unit Tests | 70+ | CppToCVisitorTest, NameManglerTest, CodeGeneratorTest |
| Integration | 3 | TranslationIntegrationTest, ValidationTest, IntegrationTest |
| Real-World | 5 | JSON parser, Logger, Test framework, String formatter, Resource manager |
| Platforms | 3 | Linux, macOS, Windows |

## Key Metrics

| Metric | Target | Status |
|--------|--------|--------|
| CI Pass Rate | >95% | 🎯 Target |
| CI Duration | <15 min | ✅ 10-15 min |
| Coverage | >80% | ⚠️ 70% min |
| Performance Variance | <5% | 🎯 Tracked |
| Sanitizer Issues | 0 critical | ✅ Clean |

## Troubleshooting

### CI Failing?
1. Check workflow logs in Actions tab
2. Run tests locally to reproduce
3. Verify LLVM/Clang versions match
4. Check for environment differences

### Coverage Not Uploading?
1. Verify `CODECOV_TOKEN` is set in secrets
2. Check Codecov workflow logs
3. Ensure coverage.xml was generated
4. Check Codecov API status

### Sanitizer False Positives?
1. Review sanitizer suppressions
2. Check LLVM library versions
3. Use continue-on-error for advisory sanitizers
4. File issue with details

### Performance Regression?
1. Review benchmark comparison in PR comment
2. Check if real regression or noise
3. Adjust threshold if needed
4. Run benchmarks locally to verify

## Status Badges

Add to README.md:
```markdown
[![CI](https://github.com/o2alexanderfedin/cpp-to-c-transpiler/workflows/Continuous%20Integration/badge.svg)](https://github.com/o2alexanderfedin/cpp-to-c-transpiler/actions/workflows/ci.yml)
[![Coverage](https://codecov.io/gh/o2alexanderfedin/cpp-to-c-transpiler/branch/develop/graph/badge.svg)](https://codecov.io/gh/o2alexanderfedin/cpp-to-c-transpiler)
[![Sanitizers](https://github.com/o2alexanderfedin/cpp-to-c-transpiler/workflows/Memory%20Safety%20and%20Sanitizers/badge.svg)](https://github.com/o2alexanderfedin/cpp-to-c-transpiler/actions/workflows/sanitizers.yml)
```

## Environment

| Variable | Value | Used In |
|----------|-------|---------|
| `BUILD_TYPE` | Release / Debug | All workflows |
| `LLVM_VERSION` | 15 | All workflows |
| `CODECOV_TOKEN` | (secret) | Coverage workflow |

## Caching

| Cache | Path | Key |
|-------|------|-----|
| LLVM/Clang | `/usr/lib/llvm-15` | `${{ runner.os }}-llvm-15` |

## Documentation

- **Full Guide:** [docs/CI_CD_GUIDE.md](../docs/CI_CD_GUIDE.md)
- **Build Setup:** [BUILD_SETUP.md](../BUILD_SETUP.md)
- **Project README:** [README.md](../README.md)
- **Workflow README:** [.github/workflows/README.md](.github/workflows/README.md)

## Support

**Issues with CI/CD?**
1. Check workflow logs
2. Review [CI/CD Guide](../docs/CI_CD_GUIDE.md)
3. Open issue with workflow run ID

**Links:**
- Actions: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/actions
- Codecov: https://codecov.io/gh/o2alexanderfedin/cpp-to-c-transpiler

---

**Last Updated:** 2025-12-18
