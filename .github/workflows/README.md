# GitHub Actions Workflows

This directory contains the CI/CD workflows for the C++ to C transpiler project.

## Workflows

### 1. Continuous Integration (`ci.yml`)
- **Runs on:** Every push and PR to develop/main
- **Duration:** ~10-15 minutes
- **Purpose:** Fast feedback on code changes
- **Jobs:**
  - Unit tests (70+ tests)
  - Integration tests
  - Real-world tests
  - Multi-platform matrix tests (Linux, macOS, Windows)

### 2. Code Coverage (`coverage.yml`)
- **Runs on:** Push and PR to develop/main
- **Duration:** ~15-20 minutes
- **Purpose:** Track test coverage over time
- **Features:**
  - Generates HTML coverage reports
  - Uploads to Codecov
  - Comments coverage on PRs
  - Enforces 70% coverage threshold

### 3. Memory Safety and Sanitizers (`sanitizers.yml`)
- **Runs on:** Push/PR + nightly at 2 AM UTC
- **Duration:** ~40-60 minutes
- **Purpose:** Detect memory errors and undefined behavior
- **Tools:**
  - AddressSanitizer (ASan)
  - UndefinedBehaviorSanitizer (UBSan)
  - ThreadSanitizer (TSan)
  - MemorySanitizer (MSan)
  - Valgrind

### 4. Benchmark Regression Detection (`benchmark-regression.yml`)
- **Runs on:** Push and PR to develop/main
- **Duration:** ~20-30 minutes
- **Purpose:** Detect performance regressions
- **Features:**
  - Compares with baseline benchmarks
  - Tracks performance trends
  - Comments results on PRs
  - Fails on >5% regression

### 5. GitHub Pages (`pages.yml`)
- **Runs on:** Push to main
- **Purpose:** Deploy documentation to GitHub Pages

## Quick Reference

### Status Badges

Add these to your README.md:

```markdown
[![CI](https://github.com/alexanderfedin/hupyy-cpp-to-c/workflows/Continuous%20Integration/badge.svg)](https://github.com/alexanderfedin/hupyy-cpp-to-c/actions/workflows/ci.yml)
[![Coverage](https://codecov.io/gh/alexanderfedin/hupyy-cpp-to-c/branch/develop/graph/badge.svg)](https://codecov.io/gh/alexanderfedin/hupyy-cpp-to-c)
[![Sanitizers](https://github.com/alexanderfedin/hupyy-cpp-to-c/workflows/Memory%20Safety%20and%20Sanitizers/badge.svg)](https://github.com/alexanderfedin/hupyy-cpp-to-c/actions/workflows/sanitizers.yml)
```

### Running Workflows Manually

Go to: Actions tab → Select workflow → Run workflow button

### Viewing Results

- **Actions Tab:** https://github.com/alexanderfedin/hupyy-cpp-to-c/actions
- **Codecov Dashboard:** https://codecov.io/gh/alexanderfedin/hupyy-cpp-to-c

## Configuration

All workflows use:
- **LLVM Version:** 15
- **Build Type:** Release (CI), Debug (Coverage/Sanitizers)
- **Parallel Jobs:** Up to available CPU cores
- **Caching:** LLVM/Clang installations cached

## Documentation

For detailed information, see:
- [CI/CD Guide](../docs/CI_CD_GUIDE.md) - Comprehensive documentation
- [Build Setup](../BUILD_SETUP.md) - Local build instructions
- [Project README](../README.md) - Project overview

## Support

Issues with CI/CD? Check:
1. Workflow logs in Actions tab
2. [CI/CD Guide](../docs/CI_CD_GUIDE.md) troubleshooting section
3. Open an issue with workflow run ID

---

**Last Updated:** 2025-12-18
