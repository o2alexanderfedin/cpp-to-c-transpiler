# Memory Safety, Undefined Behavior, and Thread Safety Testing

**Story #125** - Epic #49: Comprehensive Testing + Documentation

This document describes the comprehensive memory safety, undefined behavior (UB), and thread safety testing infrastructure for the C++ to C transpiler using industry-standard sanitizers.

## Table of Contents

- [Overview](#overview)
- [Quick Start](#quick-start)
- [Sanitizers](#sanitizers)
  - [AddressSanitizer (ASan)](#addresssanitizer-asan)
  - [UndefinedBehaviorSanitizer (UBSan)](#undefinedbehaviorsanitizer-ubsan)
  - [ThreadSanitizer (TSan)](#threadsanitizer-tsan)
  - [MemorySanitizer (MSan)](#memorysanitizer-msan)
  - [Valgrind](#valgrind)
- [Usage](#usage)
  - [Automated Testing](#automated-testing)
  - [Manual Testing](#manual-testing)
  - [CI Integration](#ci-integration)
- [Interpreting Results](#interpreting-results)
- [Common Issues and Fixes](#common-issues-and-fixes)
- [Performance Considerations](#performance-considerations)
- [Best Practices](#best-practices)

## Overview

Memory safety, undefined behavior, and thread safety are critical for production-quality code. Traditional testing cannot catch many subtle bugs that sanitizers can detect:

- **Memory Leaks**: Memory allocated but never freed
- **Use-After-Free**: Accessing memory after it has been freed
- **Buffer Overflows**: Writing beyond allocated memory bounds
- **Undefined Behavior**: Integer overflow, null pointer dereference, invalid casts
- **Data Races**: Concurrent access to shared data without synchronization
- **Uninitialized Memory**: Reading from memory before writing to it

This project uses industry-standard sanitizers from LLVM/Clang to detect these issues automatically.

### Why This Matters

The C++ to C transpiler generates C code that must be:
1. **Memory-safe**: No leaks, no use-after-free, no buffer overflows
2. **Defined behavior**: No undefined behavior patterns
3. **Thread-safe**: Safe for concurrent use where applicable
4. **Cross-platform**: Works correctly on Linux, macOS, and other platforms

Sanitizers help us achieve these goals by catching bugs that traditional testing misses.

## Quick Start

Run all sanitizers with the automated script:

```bash
./scripts/run-sanitizers.sh
```

This runs all tests with AddressSanitizer, UndefinedBehaviorSanitizer, ThreadSanitizer, and Valgrind (if available).

### Expected Output

```
[2025-12-18 10:30:00] Setting up sanitizer testing environment...
[2025-12-18 10:30:01] Compiler: Apple clang version 15.0.0
[2025-12-18 10:30:01] CPU Cores: 8
[2025-12-18 10:30:01] Project: /path/to/hupyy-cpp-to-c

[2025-12-18 10:30:02] Running AddressSanitizer (ASan)...
[✓] ASan complete: 52/52 tests passed, 0 memory issues found

[2025-12-18 10:30:45] Running UndefinedBehaviorSanitizer (UBSan)...
[✓] UBSan complete: 52/52 tests passed, 0 UB issues found

[2025-12-18 10:31:20] Running ThreadSanitizer (TSan)...
[✓] TSan complete: 1/1 tests passed, 0 thread safety issues found

[✓] SUCCESS: All tests passed with no issues detected!
✓ Zero memory leaks
✓ No undefined behavior
✓ Thread-safe code
✓ No address/memory errors

Reports available in: /path/to/hupyy-cpp-to-c/sanitizer-reports
```

## Sanitizers

### AddressSanitizer (ASan)

**What it detects:**
- Heap buffer overflow (out-of-bounds access)
- Stack buffer overflow
- Global buffer overflow
- Use-after-free
- Use-after-return
- Use-after-scope
- Double-free, invalid free
- Memory leaks

**Performance:** ~2x slowdown

**How to run:**

```bash
# Automated
./scripts/run-sanitizers.sh --asan

# Manual
cmake -B build-asan -DENABLE_ASAN=ON
cmake --build build-asan -j$(nproc)
cd build-asan && ctest -V
```

**Environment variables:**

```bash
# Detect leaks and continue on error
export ASAN_OPTIONS=detect_leaks=1:halt_on_error=0

# Full leak checking with stack traces
export ASAN_OPTIONS=detect_leaks=1:check_initialization_order=1:detect_stack_use_after_return=1
```

**Example output:**

```
=================================================================
==12345==ERROR: AddressSanitizer: heap-use-after-free on address 0x60400000efe0 at pc 0x000000428e4c
READ of size 4 at 0x60400000efe0 thread T0
    #0 0x428e4b in main example.c:15
    #1 0x7f8c0f6b3bf6 in __libc_start_main

0x60400000efe0 is located 0 bytes inside of 4-byte region [0x60400000efe0,0x60400000efe4)
freed by thread T0 here:
    #0 0x423c0c in free
    #1 0x428e0a in main example.c:12

previously allocated by thread T0 here:
    #0 0x423e3c in malloc
    #1 0x428d8a in main example.c:10

SUMMARY: AddressSanitizer: heap-use-after-free example.c:15 in main
```

### UndefinedBehaviorSanitizer (UBSan)

**What it detects:**
- Signed/unsigned integer overflow
- Division by zero
- Null pointer dereference
- Invalid casts (misaligned, downcast)
- Invalid enum values
- Out-of-bounds array access
- Shift exponent overflow
- Invalid pointer arithmetic
- Virtual table pointer violations

**Performance:** ~1.5x slowdown

**How to run:**

```bash
# Automated
./scripts/run-sanitizers.sh --ubsan

# Manual
cmake -B build-ubsan -DENABLE_UBSAN=ON
cmake --build build-ubsan -j$(nproc)
cd build-ubsan && ctest -V
```

**Environment variables:**

```bash
# Print stack traces
export UBSAN_OPTIONS=print_stacktrace=1:halt_on_error=0
```

**Example output:**

```
example.c:42:11: runtime error: signed integer overflow: 2147483647 + 1 cannot be represented in type 'int'
    #0 0x4567ab in add example.c:42
    #1 0x456890 in main example.c:50

SUMMARY: UndefinedBehaviorSanitizer: undefined-behavior example.c:42:11 in
```

### ThreadSanitizer (TSan)

**What it detects:**
- Data races (concurrent access without synchronization)
- Lock order inversions (potential deadlocks)
- Use of uninitialized mutexes
- Thread creation/join issues

**Performance:** ~5-15x slowdown

**Note:** TSan cannot be combined with ASan or MSan (mutually exclusive)

**How to run:**

```bash
# Automated
./scripts/run-sanitizers.sh --tsan

# Manual
cmake -B build-tsan -DENABLE_TSAN=ON
cmake --build build-tsan -j$(nproc)
cd build-tsan && ctest -V
```

**Environment variables:**

```bash
# Enable deadlock detection
export TSAN_OPTIONS=halt_on_error=0:second_deadlock_stack=1
```

**Example output:**

```
==================
WARNING: ThreadSanitizer: data race (pid=12345)
  Write of size 4 at 0x7b0400001234 by thread T1:
    #0 increment worker.c:15
    #1 thread_func worker.c:25

  Previous read of size 4 at 0x7b0400001234 by main thread:
    #0 print_value main.c:42
    #1 main main.c:50

  Location is global 'shared_counter' of size 4 at 0x7b0400001234 (example+0x000000001234)

SUMMARY: ThreadSanitizer: data race worker.c:15 in increment
```

### MemorySanitizer (MSan)

**What it detects:**
- Use of uninitialized memory (reads from uninitialized variables)

**Performance:** ~3x slowdown

**Note:** Requires full rebuild of all dependencies with MSan

**How to run:**

```bash
# Manual only (requires special build)
cmake -B build-msan -DENABLE_MSAN=ON
cmake --build build-msan -j$(nproc)
cd build-msan && ctest -V
```

**Note:** MSan is not included in the automated script due to dependency rebuild requirements.

### Valgrind

**What it detects:**
- Memory leaks
- Invalid memory access
- Use of uninitialized values
- Invalid free/delete

**Performance:** ~10-50x slowdown

**Platform support:**
- Full support: Linux (x86_64, ARM)
- Limited support: macOS Intel
- Not supported: macOS Apple Silicon (use ASan instead)

**How to run:**

```bash
# Automated (if available)
./scripts/run-sanitizers.sh --valgrind

# Manual
valgrind --leak-check=full --show-leak-kinds=all --track-origins=yes ./build/MyTest
```

**Example output:**

```
==12345== HEAP SUMMARY:
==12345==     in use at exit: 40 bytes in 1 blocks
==12345==   total heap usage: 5 allocs, 4 frees, 1,080 bytes allocated
==12345==
==12345== 40 bytes in 1 blocks are definitely lost in loss record 1 of 1
==12345==    at 0x4C2FB0F: malloc (vg_replace_malloc.c:299)
==12345==    by 0x400567: main (example.c:10)
==12345==
==12345== LEAK SUMMARY:
==12345==    definitely lost: 40 bytes in 1 blocks
==12345==    indirectly lost: 0 bytes in 0 blocks
==12345==      possibly lost: 0 bytes in 0 blocks
==12345==    still reachable: 0 bytes in 0 blocks
==12345==         suppressed: 0 bytes in 0 blocks
```

## Usage

### Automated Testing

The `scripts/run-sanitizers.sh` script provides comprehensive automated testing:

```bash
# Run all sanitizers (default)
./scripts/run-sanitizers.sh

# Run specific sanitizers
./scripts/run-sanitizers.sh --asan --ubsan
./scripts/run-sanitizers.sh --tsan

# Options
./scripts/run-sanitizers.sh --fail-fast    # Stop on first failure
./scripts/run-sanitizers.sh --verbose      # Show detailed output
./scripts/run-sanitizers.sh --report       # Generate HTML report

# Combine options
./scripts/run-sanitizers.sh --asan --ubsan --fail-fast --verbose
```

**Output locations:**
- Text reports: `sanitizer-reports/*.txt`
- HTML report: `sanitizer-reports/sanitizer-report.html`
- Logs: `sanitizer-reports/sanitizer-run.log`
- Build artifacts: `build-sanitizers/{asan,ubsan,tsan}/`

### Manual Testing

For individual sanitizer testing or custom configurations:

**AddressSanitizer:**

```bash
cmake -B build-asan -DENABLE_ASAN=ON -DCMAKE_BUILD_TYPE=Debug
cmake --build build-asan -j$(nproc)
cd build-asan

# Run specific test
ASAN_OPTIONS=detect_leaks=1 ./ExceptionIntegrationTest

# Run all tests
ctest -V
```

**UndefinedBehaviorSanitizer:**

```bash
cmake -B build-ubsan -DENABLE_UBSAN=ON -DCMAKE_BUILD_TYPE=Debug
cmake --build build-ubsan -j$(nproc)
cd build-ubsan

# Run with stack traces
UBSAN_OPTIONS=print_stacktrace=1 ./ValidationTest
```

**ThreadSanitizer:**

```bash
cmake -B build-tsan -DENABLE_TSAN=ON -DCMAKE_BUILD_TYPE=Debug
cmake --build build-tsan -j$(nproc)
cd build-tsan

# Run thread safety tests
./ExceptionThreadSafetyTest
```

**Multiple sanitizers (ASan + UBSan):**

```bash
cmake -B build-multi \
  -DENABLE_ASAN=ON \
  -DENABLE_UBSAN=ON \
  -DCMAKE_BUILD_TYPE=Debug
cmake --build build-multi -j$(nproc)
cd build-multi && ctest -V
```

### CI Integration

Sanitizers run automatically on every commit via GitHub Actions.

See `.github/workflows/sanitizers.yml` for the CI configuration.

**CI workflow:**
1. Build with ASan + UBSan
2. Run all tests
3. Build with TSan
4. Run thread safety tests
5. Upload reports as artifacts
6. Fail build if issues found

**Checking CI results:**
1. Go to the Actions tab in GitHub
2. Click on the latest workflow run
3. Check "Sanitizer Tests" job
4. Download artifacts for detailed reports

## Interpreting Results

### Success

When all sanitizers pass, you'll see:

```
[✓] SUCCESS: All tests passed with no issues detected!
✓ Zero memory leaks
✓ No undefined behavior
✓ Thread-safe code
✓ No address/memory errors
```

### Failure

When issues are found:

```
[✗] FAILURE: 3 issue(s) detected
Please review the reports in: /path/to/sanitizer-reports
```

**Next steps:**
1. Check the text reports in `sanitizer-reports/`
2. Open the HTML report: `sanitizer-reports/sanitizer-report.html`
3. Identify the failing test and error type
4. Review the stack trace
5. Fix the issue
6. Re-run sanitizers to verify fix

### Reading Stack Traces

Sanitizers provide detailed stack traces. Example:

```
    #0 0x423c0c in free (/lib/x86_64-linux-gnu/libc.so.6+0x8dc0c)
    #1 0x428e0a in main example.c:12:5
    #2 0x7f8c0f6b3bf6 in __libc_start_main (/lib/x86_64-linux-gnu/libc.so.6+0x21bf6)
```

Reading from bottom to top:
1. Program started (`__libc_start_main`)
2. Called `main` at `example.c:12:5`
3. Called `free` (where the error occurred)

### Common Patterns

**Use-after-free:**
```
ERROR: AddressSanitizer: heap-use-after-free
  - Look for "freed by thread" and "previously allocated by thread"
  - Fix: Don't use memory after freeing it
```

**Memory leak:**
```
Direct leak of 40 bytes in 1 blocks
  - Look for allocation site in stack trace
  - Fix: Add corresponding free/delete
```

**Data race:**
```
WARNING: ThreadSanitizer: data race
  - Look for "Write of size" and "Previous read of size"
  - Fix: Add mutex/lock or use atomic operations
```

**Integer overflow:**
```
runtime error: signed integer overflow
  - Look for the operation that overflowed
  - Fix: Use unsigned types or check before operation
```

## Common Issues and Fixes

### Issue: False Positives

**Problem:** Sanitizer reports an issue that isn't actually a bug.

**Solution:**
1. Verify it's truly a false positive (most reports are real bugs)
2. Use suppression files (last resort)
3. File a bug report with the sanitizer project

**Suppression example (ASan):**

Create `asan_suppressions.txt`:
```
leak:known_third_party_leak
```

Run with:
```bash
ASAN_OPTIONS=suppressions=asan_suppressions.txt ./MyTest
```

### Issue: Tests Fail Only with Sanitizers

**Problem:** Tests pass normally but fail with sanitizers enabled.

**Cause:** Tests may have subtle bugs (undefined behavior) that only manifest with sanitizers.

**Solution:**
1. The bug was always there; sanitizers found it
2. Fix the underlying issue
3. Don't disable sanitizers for that test

### Issue: Sanitizer Build Fails

**Problem:** CMake configuration or build fails with sanitizers.

**Solution:**

```bash
# Ensure using Clang compiler
export CC=clang
export CXX=clang++

# Clean build directory
rm -rf build-asan
cmake -B build-asan -DENABLE_ASAN=ON
cmake --build build-asan
```

### Issue: Performance Too Slow

**Problem:** Sanitizer tests take too long.

**Solution:**
1. Run only necessary sanitizers: `./scripts/run-sanitizers.sh --asan`
2. Run on subset of tests
3. Use parallel execution (script does this automatically)
4. Accept that comprehensive checking takes time

### Issue: Leaks in Third-Party Libraries

**Problem:** Sanitizers report leaks in LLVM/Clang libraries.

**Solution:**
1. These are often known issues in third-party code
2. Use suppression files
3. Focus on leaks in your code (transpiler source)

## Performance Considerations

### Overhead Summary

| Sanitizer | Slowdown | Memory Overhead | Notes |
|-----------|----------|-----------------|-------|
| ASan | 2x | 3x | Best all-around detector |
| UBSan | 1.5x | Minimal | Very low overhead |
| TSan | 5-15x | 5-10x | Only for threaded tests |
| MSan | 3x | 2x | Requires full rebuild |
| Valgrind | 10-50x | Minimal | Slowest, most thorough |

### Optimization Tips

1. **Run regularly but not on every build**
   - Use CI for automatic checking
   - Run locally before committing

2. **Parallel execution**
   - The script uses all CPU cores by default
   - Reduces total runtime significantly

3. **Targeted testing**
   - Run specific sanitizers for specific issues
   - Use `--asan` for memory issues, `--tsan` for threading

4. **Build once, test multiple times**
   - Sanitizer builds are cached in `build-sanitizers/`
   - Subsequent runs are faster

### Production Impact

**Important:** Sanitizers are for testing only. Never ship sanitizer-enabled builds to production.

For production:
```bash
cmake -B build-release -DCMAKE_BUILD_TYPE=Release
cmake --build build-release
```

This builds optimized code without sanitizer overhead.

## Best Practices

### Development Workflow

1. **Before committing:**
   ```bash
   ./scripts/run-sanitizers.sh --asan --ubsan
   ```

2. **Before PR:**
   ```bash
   ./scripts/run-sanitizers.sh  # All sanitizers
   ```

3. **CI automatically runs on every push**

### Writing Tests

1. **Make tests sanitizer-friendly:**
   - Always free allocated memory
   - Initialize all variables
   - Use proper synchronization for threads

2. **Don't suppress sanitizer warnings:**
   - Fix the underlying issue instead
   - Suppressions hide real bugs

3. **Test edge cases:**
   - Null pointers
   - Empty containers
   - Boundary conditions

### Debugging Sanitizer Issues

1. **Enable detailed output:**
   ```bash
   ASAN_OPTIONS=verbosity=1 ./MyTest
   ```

2. **Get full stack traces:**
   ```bash
   UBSAN_OPTIONS=print_stacktrace=1 ./MyTest
   ```

3. **Run under debugger:**
   ```bash
   lldb ./build-asan/MyTest
   (lldb) run
   (lldb) bt  # When sanitizer stops
   ```

4. **Reproduce minimally:**
   - Isolate the failing test
   - Create minimal reproduction
   - Fix and verify

### Integration with Other Tools

Sanitizers work well with:

- **Code coverage:** Run coverage with sanitizers for comprehensive testing
- **Continuous integration:** Automated sanitizer runs on every commit
- **Benchmarking:** Measure sanitizer overhead (see `benchmarks/`)

## Success Criteria

For Story #125 to be complete:

- [ ] Zero memory leaks detected by ASan
- [ ] Zero undefined behavior detected by UBSan
- [ ] Zero data races detected by TSan
- [ ] All 1,000+ tests pass with sanitizers
- [ ] CI integration running on every commit
- [ ] Documentation complete and comprehensive
- [ ] Performance overhead documented (<10% for typical workloads)

## Resources

### Official Documentation

- [AddressSanitizer](https://clang.llvm.org/docs/AddressSanitizer.html)
- [UndefinedBehaviorSanitizer](https://clang.llvm.org/docs/UndefinedBehaviorSanitizer.html)
- [ThreadSanitizer](https://clang.llvm.org/docs/ThreadSanitizer.html)
- [MemorySanitizer](https://clang.llvm.org/docs/MemorySanitizer.html)
- [Valgrind](https://valgrind.org/docs/manual/manual.html)

### Further Reading

- [Google Sanitizers Wiki](https://github.com/google/sanitizers/wiki)
- [LLVM Sanitizer Coverage](https://clang.llvm.org/docs/SanitizerCoverage.html)
- [Thread Safety Analysis](https://clang.llvm.org/docs/ThreadSafetyAnalysis.html)

## Support

For issues or questions:

1. Check this documentation
2. Review the [Common Issues](#common-issues-and-fixes) section
3. Check sanitizer reports in `sanitizer-reports/`
4. Open an issue on GitHub with:
   - Sanitizer output
   - Test name
   - Platform/OS information
   - Steps to reproduce

---

**Story #125** - Memory Safety, UB, and Thread Safety Testing
**Epic #49** - Comprehensive Testing + Documentation

Last updated: 2025-12-18
