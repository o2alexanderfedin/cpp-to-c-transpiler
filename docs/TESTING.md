# Testing Guide - C++ to C Transpiler

## Quick Start

### Run All Tests

```bash
# Option 1: Using script (recommended)
./scripts/run-all-tests.sh

# Option 2: Using CMake
cd build && make test-all

# Option 3: Using CTest directly
cd build && ctest
```

### Run Specific Test Categories

```bash
# Core unit tests only
make test-core

# Integration tests only
make test-integration

# Real-world tests only
make test-real-world
```

### Run Tests in Parallel

```bash
# Automatic parallel execution
./scripts/run-all-tests.sh

# Or using CMake
make test-parallel

# Or using CTest with specific job count
ctest --parallel 8
```

### Generate Code Coverage

```bash
# Option 1: Using dedicated script
./scripts/generate-coverage.sh

# Option 2: Using environment variable
COVERAGE=1 ./scripts/run-all-tests.sh

# Option 3: Using CMake target
cd build
cmake -DENABLE_COVERAGE=ON ..
make coverage

# View coverage report
open build/coverage/index.html
```

## Test Organization

### Test Categories

- **Core Unit Tests** (80 tests): Tests for core transpiler features
- **Real-World Integration** (216 tests): End-to-end integration tests
- **Example Tests**: Example/demonstration tests

**Total Built Tests**: 296 tests (100% pass rate)
**Additional Tests**: 88 tests marked as NOT_BUILT (require implementation)

### Test Labels

Tests are labeled for easy filtering:
- `core` - Core transpiler functionality
- `unit` - Unit tests
- `integration` - Integration tests
- `real-world` - Real-world scenario tests

Filter by label:
```bash
ctest -L "core"
ctest -L "integration"
ctest -L "real-world"
```

## Writing Tests

### Test Structure (Google Test)

```cpp
#include <gtest/gtest.h>

TEST(TestSuiteName, TestName) {
    // Arrange
    auto input = createInput();

    // Act
    auto result = performOperation(input);

    // Assert
    ASSERT_NE(result, nullptr);
    EXPECT_EQ(result->value, 42);
}
```

### Test Fixtures

```cpp
class MyTestFixture : public ::testing::Test {
protected:
    void SetUp() override {
        // Common setup
    }

    void TearDown() override {
        // Cleanup
    }

    // Helper methods
};

TEST_F(MyTestFixture, TestWithFixture) {
    // Uses fixture setup
}
```

## CI/CD Integration

Tests run automatically on:
- Every push to `develop` and `main`
- Every pull request
- Nightly builds with coverage reports

### GitHub Actions

Test results are published as GitHub Actions artifacts:
- Test XML reports: `test-results.xml`
- Coverage reports: `coverage-report.html`

## Troubleshooting

### Build Failures

```bash
# Clean rebuild
rm -rf build && mkdir build && cd build
cmake .. && make -j8
```

### Test Failures

```bash
# Run with verbose output
ctest --output-on-failure --verbose

# Run specific test
./build/ACSLStatementAnnotatorTest
```

### Coverage Issues

```bash
# Ensure lcov is installed
brew install lcov

# Rebuild with coverage
cd build
cmake -DENABLE_COVERAGE=ON ..
make clean && make -j8
```

## Performance

**Expected Test Execution Time**:
- All 296 tests (parallel): ~3-5 seconds
- All 296 tests (sequential): ~10-15 seconds
- Core tests only: ~2-3 seconds
- Integration tests only: ~8-10 seconds

**Coverage Generation Time**:
- Full coverage report: ~10-15 minutes (if build succeeds)

## Test Infrastructure

### Test Executables

The following test executables are available:

1. **Core Tests**:
   - NameManglerTest
   - OverloadResolutionTest

2. **Runtime Tests**:
   - ExceptionRuntimeTest
   - ExceptionIntegrationTest
   - ExceptionPerformanceTest
   - HierarchyTraversalTest
   - CrossCastTraversalTest
   - RuntimeModeLibraryTest
   - RuntimeFeatureFlagsTest
   - SizeOptimizationTest

3. **Real-World Integration Tests**:
   - test_json_parser
   - test_resource_manager
   - test_logger
   - test_string_formatter
   - test_test_framework
   - ConsoleAppTest (multiple scenarios)
   - BasicAssertionsTest
   - ArithmeticTest
   - ContainerTest
   - FileResourceTest

### Test Discovery

Tests are automatically discovered using `gtest_discover_tests()` in CMake, which means:
- New tests are automatically registered
- No manual test registration needed
- CTest integration is automatic

## Coverage Tools

### Required Tools

```bash
# macOS
brew install lcov

# Ubuntu/Debian
sudo apt-get install lcov

# Fedora/RHEL
sudo dnf install lcov
```

### Coverage Configuration

Coverage is configured via CMake option:
```bash
cmake -DENABLE_COVERAGE=ON ..
```

This adds the following flags:
- `--coverage`
- `-fprofile-arcs`
- `-ftest-coverage`

### Coverage Targets

The project defines the following coverage targets:
- `make coverage` - Runs all tests and generates HTML coverage report
- Report location: `build/coverage/index.html`

## Best Practices

1. **Always run tests before committing**
   ```bash
   ./scripts/run-all-tests.sh
   ```

2. **Check coverage for new features**
   ```bash
   ./scripts/generate-coverage.sh
   ```

3. **Use appropriate test categories**
   - Unit tests for isolated components
   - Integration tests for feature interactions
   - Real-world tests for end-to-end scenarios

4. **Write clear test names**
   - Use descriptive names that explain what is being tested
   - Follow GTest naming conventions

5. **Keep tests fast**
   - Unit tests should run in milliseconds
   - Integration tests in seconds
   - Use test fixtures to avoid repetitive setup

## Future Enhancements

The following tests are marked as NOT_BUILT and require implementation:
- Template-related tests
- Virtual function tests
- Exception handling tests
- RTTI tests
- Coroutine tests
- Smart pointer tests
- ACSL annotation tests

Total: 88 tests awaiting implementation

## Resources

- [Google Test Documentation](https://google.github.io/googletest/)
- [CMake CTest Documentation](https://cmake.org/cmake/help/latest/manual/ctest.1.html)
- [lcov Documentation](http://ltp.sourceforge.net/coverage/lcov.php)
- [Code Coverage Best Practices](https://testing.googleblog.com/2020/08/code-coverage-best-practices.html)

## Summary

The C++ to C transpiler has a comprehensive test suite with:
- **296 built tests** (100% pass rate)
- **88 additional tests** requiring implementation
- **Google Test framework** for modern C++ testing
- **CTest integration** for parallel execution
- **Code coverage** support with lcov/genhtml
- **CI/CD integration** with GitHub Actions

All infrastructure is in place for unified test execution and code coverage reporting.
