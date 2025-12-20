# Testing and Code Coverage Guide

This document describes the testing infrastructure and code coverage reporting for the cpptoc C++ to C transpiler project.

## Table of Contents

- [Overview](#overview)
- [Test Suite](#test-suite)
- [Running Tests](#running-tests)
- [Code Coverage](#code-coverage)
- [Writing Tests](#writing-tests)
- [Continuous Integration](#continuous-integration)
- [Troubleshooting](#troubleshooting)

## Overview

The cpptoc project uses a comprehensive testing approach with:

- **492 test functions** covering all major components
- **1,956 assertions** verifying correctness
- Unit tests for individual components
- Integration tests for end-to-end workflows
- Code coverage reporting with gcov/lcov

### Test Framework

Tests are written using a lightweight assertion-based framework without external dependencies. Each test executable is self-contained and can be run independently.

## Test Suite

### Test Organization

Tests are organized by Epic and Story, corresponding to the project's SCRUM-based development:

#### Epic #2 & #3: Core Transpilation
- `CppToCVisitorTest` - AST visitor functionality
- `NameManglerTest` - Name mangling for C compatibility
- `OverloadResolutionTest` - Function overload handling
- `TemplateExtractorTest` - Template instantiation extraction
- `MonomorphizationTest` - Template monomorphization
- `STLIntegrationTest` - STL container support
- `TranslationIntegrationTest` - End-to-end translation

#### Epic #4: Code Generation
- `CodeGeneratorTest` - Code generation logic
- `ValidationTest` - Compilation and behavioral validation

#### Epic #5: RAII & Destructors
- `CFGAnalysisTest` - Control flow graph analysis
- `FunctionExitDestructorTest` - Function exit cleanup
- `EarlyReturnDestructorTest` - Early return handling
- `NestedScopeDestructorTest` - Nested scope cleanup
- `GotoDestructorTest` - Goto statement handling
- `LoopDestructorTest` - Loop break/continue handling
- `RAIIIntegrationTest` - RAII integration testing

#### Epic #6: Inheritance
- `InheritanceTest` - Single inheritance support
- `VirtualBaseDetectionTest` - Virtual inheritance detection
- `VirtualBaseOffsetTableTest` - Virtual base offset tables
- `VTTGeneratorTest` - Virtual table tables (VTT)
- `ConstructorSplitterTest` - Constructor splitting (C1/C2)

#### Epic #7: Constructors/Destructors
- `MemberInitListTest` - Member initialization lists

#### Epic #10: Exception Handling
- `ExceptionFrameTest` - Exception frame structures
- `ActionTableGeneratorTest` - Exception action tables
- `TryCatchTransformerTest` - Try-catch block transformation
- `ThrowTranslatorTest` - Throw expression translation
- `CatchHandlerTypeMatchingTest` - Catch handler matching
- `ExceptionRuntimeTest` - Exception runtime library
- `ExceptionIntegrationTest` - Exception integration
- `ExceptionThreadSafetyTest` - Thread safety
- `ExceptionPerformanceTest` - Performance benchmarks

#### Epic #11: RTTI
- `TypeInfoGeneratorTest` - type_info generation
- `TypeidTranslatorTest` - typeid operator translation
- `DynamicCastTranslatorTest` - dynamic_cast support
- `HierarchyTraversalTest` - Hierarchy traversal
- `DynamicCastCrossCastTest` - Cross-casting
- `CrossCastTraversalTest` - Cross-cast traversal

#### Epic #16: Runtime Optimization
- `RuntimeModeInlineTest` - Inline runtime mode
- `RuntimeModeLibraryTest` - Library runtime mode
- `RuntimeFeatureFlagsTest` - Feature flags
- `SizeOptimizationTest` - Size optimization

#### Epic #19: Header Generation
- `HeaderSeparatorTest` - Header/implementation separation
- `IncludeGuardGeneratorTest` - Include guard generation
- `ForwardDeclTest` - Forward declarations
- `DependencyAnalyzerTest` - Dependency tracking
- `FileOutputManagerTest` - File output system
- `IntegrationTest` - Header generation integration

#### Epic #41: Virtual Functions
- `VirtualMethodAnalyzerTest` - Virtual method detection
- `VtableGeneratorTest` - Vtable generation
- `VptrInjectorTest` - Vptr field injection
- `OverrideResolverTest` - Override resolution
- `VtableInitializerTest` - Vtable initialization
- `VirtualCallTranslatorTest` - Virtual call translation
- `PureVirtualHandlerTest` - Pure virtual functions
- `VirtualDestructorHandlerTest` - Virtual destructors
- `VirtualFunctionIntegrationTest` - Virtual function integration

#### Epic #46: Coroutines
- `CoroutineDetectorTest` - Coroutine detection
- `SuspendPointIdentifierTest` - Suspend point identification
- `StateMachineTransformerTest` - State machine transformation
- `PromiseTranslatorTest` - Promise object translation
- `ResumeDestroyFunctionTest` - Resume/destroy functions
- `FrameAllocationTest` - Frame allocation
- `CoroutineIntegrationTest` - Coroutine integration

### Test Statistics

- **Total Test Executables**: 60+
- **Total Test Functions**: 492
- **Total Assertions**: 1,956
- **Coverage Target**: 80%+ line coverage

## Running Tests

### Quick Start

Run all tests with default settings:

```bash
cd build
make
./CppToCVisitorTest
./NameManglerTest
# ... run other tests
```

### Build and Run All Tests

```bash
# Build project
mkdir -p build
cd build
cmake ..
make -j$(nproc)

# Run all tests
for test in *Test; do
    echo "Running $test..."
    ./"$test"
done
```

### Run Specific Test Suite

```bash
cd build
./CppToCVisitorTest          # Run visitor tests
./ExceptionIntegrationTest   # Run exception tests
./VirtualFunctionIntegrationTest  # Run virtual function tests
```

## Code Coverage

### Prerequisites

Install coverage tools:

```bash
# macOS
brew install lcov

# Ubuntu/Debian
sudo apt-get install lcov

# Fedora/RHEL
sudo dnf install lcov
```

### Generate Coverage Report

Use the provided script to generate a comprehensive coverage report:

```bash
./scripts/generate_coverage.sh
```

This script will:
1. Configure CMake with coverage enabled
2. Build all tests with instrumentation
3. Run all test executables
4. Collect coverage data
5. Generate HTML and text reports

### Script Options

```bash
# Clean build before generating coverage
./scripts/generate_coverage.sh --clean

# Use custom build directory
./scripts/generate_coverage.sh --build-dir my-build

# Enable verbose output
./scripts/generate_coverage.sh --verbose

# Show help
./scripts/generate_coverage.sh --help
```

### View Coverage Report

Open the HTML coverage report in your browser:

```bash
./scripts/view_coverage.sh
```

Or view summary in terminal:

```bash
./scripts/view_coverage.sh --summary
```

Generate text report:

```bash
./scripts/view_coverage.sh --text
```

### Manual Coverage Generation

If you prefer to run coverage manually:

```bash
# 1. Configure with coverage enabled
mkdir -p build-coverage
cd build-coverage
cmake -DENABLE_COVERAGE=ON ..

# 2. Build
make -j$(nproc)

# 3. Zero coverage counters
lcov --directory . --zerocounters

# 4. Run tests
for test in *Test; do ./"$test"; done

# 5. Capture coverage data
lcov --directory . --capture --output-file coverage.info

# 6. Filter out system headers and test files
lcov --remove coverage.info '/usr/*' '*/tests/*' '*/build/*' \
     --output-file coverage.info.cleaned

# 7. Generate HTML report
genhtml coverage.info.cleaned --output-directory coverage \
        --demangle-cpp --title "cpptoc Coverage"

# 8. Open report
open coverage/index.html  # macOS
xdg-open coverage/index.html  # Linux
```

### Coverage Targets

The project aims for:

- **Line Coverage**: 80%+
- **Function Coverage**: 85%+
- **Branch Coverage**: 75%+

### Understanding Coverage Reports

#### HTML Report

The HTML report (`coverage/index.html`) provides:
- Overall coverage percentages
- Per-directory breakdown
- Per-file coverage details
- Line-by-line coverage visualization
  - Green: Code executed
  - Red: Code not executed
  - Orange: Partially covered branches

#### Text Report

The text report provides a summary suitable for CI/CD:
```
Overall coverage rate:
  lines......: 84.2% (5234 of 6215 lines)
  functions..: 87.5% (412 of 471 functions)
  branches...: 76.8% (3142 of 4092 branches)
```

## Writing Tests

### Test Structure

Tests follow a consistent structure:

```cpp
#include <cassert>
#include <iostream>

// Test fixture setup
void setup() {
    // Initialize test environment
}

// Individual test cases
void test_basic_functionality() {
    // Arrange
    auto obj = create_test_object();

    // Act
    auto result = obj.perform_action();

    // Assert
    assert(result == expected_value);
}

void test_error_handling() {
    // Test error conditions
    assert(handles_error_correctly());
}

// Test runner
int main() {
    std::cout << "Running MyComponent tests...\n";

    setup();

    test_basic_functionality();
    test_error_handling();
    // ... more tests

    std::cout << "All tests passed!\n";
    return 0;
}
```

### Best Practices

1. **Test Independence**: Each test should be independent and not rely on other tests
2. **Descriptive Names**: Use clear, descriptive test function names
3. **Arrange-Act-Assert**: Follow the AAA pattern
4. **Edge Cases**: Test boundary conditions and error cases
5. **Coverage**: Aim for high coverage of critical paths

### Example Test

```cpp
void test_name_mangling_for_overloaded_functions() {
    // Arrange
    NameMangler mangler;
    std::string func_name = "process";
    std::vector<std::string> param_types = {"int", "double"};

    // Act
    std::string mangled = mangler.mangle(func_name, param_types);

    // Assert
    assert(mangled == "process_i_d");
    assert(mangled != func_name);  // Should be different from original
}
```

## Continuous Integration

### GitHub Actions Integration

Add coverage reporting to your CI pipeline:

```yaml
name: CI with Coverage

on: [push, pull_request]

jobs:
  test-with-coverage:
    runs-on: ubuntu-latest

    steps:
    - uses: actions/checkout@v2

    - name: Install dependencies
      run: |
        sudo apt-get update
        sudo apt-get install -y lcov cmake build-essential

    - name: Generate coverage
      run: |
        ./scripts/generate_coverage.sh --clean

    - name: Upload coverage to Codecov
      uses: codecov/codecov-action@v2
      with:
        file: build-coverage/coverage.info.cleaned
        fail_ci_if_error: true
```

### Coverage Badges

Add coverage badges to your README:

```markdown
[![Coverage](https://codecov.io/gh/username/cpptoc/branch/main/graph/badge.svg)](https://codecov.io/gh/username/cpptoc)
```

## Troubleshooting

### Common Issues

#### 1. "lcov: not found"

**Problem**: Coverage tools not installed

**Solution**:
```bash
# macOS
brew install lcov

# Linux
sudo apt-get install lcov
```

#### 2. "No coverage data found"

**Problem**: Tests not built with coverage instrumentation

**Solution**: Ensure `ENABLE_COVERAGE=ON` is set:
```bash
cmake -DENABLE_COVERAGE=ON ..
```

#### 3. Low coverage numbers

**Problem**: Not all tests were run

**Solution**: Ensure all test executables are run before collecting coverage:
```bash
# Run all tests
for test in *Test; do ./"$test"; done

# Then collect coverage
lcov --directory . --capture --output-file coverage.info
```

#### 4. "Branch coverage not available"

**Problem**: Compiler doesn't support branch coverage

**Solution**: Use GCC 8+ or Clang 10+ with appropriate flags

#### 5. Tests fail during coverage run

**Problem**: Tests may have issues or environment setup problems

**Solution**:
- Run tests individually to identify failing tests
- Check test output with `--verbose` flag
- Ensure all dependencies are available

### Debug Coverage Issues

Enable verbose output:
```bash
./scripts/generate_coverage.sh --verbose
```

Check coverage data files:
```bash
ls -la build-coverage/*.gcno  # Should have .gcno files after build
ls -la build-coverage/*.gcda  # Should have .gcda files after test run
```

Manually verify coverage capture:
```bash
cd build-coverage
lcov --directory . --capture --output-file test.info
lcov --list test.info
```

## Advanced Topics

### Incremental Coverage

Run coverage on specific components:

```bash
# Only run RAII tests
cd build-coverage
./CFGAnalysisTest
./FunctionExitDestructorTest
./RAIIIntegrationTest

# Collect coverage for just these tests
lcov --directory . --capture --output-file raii_coverage.info
```

### Coverage Exclusion

Exclude specific code from coverage analysis by adding comments:

```cpp
// LCOV_EXCL_START
void debug_only_function() {
    // This code won't be counted in coverage
}
// LCOV_EXCL_STOP

void another_function() {
    // LCOV_EXCL_LINE
    assert(false && "Should never happen");
}
```

### Differential Coverage

Compare coverage between branches:

```bash
# Generate coverage for main branch
git checkout main
./scripts/generate_coverage.sh --build-dir build-main

# Generate coverage for feature branch
git checkout feature-branch
./scripts/generate_coverage.sh --build-dir build-feature

# Compare
lcov --diff build-main/coverage.info.cleaned \
     build-feature/coverage.info.cleaned \
     --output-file diff.info
```

## Resources

- [gcov Documentation](https://gcc.gnu.org/onlinedocs/gcc/Gcov.html)
- [lcov Project](http://ltp.sourceforge.net/coverage/lcov.php)
- [Coverage Best Practices](https://testing.googleblog.com/2020/08/code-coverage-best-practices.html)

## Summary

The cpptoc project has a robust testing infrastructure with 492 test functions and 1,956 assertions. Code coverage reporting is integrated and easy to use with the provided scripts. Target coverage is 80%+ for lines, 85%+ for functions, and 75%+ for branches.

For questions or issues with testing, please refer to the project documentation or open an issue on GitHub.
