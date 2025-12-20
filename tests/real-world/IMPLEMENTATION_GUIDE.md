# Real-World Testing Implementation Guide

This guide provides detailed instructions for implementing, running, and extending the real-world testing suite for the C++ to C transpiler.

## Table of Contents

1. [Quick Start](#quick-start)
2. [Project Structure](#project-structure)
3. [Building Projects](#building-projects)
4. [Running Tests](#running-tests)
5. [Adding New Projects](#adding-new-projects)
6. [Transpilation Process](#transpilation-process)
7. [Troubleshooting](#troubleshooting)
8. [Best Practices](#best-practices)

## Quick Start

### Prerequisites

- CMake 3.20+
- C++17 compiler (g++ or clang++)
- C99 compiler (gcc or clang)
- cpptoc transpiler (built from main project)

### Build All Projects

```bash
cd tests/real-world
./build-all-projects.sh
```

### Run All Tests

```bash
./test-all-projects.sh
```

### Transpile and Validate

```bash
cd ../..
./scripts/test-real-world.sh
```

## Project Structure

Each real-world project follows this standard structure:

```
<project>/
├── README.md          # Project description and features
├── CMakeLists.txt     # Build configuration
├── include/           # Header files
│   └── *.h
├── src/              # Source files (if not header-only)
│   └── *.cpp
├── tests/            # Test files
│   ├── test_*.cpp   # Unit tests
│   └── examples.cpp # Usage examples
└── expected/         # Expected outputs (optional)
    └── *.txt
```

### Why This Structure?

1. **Separation of Concerns**: Headers, source, and tests are clearly separated
2. **Standard CMake**: Follows CMake best practices
3. **Easy Navigation**: Developers can quickly find what they need
4. **Transpilation Friendly**: Clear separation helps the transpiler
5. **Testable**: Tests are isolated and easy to run

## Building Projects

### Build Single Project

```bash
cd tests/real-world/<project>
mkdir build
cd build
cmake ..
make
```

### Build All Projects

```bash
#!/bin/bash
# build-all-projects.sh

PROJECTS="json-parser logger test-framework string-formatter resource-manager"

for project in $PROJECTS; do
    echo "Building $project..."
    cd $project
    mkdir -p build
    cd build
    cmake .. && make
    cd ../..
done
```

### Build Options

```bash
# Debug build
cmake -DCMAKE_BUILD_TYPE=Debug ..

# Release build
cmake -DCMAKE_BUILD_TYPE=Release ..

# With verbose output
cmake -DCMAKE_VERBOSE_MAKEFILE=ON ..

# With specific compiler
cmake -DCMAKE_CXX_COMPILER=clang++ ..
```

## Running Tests

### Run Single Project Tests

```bash
cd tests/real-world/<project>/build
ctest
# or
./test_<project>
```

### Run All Tests

```bash
#!/bin/bash
# test-all-projects.sh

for project in $PROJECTS; do
    echo "Testing $project..."
    cd $project/build
    if [ -f "test_$project" ]; then
        ./test_$project
    else
        ctest
    fi
    cd ../..
done
```

### Test Output Formats

#### Verbose Output

```bash
ctest -V
```

#### JSON Output

```bash
ctest --output-on-failure --output-junit results.xml
```

#### Summary Only

```bash
ctest --quiet
```

## Adding New Projects

### Step 1: Create Project Directory

```bash
cd tests/real-world
mkdir my-new-project
cd my-new-project
mkdir -p {include,src,tests,expected}
```

### Step 2: Create README.md

```markdown
# My New Project

## Overview
Brief description of the project

## C++ Features Tested
- Feature 1
- Feature 2
- ...

## Target Size
X,XXX lines of code
```

### Step 3: Create CMakeLists.txt

```cmake
cmake_minimum_required(VERSION 3.20)
project(my_new_project CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

include_directories(include)

# Library (if needed)
add_library(my_new_project
    src/MyClass.cpp
)

# Test executable
add_executable(test_my_new_project
    tests/test_my_new_project.cpp
)

target_link_libraries(test_my_new_project my_new_project)

enable_testing()
add_test(NAME MyNewProjectTest COMMAND test_my_new_project)
```

### Step 4: Implement Headers

```cpp
// include/MyClass.h
#ifndef MY_CLASS_H
#define MY_CLASS_H

class MyClass {
public:
    MyClass();
    ~MyClass();
    
    void doSomething();
};

#endif // MY_CLASS_H
```

### Step 5: Implement Source

```cpp
// src/MyClass.cpp
#include "MyClass.h"

MyClass::MyClass() {}
MyClass::~MyClass() {}

void MyClass::doSomething() {
    // Implementation
}
```

### Step 6: Write Tests

```cpp
// tests/test_my_new_project.cpp
#include "MyClass.h"
#include <cassert>

int main() {
    MyClass obj;
    obj.doSomething();
    
    // Add assertions
    assert(true);
    
    return 0;
}
```

### Step 7: Build and Test

```bash
mkdir build
cd build
cmake ..
make
ctest
```

### Step 8: Update Main README

Add your project to `tests/real-world/README.md`

## Transpilation Process

### Manual Transpilation

```bash
# Transpile single file
cpptoc include/MyClass.h --output output/MyClass.h -- -std=c++17

cpptoc src/MyClass.cpp --output output/MyClass.c -- -std=c++17 \
    -I include
```

### Automated Transpilation

```bash
#!/bin/bash
# transpile-project.sh <project>

PROJECT=$1
INPUT_DIR="tests/real-world/$PROJECT"
OUTPUT_DIR="tests/real-world/$PROJECT/transpiled"

mkdir -p $OUTPUT_DIR

# Transpile headers
for header in $INPUT_DIR/include/*.h; do
    basename=$(basename $header)
    cpptoc $header --output $OUTPUT_DIR/$basename -- -std=c++17
done

# Transpile sources
for source in $INPUT_DIR/src/*.cpp; do
    basename=$(basename $source .cpp)
    cpptoc $source --output $OUTPUT_DIR/$basename.c -- \
        -std=c++17 -I $INPUT_DIR/include
done
```

### Compile Transpiled Code

```bash
#!/bin/bash
# compile-transpiled.sh <project>

PROJECT=$1
TRANSPILED_DIR="tests/real-world/$PROJECT/transpiled"
BUILD_DIR="tests/real-world/$PROJECT/build-transpiled"

mkdir -p $BUILD_DIR

# Compile C sources
for source in $TRANSPILED_DIR/*.c; do
    basename=$(basename $source .c)
    gcc -c $source -o $BUILD_DIR/$basename.o \
        -I $TRANSPILED_DIR \
        -I runtime \
        -std=c99
done

# Link
gcc $BUILD_DIR/*.o -o $BUILD_DIR/test_$PROJECT
```

### Validation

```bash
#!/bin/bash
# validate-transpilation.sh <project>

PROJECT=$1

# Run native C++ version
cd tests/real-world/$PROJECT/build
./test_$PROJECT > native_output.txt

# Run transpiled C version
cd ../build-transpiled
./test_$PROJECT > transpiled_output.txt

# Compare outputs
diff native_output.txt transpiled_output.txt

if [ $? -eq 0 ]; then
    echo "✓ Outputs match!"
else
    echo "✗ Outputs differ!"
fi
```

## Troubleshooting

### Build Failures

#### Problem: CMake can't find compiler

```
CMake Error: Could not find CMAKE_CXX_COMPILER
```

**Solution:**
```bash
export CXX=g++
# or
cmake -DCMAKE_CXX_COMPILER=g++ ..
```

#### Problem: Missing headers

```
fatal error: MyClass.h: No such file or directory
```

**Solution:**
Check include paths:
```cmake
include_directories(include)
include_directories(${PROJECT_SOURCE_DIR}/include)
```

### Test Failures

#### Problem: Assertion failed

```
Assertion failed: (expected == actual)
```

**Solution:**
- Check test logic
- Verify expected values
- Add debug output
- Run with debugger: `gdb ./test_project`

#### Problem: Segmentation fault

```
Segmentation fault (core dumped)
```

**Solution:**
- Run with valgrind: `valgrind ./test_project`
- Check for null pointers
- Verify array bounds
- Enable AddressSanitizer: `cmake -DCMAKE_CXX_FLAGS="-fsanitize=address" ..`

### Transpilation Issues

#### Problem: Unsupported feature

```
Error: Unsupported C++ feature: X
```

**Solution:**
- Check transpiler documentation
- Simplify code if possible
- File issue with transpiler team
- Use workaround if available

#### Problem: Generated code doesn't compile

```
error: invalid use of incomplete type
```

**Solution:**
- Check header dependencies
- Ensure forward declarations
- Verify include order
- Add missing includes to runtime

## Best Practices

### Writing Transpiler-Friendly Code

1. **Use Standard C++**
   - Avoid compiler-specific extensions
   - Stick to C++17 standard
   - Use portable constructs

2. **Clear Type Declarations**
   ```cpp
   // Good
   std::vector<int> vec;
   
   // Avoid
   auto vec = std::vector<int>();
   ```

3. **Explicit Template Instantiations**
   ```cpp
   // Good - explicit
   template class MyTemplate<int>;
   
   // Automatic instantiation works but is less clear
   ```

4. **Avoid Macros When Possible**
   ```cpp
   // Prefer
   constexpr int MAX_SIZE = 100;
   
   // Over
   #define MAX_SIZE 100
   ```

### Testing Guidelines

1. **Comprehensive Coverage**
   - Test normal cases
   - Test edge cases
   - Test error cases
   - Test boundary conditions

2. **Clear Test Names**
   ```cpp
   // Good
   void testVectorPushBackIncreasesSize()
   
   // Bad
   void test1()
   ```

3. **Independent Tests**
   - Each test should be independent
   - No shared state between tests
   - Tests can run in any order

4. **Descriptive Assertions**
   ```cpp
   // Good
   ASSERT_EQ(vec.size(), 3, "Vector should have 3 elements");
   
   // Acceptable
   assert(vec.size() == 3);
   ```

### Performance Considerations

1. **Profile Before Optimizing**
   ```bash
   # Build with profiling
   cmake -DCMAKE_CXX_FLAGS="-pg" ..
   make
   ./test_project
   gprof test_project gmon.out > profile.txt
   ```

2. **Benchmark Critical Paths**
   ```cpp
   #include <chrono>
   
   auto start = std::chrono::high_resolution_clock::now();
   // Code to benchmark
   auto end = std::chrono::high_resolution_clock::now();
   auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end - start);
   std::cout << "Duration: " << duration.count() << "μs" << std::endl;
   ```

3. **Compare Native vs Transpiled**
   - Always benchmark both versions
   - Target < 20% overhead
   - Identify bottlenecks
   - Optimize hot paths

### Documentation Standards

1. **Code Comments**
   ```cpp
   /**
    * @brief Brief description
    * @param param Description of parameter
    * @return Description of return value
    */
   int myFunction(int param);
   ```

2. **README Updates**
   - Keep README.md current
   - Document new features
   - Update examples
   - Note known issues

3. **Test Documentation**
   ```cpp
   // Test that vector push_back increases size
   void testPushBack() {
       std::vector<int> vec;
       vec.push_back(1);
       assert(vec.size() == 1);
   }
   ```

## Continuous Integration

### GitHub Actions Example

```yaml
name: Real-World Tests

on: [push, pull_request]

jobs:
  test-real-world:
    runs-on: ubuntu-latest
    
    steps:
    - uses: actions/checkout@v2
    
    - name: Install Dependencies
      run: |
        sudo apt-get update
        sudo apt-get install -y cmake g++ clang
    
    - name: Build Transpiler
      run: |
        mkdir build
        cd build
        cmake ..
        make
    
    - name: Build Real-World Projects
      run: |
        cd tests/real-world
        ./build-all-projects.sh
    
    - name: Run Tests
      run: |
        cd tests/real-world
        ./test-all-projects.sh
    
    - name: Transpile Projects
      run: |
        ./scripts/test-real-world.sh
    
    - name: Upload Results
      uses: actions/upload-artifact@v2
      with:
        name: test-results
        path: test-results/
```

## Metrics and Reporting

### LOC Counter

```bash
#!/bin/bash
# count-loc.sh

find tests/real-world -name "*.cpp" -o -name "*.h" | \
    xargs wc -l | \
    tail -1
```

### Test Coverage

```bash
# Build with coverage
cmake -DCMAKE_CXX_FLAGS="--coverage" ..
make
ctest

# Generate report
lcov --capture --directory . --output-file coverage.info
genhtml coverage.info --output-directory coverage-report
```

### Performance Report

```bash
#!/bin/bash
# performance-report.sh

echo "Performance Benchmarks"
echo "====================="

for project in $PROJECTS; do
    echo ""
    echo "$project:"
    
    # Run native
    /usr/bin/time -f "Native: %E" \
        tests/real-world/$project/build/test_$project > /dev/null
    
    # Run transpiled
    /usr/bin/time -f "Transpiled: %E" \
        tests/real-world/$project/build-transpiled/test_$project > /dev/null
done
```

## Advanced Topics

### Custom Transpilation Rules

Create `.cpptoc.json` in project root:

```json
{
  "rules": {
    "inline_small_functions": true,
    "optimize_templates": true,
    "preserve_comments": true
  },
  "exclude": [
    "tests/*",
    "examples/*"
  ]
}
```

### Cross-Platform Testing

```yaml
# .github/workflows/cross-platform.yml

strategy:
  matrix:
    os: [ubuntu-latest, macos-latest, windows-latest]
    compiler: [gcc, clang, msvc]
    
runs-on: ${{ matrix.os }}
```

### Memory Leak Detection

```bash
# With valgrind
valgrind --leak-check=full --show-leak-kinds=all \
    ./test_project

# With AddressSanitizer
cmake -DCMAKE_CXX_FLAGS="-fsanitize=address" ..
make
./test_project
```

## Conclusion

This guide provides everything needed to:
- ✓ Build real-world test projects
- ✓ Run comprehensive tests
- ✓ Transpile C++ to C
- ✓ Validate transpilation
- ✓ Add new projects
- ✓ Troubleshoot issues
- ✓ Follow best practices

For questions or issues, please consult:
- Main project README
- Architecture documentation
- Transpiler documentation
- GitHub issues

---

**Last Updated**: 2025-12-18
**Version**: 1.0
**Status**: Complete
