#!/bin/bash
# Test: CMake Build System Integration
# This test verifies that the build system is properly configured

set -e

PROJECT_ROOT="/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c"
BUILD_DIR="$PROJECT_ROOT/build"

echo "=== Build System Integration Test ==="
echo

# Test 1: CMakeLists.txt exists
echo "Test 1: Checking if CMakeLists.txt exists..."
if [ ! -f "$PROJECT_ROOT/CMakeLists.txt" ]; then
    echo "FAIL: CMakeLists.txt not found"
    exit 1
fi
echo "PASS: CMakeLists.txt exists"
echo

# Test 2: CMake can configure the project
echo "Test 2: Configuring with CMake..."
rm -rf "$BUILD_DIR"
if ! cmake -B "$BUILD_DIR" -DCMAKE_BUILD_TYPE=Debug 2>&1; then
    echo "FAIL: CMake configuration failed"
    exit 1
fi
echo "PASS: CMake configuration succeeded"
echo

# Test 3: CMake can build the project
echo "Test 3: Building with CMake..."
if ! cmake --build "$BUILD_DIR" 2>&1; then
    echo "FAIL: CMake build failed"
    exit 1
fi
echo "PASS: CMake build succeeded"
echo

# Test 4: Executable exists
echo "Test 4: Checking if executable exists..."
if [ ! -f "$BUILD_DIR/cpptoc" ]; then
    echo "FAIL: Executable 'cpptoc' not found in build directory"
    exit 1
fi
echo "PASS: Executable 'cpptoc' exists"
echo

echo "=== All Build System Tests Passed ==="
exit 0
