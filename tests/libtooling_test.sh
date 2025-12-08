#!/bin/bash
# Test: Clang LibTooling Integration
# This test verifies that the tool can parse C++ files using LibTooling

set -e

PROJECT_ROOT="/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c"
CPPTOC="$PROJECT_ROOT/build/cpptoc"
TEST_FILE="$PROJECT_ROOT/tests/fixtures/simple.cpp"

echo "=== Clang LibTooling Integration Test ==="
echo

# Test 1: Tool accepts command line arguments
echo "Test 1: Running tool with test file..."
if ! OUTPUT=$("$CPPTOC" "$TEST_FILE" -- 2>&1); then
    echo "FAIL: Tool failed to run"
    echo "Output: $OUTPUT"
    exit 1
fi
echo "PASS: Tool ran successfully"
echo

# Test 2: Tool outputs parse confirmation
echo "Test 2: Checking tool output for parse confirmation..."
if ! echo "$OUTPUT" | grep -q "Parsed file"; then
    echo "FAIL: Tool did not output 'Parsed file' message"
    echo "Output: $OUTPUT"
    exit 1
fi
echo "PASS: Tool confirmed file parsing"
echo

# Test 3: Tool reports declaration count
echo "Test 3: Checking tool output for declaration count..."
if ! echo "$OUTPUT" | grep -q "declarations"; then
    echo "FAIL: Tool did not report declaration count"
    echo "Output: $OUTPUT"
    exit 1
fi
echo "PASS: Tool reported declaration count"
echo

echo "=== All LibTooling Integration Tests Passed ==="
exit 0
