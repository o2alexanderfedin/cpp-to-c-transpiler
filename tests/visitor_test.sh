#!/bin/bash
# Test: RecursiveASTVisitor Integration
# This test verifies that the visitor can traverse and identify AST nodes

set -e

PROJECT_ROOT="/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c"
CPPTOC="$PROJECT_ROOT/build/cpptoc"
TEST_FILE="$PROJECT_ROOT/tests/fixtures/visitor_test.cpp"

echo "=== RecursiveASTVisitor Integration Test ==="
echo

# Run tool and capture output
OUTPUT=$("$CPPTOC" "$TEST_FILE" -- 2>&1)

# Test 1: Visitor finds the class
echo "Test 1: Checking visitor found class 'Point'..."
if ! echo "$OUTPUT" | grep -q "Found class: Point"; then
    echo "FAIL: Visitor did not find class 'Point'"
    echo "Output: $OUTPUT"
    exit 1
fi
echo "PASS: Visitor found class 'Point'"
echo

# Test 2: Visitor finds methods
echo "Test 2: Checking visitor found methods..."
if ! echo "$OUTPUT" | grep -q "Found method:.*Point"; then
    echo "FAIL: Visitor did not find any methods"
    echo "Output: $OUTPUT"
    exit 1
fi
echo "PASS: Visitor found methods"
echo

# Test 3: Visitor finds variables
echo "Test 3: Checking visitor found member variables..."
if ! echo "$OUTPUT" | grep -q "Found variable:"; then
    echo "FAIL: Visitor did not find any variables"
    echo "Output: $OUTPUT"
    exit 1
fi
echo "PASS: Visitor found variables"
echo

echo "=== All RecursiveASTVisitor Tests Passed ==="
exit 0
