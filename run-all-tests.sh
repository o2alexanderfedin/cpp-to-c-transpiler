#!/bin/bash

# Script to run all test executables and capture output
# Usage: ./run-all-tests.sh

BUILD_DIR="/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build"
LOG_DIR="/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/test-logs"
SUMMARY_FILE="${LOG_DIR}/test-summary.txt"

# Initialize summary
echo "Test Execution Summary - $(date)" > "$SUMMARY_FILE"
echo "=====================================" >> "$SUMMARY_FILE"
echo "" >> "$SUMMARY_FILE"

# Counter variables
total_tests=0
passed_tests=0
failed_tests=0

# Get all test executables
cd "$BUILD_DIR"
test_executables=$(ls -1 *Test 2>/dev/null | sort)

echo "Found test executables:"
echo "$test_executables"
echo ""

# Run each test
for test in $test_executables; do
    echo "Running $test..."
    total_tests=$((total_tests + 1))

    log_file="${LOG_DIR}/${test}.log"

    # Run test and capture output
    if ./"$test" > "$log_file" 2>&1; then
        echo "  ✓ PASSED"
        passed_tests=$((passed_tests + 1))
        echo "PASSED: $test" >> "$SUMMARY_FILE"
    else
        exit_code=$?
        echo "  ✗ FAILED (exit code: $exit_code)"
        failed_tests=$((failed_tests + 1))
        echo "FAILED: $test (exit code: $exit_code)" >> "$SUMMARY_FILE"
    fi

    echo ""
done

# Write summary
echo "" >> "$SUMMARY_FILE"
echo "=====================================" >> "$SUMMARY_FILE"
echo "Total tests: $total_tests" >> "$SUMMARY_FILE"
echo "Passed: $passed_tests" >> "$SUMMARY_FILE"
echo "Failed: $failed_tests" >> "$SUMMARY_FILE"
echo "Pass rate: $(awk "BEGIN {printf \"%.2f\", ($passed_tests/$total_tests)*100}")%" >> "$SUMMARY_FILE"

# Display summary
echo "======================================"
echo "Test Execution Complete"
echo "======================================"
cat "$SUMMARY_FILE"

exit $failed_tests
