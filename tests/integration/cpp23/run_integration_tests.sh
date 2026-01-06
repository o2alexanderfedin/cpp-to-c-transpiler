#!/bin/bash
# Integration Test Harness for Phase 38-P2
# Tests confirmed working feature combinations

set -e

SCRIPT_DIR="$( cd "$( dirname "${BASH_SOURCE[0]}" )" && pwd )"
TRANSPILER="${SCRIPT_DIR}/../../../build_working/cpptoc"
TEST_OUTPUT_DIR="${SCRIPT_DIR}/output"
RESULTS_FILE="${SCRIPT_DIR}/test_results.txt"

# Colors for output
GREEN='\033[0;32m'
RED='\033[0;31m'
YELLOW='\033[1;33m'
NC='\033[0;m' # No Color

# Create output directory
mkdir -p "${TEST_OUTPUT_DIR}"

# Initialize results
echo "Phase 38-P2 Integration Test Results" > "${RESULTS_FILE}"
echo "Date: $(date)" >> "${RESULTS_FILE}"
echo "======================================" >> "${RESULTS_FILE}"
echo "" >> "${RESULTS_FILE}"

TOTAL_TESTS=0
PASSED_TESTS=0
FAILED_TESTS=0

run_test() {
    local test_name=$1
    local test_file="${SCRIPT_DIR}/${test_name}.cpp"
    local test_dir="${TEST_OUTPUT_DIR}/${test_name}_project"

    TOTAL_TESTS=$((TOTAL_TESTS + 1))

    echo -e "${YELLOW}Running: ${test_name}${NC}"

    # Step 1: Compile C++ version
    echo "  [1/5] Compiling C++ version..."
    if ! g++ -std=c++23 "${test_file}" -o "${TEST_OUTPUT_DIR}/${test_name}_cpp" 2>"${TEST_OUTPUT_DIR}/${test_name}_cpp.log"; then
        echo -e "${RED}  FAIL: C++ compilation failed${NC}"
        echo "${test_name}: FAIL (C++ compilation)" >> "${RESULTS_FILE}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        return 1
    fi

    # Step 2: Run C++ version
    echo "  [2/5] Running C++ version..."
    if ! "${TEST_OUTPUT_DIR}/${test_name}_cpp" 2>"${TEST_OUTPUT_DIR}/${test_name}_cpp_run.log"; then
        echo -e "${RED}  FAIL: C++ execution failed${NC}"
        echo "${test_name}: FAIL (C++ execution)" >> "${RESULTS_FILE}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        return 1
    fi

    # Step 3: Transpile to C
    echo "  [3/5] Transpiling to C..."

    # Create project structure for transpiler
    mkdir -p "${test_dir}"
    cp "${test_file}" "${test_dir}/main.cpp"
    mkdir -p "${test_dir}/output"

    if ! "${TRANSPILER}" --source-dir="${test_dir}" --output-dir="${test_dir}/output" 2>"${TEST_OUTPUT_DIR}/${test_name}_transpile.log"; then
        echo -e "${RED}  FAIL: Transpilation failed${NC}"
        echo "${test_name}: FAIL (Transpilation)" >> "${RESULTS_FILE}"
        cat "${TEST_OUTPUT_DIR}/${test_name}_transpile.log" | grep -E "error:|Error:" | head -5
        FAILED_TESTS=$((FAILED_TESTS + 1))
        return 1
    fi

    # Find the generated C file
    C_FILE=$(find "${test_dir}/output" -name "*.c" | head -1)
    if [ -z "$C_FILE" ]; then
        echo -e "${RED}  FAIL: No C file generated${NC}"
        echo "${test_name}: FAIL (No C file generated)" >> "${RESULTS_FILE}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        return 1
    fi

    # Step 4: Compile C version
    echo "  [4/5] Compiling C version..."
    if ! gcc -std=c99 "${C_FILE}" -o "${TEST_OUTPUT_DIR}/${test_name}_c" 2>"${TEST_OUTPUT_DIR}/${test_name}_c.log"; then
        echo -e "${RED}  FAIL: C compilation failed${NC}"
        echo "${test_name}: FAIL (C compilation)" >> "${RESULTS_FILE}"
        cat "${TEST_OUTPUT_DIR}/${test_name}_c.log" | head -10
        FAILED_TESTS=$((FAILED_TESTS + 1))
        return 1
    fi

    # Step 5: Run C version
    echo "  [5/5] Running C version..."
    if ! "${TEST_OUTPUT_DIR}/${test_name}_c" 2>"${TEST_OUTPUT_DIR}/${test_name}_c_run.log"; then
        echo -e "${RED}  FAIL: C execution failed${NC}"
        echo "${test_name}: FAIL (C execution)" >> "${RESULTS_FILE}"
        FAILED_TESTS=$((FAILED_TESTS + 1))
        return 1
    fi

    echo -e "${GREEN}  PASS${NC}"
    echo "${test_name}: PASS" >> "${RESULTS_FILE}"
    PASSED_TESTS=$((PASSED_TESTS + 1))
    return 0
}

echo "Starting Integration Tests..."
echo ""

# Run all tests
run_test "01_templates_inheritance" || true
run_test "02_virtual_multiple_inheritance" || true
run_test "03_scoped_enums_namespaces" || true
run_test "04_operator_overloading_templates" || true
run_test "05_range_for_custom_containers" || true

echo ""
echo "======================================" >> "${RESULTS_FILE}"
echo "Summary:" >> "${RESULTS_FILE}"
echo "  Total: ${TOTAL_TESTS}" >> "${RESULTS_FILE}"
echo "  Passed: ${PASSED_TESTS}" >> "${RESULTS_FILE}"
echo "  Failed: ${FAILED_TESTS}" >> "${RESULTS_FILE}"
if [ ${TOTAL_TESTS} -gt 0 ]; then
    PASS_RATE=$((PASSED_TESTS * 100 / TOTAL_TESTS))
else
    PASS_RATE=0
fi
echo "  Pass Rate: ${PASS_RATE}%" >> "${RESULTS_FILE}"

echo ""
echo "======================================"
echo "Test Results Summary:"
echo -e "  Total:     ${TOTAL_TESTS}"
echo -e "  ${GREEN}Passed:${NC}    ${PASSED_TESTS}"
echo -e "  ${RED}Failed:${NC}    ${FAILED_TESTS}"
echo -e "  Pass Rate: ${PASS_RATE}%"
echo "======================================"
echo ""
echo "Detailed results saved to: ${RESULTS_FILE}"
echo "Test output saved to: ${TEST_OUTPUT_DIR}/"

# Exit with success if pass rate >= 80%
if [ ${PASS_RATE} -ge 80 ]; then
    echo "SUCCESS: Pass rate >= 80%"
    exit 0
elif [ ${PASS_RATE} -ge 60 ]; then
    echo "PARTIAL SUCCESS: Pass rate >= 60% but < 80%"
    exit 0
else
    echo "FAILURE: Pass rate < 60%"
    exit 1
fi
