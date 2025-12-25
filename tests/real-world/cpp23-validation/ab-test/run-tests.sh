#!/bin/bash

################################################################################
# A/B Testing Framework for C++23 to C99 Transpilation Validation
# Phase 33.3: Comprehensive test execution and comparison
#
# This script:
# 1. Iterates through all gcc-adapted test categories
# 2. Builds C++23 versions of each test
# 3. Executes C++23 tests and captures output
# 4. Transpiles C++23 code to C using cpptoc
# 5. Builds C versions (if transpilation successful)
# 6. Compares C and C++ outputs
# 7. Generates comprehensive summary report
#
# Usage: ./run-tests.sh [--clean] [--categories <cat1,cat2>] [--verbose]
################################################################################

set -o pipefail

# Configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/../../../.." && pwd)"
REPO_ROOT="${PROJECT_ROOT}"
BUILD_DIR="${REPO_ROOT}/build_working"
CPPTOC_BIN="${BUILD_DIR}/cpptoc"
GCC_ADAPTED_DIR="${SCRIPT_DIR}/../gcc-adapted"
AB_TEST_DIR="${SCRIPT_DIR}"
RESULTS_DIR="${AB_TEST_DIR}/results"
TRANSPILED_DIR="${SCRIPT_DIR}/../transpiled"
LOGS_DIR="${AB_TEST_DIR}/logs"

# Ensure directories exist
mkdir -p "${RESULTS_DIR}" "${LOGS_DIR}"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Global counters
TOTAL_CATEGORIES=0
CATEGORIES_PROCESSED=0
BUILD_SUCCESS_CPP=0
BUILD_FAILED_CPP=0
TRANSPILE_SUCCESS=0
TRANSPILE_FAILED=0
BUILD_SUCCESS_C=0
BUILD_FAILED_C=0
OUTPUT_MATCH=0
OUTPUT_MISMATCH=0
EXECUTION_ERRORS=0

# Flags
CLEAN_BUILD=false
VERBOSE=false
SPECIFIC_CATEGORIES=""

################################################################################
# Helper Functions
################################################################################

log() {
    local level=$1
    shift
    local msg="$@"
    echo "[$(date '+%H:%M:%S')] [$level] $msg"
}

info() {
    echo -e "${BLUE}[INFO]${NC} $@"
}

success() {
    echo -e "${GREEN}[SUCCESS]${NC} $@"
}

warning() {
    echo -e "${YELLOW}[WARN]${NC} $@"
}

error() {
    echo -e "${RED}[ERROR]${NC} $@"
}

verbose() {
    if [ "$VERBOSE" = true ]; then
        echo -e "${BLUE}[VERBOSE]${NC} $@"
    fi
}

################################################################################
# Validation Functions
################################################################################

validate_prerequisites() {
    info "Validating prerequisites..."

    if [ ! -f "$CPPTOC_BIN" ]; then
        error "cpptoc binary not found at $CPPTOC_BIN"
        error "Please build the transpiler first: cd $BUILD_DIR && cmake --build ."
        return 1
    fi

    if [ ! -d "$GCC_ADAPTED_DIR" ]; then
        error "gcc-adapted directory not found at $GCC_ADAPTED_DIR"
        return 1
    fi

    # Check for C/C++ compiler
    if ! command -v cmake &> /dev/null; then
        error "cmake not found. Please install cmake."
        return 1
    fi

    if ! command -v make &> /dev/null; then
        error "make not found. Please install make."
        return 1
    fi

    if ! command -v clang++ &> /dev/null && ! command -v g++ &> /dev/null; then
        error "Neither clang++ nor g++ found. Please install a C++ compiler."
        return 1
    fi

    if ! command -v clang &> /dev/null && ! command -v gcc &> /dev/null; then
        error "Neither clang nor gcc found. Please install a C compiler."
        return 1
    fi

    success "All prerequisites validated."
    return 0
}

################################################################################
# Category Processing Functions
################################################################################

get_test_categories() {
    if [ -n "$SPECIFIC_CATEGORIES" ]; then
        echo "$SPECIFIC_CATEGORIES" | tr ',' '\n'
    else
        find "$GCC_ADAPTED_DIR" -maxdepth 1 -type d ! -name "gcc-adapted" | xargs -n1 basename | sort
    fi
}

build_cpp_version() {
    local category=$1
    local category_path="${GCC_ADAPTED_DIR}/${category}"
    local build_dir="${category_path}/build"

    info "Building C++23 version for: $category"

    # Clean previous build if requested
    if [ "$CLEAN_BUILD" = true ] && [ -d "$build_dir" ]; then
        verbose "Cleaning previous build directory..."
        rm -rf "$build_dir"
    fi

    # Create build directory
    mkdir -p "$build_dir"
    cd "$build_dir" || return 1

    # Configure
    if ! cmake -B . -DCMAKE_CXX_STANDARD=23 -DCMAKE_CXX_STANDARD_REQUIRED=ON .. >> "${LOGS_DIR}/${category}.cpp.build.log" 2>&1; then
        error "CMake configuration failed for $category"
        cat "${LOGS_DIR}/${category}.cpp.build.log" >&2
        return 1
    fi

    # Build
    if ! cmake --build . >> "${LOGS_DIR}/${category}.cpp.build.log" 2>&1; then
        error "CMake build failed for $category"
        tail -20 "${LOGS_DIR}/${category}.cpp.build.log" >&2
        return 1
    fi

    success "C++23 build successful: $category"
    return 0
}

run_cpp_tests() {
    local category=$1
    local category_path="${GCC_ADAPTED_DIR}/${category}"
    local build_dir="${category_path}/build"

    info "Running C++23 tests for: $category"

    cd "$build_dir" || return 1

    # Run ctest and capture output
    if ctest --output-on-failure > "${RESULTS_DIR}/${category}.cpp.out" 2>&1; then
        success "C++23 tests passed: $category"
        return 0
    else
        local exit_code=$?
        warning "C++23 tests failed with exit code $exit_code: $category"
        # Still continue - we want to compare outputs even if tests fail
        return 0
    fi
}

transpile_category() {
    local category=$1
    local category_path="${GCC_ADAPTED_DIR}/${category}"
    local transpiled_category_dir="${TRANSPILED_DIR}/${category}"

    info "Transpiling C++23 to C for: $category"

    # Create transpiled directory
    mkdir -p "$transpiled_category_dir"

    local total_tests=0
    local successful_transpiles=0

    # Find and transpile all test files
    for test_file in "${category_path}"/test*.cpp; do
        if [ ! -f "$test_file" ]; then
            continue
        fi

        ((total_tests++))
        local test_name=$(basename "$test_file" .cpp)
        local output_file="${transpiled_category_dir}/${test_name}.c"

        verbose "Transpiling: $test_file -> $output_file"

        if "$CPPTOC_BIN" "$test_file" -o "$output_file" >> "${LOGS_DIR}/${category}.transpile.log" 2>&1; then
            verbose "Transpiled successfully: $test_name"
            ((successful_transpiles++))
        else
            warning "Transpilation failed: $test_name"
            echo "--- Transpilation Error for $test_name ---" >> "${LOGS_DIR}/${category}.transpile.log"
        fi
    done

    if [ $total_tests -eq 0 ]; then
        warning "No test files found for category: $category"
        return 1
    fi

    local success_rate=$((successful_transpiles * 100 / total_tests))
    info "Transpilation complete: $category ($successful_transpiles/$total_tests = ${success_rate}%)"

    if [ $successful_transpiles -eq 0 ]; then
        return 1
    fi

    return 0
}

build_c_version() {
    local category=$1
    local transpiled_category_dir="${TRANSPILED_DIR}/${category}"

    info "Building C version for: $category"

    # Check if transpiled files exist
    local c_files=("${transpiled_category_dir}"/test*.c)
    if [ ${#c_files[@]} -eq 0 ] || [ ! -e "${c_files[0]}" ]; then
        warning "No transpiled C files found for: $category"
        return 1
    fi

    local build_dir="${transpiled_category_dir}/build"
    mkdir -p "$build_dir"
    cd "$build_dir" || return 1

    # Create a CMakeLists.txt for building C tests
    create_c_cmake_file "$category" "$transpiled_category_dir" "${LOGS_DIR}/${category}.c.cmake.log"

    # Configure
    if ! cmake -B . -DCMAKE_C_STANDARD=99 .. >> "${LOGS_DIR}/${category}.c.build.log" 2>&1; then
        warning "CMake configuration failed for C version: $category"
        verbose "CMake log:"
        cat "${LOGS_DIR}/${category}.c.build.log" >&2
        return 1
    fi

    # Build
    if ! cmake --build . >> "${LOGS_DIR}/${category}.c.build.log" 2>&1; then
        warning "C build failed for: $category"
        tail -20 "${LOGS_DIR}/${category}.c.build.log" >&2
        return 1
    fi

    success "C version build successful: $category"
    return 0
}

create_c_cmake_file() {
    local category=$1
    local transpiled_dir=$2
    local log_file=$3

    local cmake_file="${transpiled_dir}/build/CMakeLists.txt"

    cat > "$cmake_file" << 'CMAKEFILE'
cmake_minimum_required(VERSION 3.12)
project(c99_tests)

set(CMAKE_C_STANDARD 99)
set(CMAKE_C_STANDARD_REQUIRED ON)

# Get all .c files in parent directory
file(GLOB TEST_SOURCES ../*.c)

foreach(test_file ${TEST_SOURCES})
    get_filename_component(test_name ${test_file} NAME_WE)
    add_executable(${test_name} ${test_file})
    set_target_properties(${test_name} PROPERTIES C_STANDARD 99 C_STANDARD_REQUIRED ON)
    add_test(NAME ${test_name} COMMAND ${test_name})
endforeach()

enable_testing()
CMAKEFILE

    verbose "Created CMakeLists.txt for C build: $category"
}

run_c_tests() {
    local category=$1
    local transpiled_category_dir="${TRANSPILED_DIR}/${category}"
    local build_dir="${transpiled_category_dir}/build"

    if [ ! -d "$build_dir" ]; then
        warning "C build directory does not exist: $category"
        return 1
    fi

    info "Running C tests for: $category"

    cd "$build_dir" || return 1

    # Run ctest and capture output
    if ctest --output-on-failure > "${RESULTS_DIR}/${category}.c.out" 2>&1; then
        success "C tests passed: $category"
        return 0
    else
        local exit_code=$?
        warning "C tests failed with exit code $exit_code: $category"
        # Continue to comparison
        return 0
    fi
}

compare_outputs() {
    local category=$1

    info "Comparing outputs for: $category"

    local cpp_out="${RESULTS_DIR}/${category}.cpp.out"
    local c_out="${RESULTS_DIR}/${category}.c.out"
    local comparison_file="${RESULTS_DIR}/${category}.comparison.txt"

    # Check if both output files exist
    if [ ! -f "$cpp_out" ]; then
        warning "C++ output file not found: $cpp_out"
        return 2
    fi

    if [ ! -f "$c_out" ]; then
        warning "C output file not found: $c_out"
        return 2
    fi

    # Compare outputs
    if diff -u "$cpp_out" "$c_out" > "$comparison_file" 2>&1; then
        success "Outputs match: $category"
        return 0
    else
        warning "Outputs differ: $category"
        echo "See detailed comparison in: $comparison_file"
        return 1
    fi
}

################################################################################
# Category Processing Function
################################################################################

process_category() {
    local category=$1
    local category_path="${GCC_ADAPTED_DIR}/${category}"

    echo ""
    echo "=============================================================================="
    info "Processing category: $category"
    echo "=============================================================================="

    # Verify category exists
    if [ ! -d "$category_path" ]; then
        error "Category directory not found: $category_path"
        ((EXECUTION_ERRORS++))
        return 1
    fi

    # Verify CMakeLists.txt exists
    if [ ! -f "${category_path}/CMakeLists.txt" ]; then
        error "CMakeLists.txt not found in: $category_path"
        ((EXECUTION_ERRORS++))
        return 1
    fi

    # Step 1: Build C++23 version
    if build_cpp_version "$category"; then
        ((BUILD_SUCCESS_CPP++))
    else
        ((BUILD_FAILED_CPP++))
        error "Skipping remaining steps for $category due to C++23 build failure"
        return 1
    fi

    # Step 2: Run C++23 tests
    if run_cpp_tests "$category"; then
        verbose "C++23 tests executed successfully"
    else
        verbose "C++23 tests had failures (continuing with comparison)"
    fi

    # Step 3: Transpile to C
    if transpile_category "$category"; then
        ((TRANSPILE_SUCCESS++))
    else
        ((TRANSPILE_FAILED++))
        warning "Transpilation failed for $category - skipping C build and comparison"
        return 1
    fi

    # Step 4: Build C version
    if build_c_version "$category"; then
        ((BUILD_SUCCESS_C++))
    else
        ((BUILD_FAILED_C++))
        warning "C build failed for $category - skipping C test execution"
        return 1
    fi

    # Step 5: Run C tests
    if run_c_tests "$category"; then
        verbose "C tests executed successfully"
    else
        verbose "C tests had failures (continuing with comparison)"
    fi

    # Step 6: Compare outputs
    case $(compare_outputs "$category") in
        0)
            ((OUTPUT_MATCH++))
            ;;
        1)
            ((OUTPUT_MISMATCH++))
            ;;
        2)
            ((EXECUTION_ERRORS++))
            ;;
    esac

    success "Category processing complete: $category"
    return 0
}

################################################################################
# Summary and Reporting
################################################################################

generate_summary() {
    local summary_file="${RESULTS_DIR}/SUMMARY.txt"

    echo ""
    echo "=============================================================================="
    echo "A/B TESTING SUMMARY REPORT"
    echo "=============================================================================="
    echo ""

    {
        echo "A/B Testing Summary Report"
        echo "Generated: $(date)"
        echo ""
        echo "Project Root: $REPO_ROOT"
        echo "Transpiler: $CPPTOC_BIN"
        echo ""
        echo "==============================================================================="
        echo "EXECUTION STATISTICS"
        echo "==============================================================================="
        echo ""
        echo "Total Categories:                 $TOTAL_CATEGORIES"
        echo "Categories Processed:             $CATEGORIES_PROCESSED"
        echo ""
        echo "==============================================================================="
        echo "C++23 BUILD RESULTS"
        echo "==============================================================================="
        echo ""
        echo "Successful Builds:                $BUILD_SUCCESS_CPP"
        echo "Failed Builds:                    $BUILD_FAILED_CPP"

        if [ $BUILD_SUCCESS_CPP -gt 0 ]; then
            local cpp_success_rate=$((BUILD_SUCCESS_CPP * 100 / (BUILD_SUCCESS_CPP + BUILD_FAILED_CPP)))
            echo "Success Rate:                     ${cpp_success_rate}%"
        fi

        echo ""
        echo "==============================================================================="
        echo "TRANSPILATION RESULTS"
        echo "==============================================================================="
        echo ""
        echo "Successful Transpilations:        $TRANSPILE_SUCCESS"
        echo "Failed Transpilations:            $TRANSPILE_FAILED"

        if [ $TRANSPILE_SUCCESS -gt 0 ]; then
            local transpile_success_rate=$((TRANSPILE_SUCCESS * 100 / (TRANSPILE_SUCCESS + TRANSPILE_FAILED)))
            echo "Success Rate:                     ${transpile_success_rate}%"
        fi

        echo ""
        echo "==============================================================================="
        echo "C BUILD RESULTS"
        echo "==============================================================================="
        echo ""
        echo "Successful Builds:                $BUILD_SUCCESS_C"
        echo "Failed Builds:                    $BUILD_FAILED_C"

        if [ $BUILD_SUCCESS_C -gt 0 ]; then
            local c_success_rate=$((BUILD_SUCCESS_C * 100 / (BUILD_SUCCESS_C + BUILD_FAILED_C)))
            echo "Success Rate:                     ${c_success_rate}%"
        fi

        echo ""
        echo "==============================================================================="
        echo "OUTPUT COMPARISON RESULTS"
        echo "==============================================================================="
        echo ""
        echo "Outputs Matching:                 $OUTPUT_MATCH"
        echo "Outputs Differing:                $OUTPUT_MISMATCH"
        echo "Execution Errors:                 $EXECUTION_ERRORS"

        if [ $((OUTPUT_MATCH + OUTPUT_MISMATCH)) -gt 0 ]; then
            local match_rate=$((OUTPUT_MATCH * 100 / (OUTPUT_MATCH + OUTPUT_MISMATCH)))
            echo "Match Rate:                       ${match_rate}%"
        fi

        echo ""
        echo "==============================================================================="
        echo "RESULT ARTIFACTS"
        echo "==============================================================================="
        echo ""
        echo "Results Directory:                $RESULTS_DIR"
        echo "Logs Directory:                   $LOGS_DIR"
        echo "Transpiled Code:                  $TRANSPILED_DIR"
        echo ""
        echo "Key Files:"
        echo "  - *.cpp.out:       C++23 test output"
        echo "  - *.c.out:         C test output"
        echo "  - *.comparison.txt:Diff between outputs"
        echo "  - *.build.log:     Build logs"
        echo "  - *.transpile.log: Transpilation logs"

        echo ""
        echo "==============================================================================="
        echo "END OF REPORT"
        echo "==============================================================================="
    } | tee "$summary_file"

    # Print to console as well
    cat "$summary_file"
}

################################################################################
# Main Execution
################################################################################

print_header() {
    echo ""
    echo "================================================================================"
    echo "A/B Testing Framework for C++23 to C99 Transpilation Validation"
    echo "Phase 33.3: Comprehensive Test Execution and Comparison"
    echo "================================================================================"
    echo ""
}

parse_arguments() {
    while [[ $# -gt 0 ]]; do
        case $1 in
            --clean)
                CLEAN_BUILD=true
                shift
                ;;
            --verbose)
                VERBOSE=true
                shift
                ;;
            --categories)
                SPECIFIC_CATEGORIES="$2"
                shift 2
                ;;
            *)
                error "Unknown option: $1"
                print_usage
                exit 1
                ;;
        esac
    done
}

print_usage() {
    cat << EOF
Usage: $0 [OPTIONS]

Options:
    --clean               Clean previous build artifacts before rebuilding
    --verbose             Enable verbose output for debugging
    --categories CAT1,CAT2  Process only specific categories (comma-separated)
                          Example: --categories if-consteval-P1938,multidim-subscript-P2128

Examples:
    # Run all categories with clean builds
    ./run-tests.sh --clean

    # Run specific categories with verbose output
    ./run-tests.sh --verbose --categories if-consteval-P1938,multidim-subscript-P2128

    # Standard run (incremental builds)
    ./run-tests.sh
EOF
}

main() {
    print_header
    parse_arguments "$@"

    # Step 1: Validate prerequisites
    if ! validate_prerequisites; then
        exit 1
    fi

    echo ""

    # Step 2: Get categories to process
    local categories=$(get_test_categories)
    TOTAL_CATEGORIES=$(echo "$categories" | wc -l)

    info "Found $TOTAL_CATEGORIES test categories"
    if [ -n "$SPECIFIC_CATEGORIES" ]; then
        info "Processing specific categories: $SPECIFIC_CATEGORIES"
    fi

    # Step 3: Process each category
    for category in $categories; do
        ((CATEGORIES_PROCESSED++))

        if process_category "$category"; then
            verbose "Category processing completed: $category"
        else
            verbose "Category processing had issues: $category"
        fi
    done

    # Step 4: Generate comprehensive summary
    echo ""
    generate_summary

    # Step 5: Exit with appropriate code
    if [ $EXECUTION_ERRORS -gt 0 ] || [ $BUILD_FAILED_CPP -gt 0 ] || [ $TRANSPILE_FAILED -gt 0 ] || [ $BUILD_FAILED_C -gt 0 ]; then
        warning "A/B testing completed with errors"
        exit 1
    else
        success "A/B testing completed successfully"
        exit 0
    fi
}

# Run main function
main "$@"
