#!/bin/bash
#
# Code Coverage Report Generation Script
#
# This script builds the project with coverage instrumentation, runs all tests,
# and generates comprehensive coverage reports in HTML and text formats.
#
# Usage:
#   ./scripts/generate_coverage.sh [options]
#
# Options:
#   --clean          Clean build directory before building
#   --build-dir DIR  Specify build directory (default: build-coverage)
#   --output-dir DIR Specify output directory (default: coverage)
#   --verbose        Enable verbose output
#   --help           Show this help message
#
# Requirements:
#   - lcov (install with: brew install lcov on macOS)
#   - CMake 3.20+
#   - C++17 compiler with gcov support
#

set -e  # Exit on error

# Default configuration
BUILD_DIR="build-coverage"
OUTPUT_DIR="coverage"
CLEAN_BUILD=0
VERBOSE=0
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Color output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --clean)
            CLEAN_BUILD=1
            shift
            ;;
        --build-dir)
            BUILD_DIR="$2"
            shift 2
            ;;
        --output-dir)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --verbose)
            VERBOSE=1
            shift
            ;;
        --help)
            grep '^#' "$0" | grep -v '#!/bin/bash' | sed 's/^# //' | sed 's/^#//'
            exit 0
            ;;
        *)
            echo -e "${RED}Error: Unknown option: $1${NC}"
            echo "Use --help for usage information"
            exit 1
            ;;
    esac
done

# Helper functions
log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[SUCCESS]${NC} $1"
}

log_warning() {
    echo -e "${YELLOW}[WARNING]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Check for required tools
check_dependencies() {
    log_info "Checking dependencies..."

    local missing_deps=0

    if ! command -v lcov &> /dev/null; then
        log_error "lcov not found. Install with: brew install lcov"
        missing_deps=1
    fi

    if ! command -v genhtml &> /dev/null; then
        log_error "genhtml not found (usually comes with lcov)"
        missing_deps=1
    fi

    if ! command -v cmake &> /dev/null; then
        log_error "cmake not found"
        missing_deps=1
    fi

    if ! command -v gcov &> /dev/null; then
        log_warning "gcov not found in PATH, trying system default"
    fi

    if [ $missing_deps -eq 1 ]; then
        log_error "Missing required dependencies. Please install them and try again."
        exit 1
    fi

    log_success "All dependencies found"
}

# Clean build directory
clean_build_dir() {
    if [ $CLEAN_BUILD -eq 1 ] && [ -d "$PROJECT_ROOT/$BUILD_DIR" ]; then
        log_info "Cleaning build directory: $BUILD_DIR"
        rm -rf "$PROJECT_ROOT/$BUILD_DIR"
    fi
}

# Configure CMake with coverage enabled
configure_cmake() {
    log_info "Configuring CMake with coverage enabled..."

    mkdir -p "$PROJECT_ROOT/$BUILD_DIR"
    cd "$PROJECT_ROOT/$BUILD_DIR"

    if [ $VERBOSE -eq 1 ]; then
        cmake -DENABLE_COVERAGE=ON ..
    else
        cmake -DENABLE_COVERAGE=ON .. > /dev/null
    fi

    log_success "CMake configuration complete"
}

# Build the project and all tests
build_project() {
    log_info "Building project with coverage instrumentation..."

    cd "$PROJECT_ROOT/$BUILD_DIR"

    # Get CPU count for parallel build
    if [[ "$OSTYPE" == "darwin"* ]]; then
        CPU_COUNT=$(sysctl -n hw.ncpu)
    else
        CPU_COUNT=$(nproc)
    fi

    if [ $VERBOSE -eq 1 ]; then
        make -j"$CPU_COUNT"
    else
        make -j"$CPU_COUNT" > /dev/null 2>&1
    fi

    log_success "Build complete"
}

# Run all test executables
run_tests() {
    log_info "Running all tests..."

    cd "$PROJECT_ROOT/$BUILD_DIR"

    # Find all test executables
    local test_executables=$(find . -maxdepth 1 -type f -name "*Test" | sort)
    local total_tests=$(echo "$test_executables" | wc -l | tr -d ' ')
    local current_test=0
    local failed_tests=0

    log_info "Found $total_tests test executables"

    # Zero coverage counters before running tests
    lcov --directory . --zerocounters > /dev/null 2>&1

    for test_exe in $test_executables; do
        current_test=$((current_test + 1))
        local test_name=$(basename "$test_exe")

        echo -ne "${BLUE}[INFO]${NC} Running test $current_test/$total_tests: $test_name..."

        if [ $VERBOSE -eq 1 ]; then
            echo ""
            if ./"$test_name"; then
                log_success "Test passed: $test_name"
            else
                log_error "Test failed: $test_name"
                failed_tests=$((failed_tests + 1))
            fi
        else
            if ./"$test_name" > /dev/null 2>&1; then
                echo -e " ${GREEN}PASS${NC}"
            else
                echo -e " ${RED}FAIL${NC}"
                failed_tests=$((failed_tests + 1))
            fi
        fi
    done

    if [ $failed_tests -eq 0 ]; then
        log_success "All $total_tests tests passed"
    else
        log_warning "$failed_tests out of $total_tests tests failed"
    fi
}

# Generate coverage data
generate_coverage_data() {
    log_info "Collecting coverage data..."

    cd "$PROJECT_ROOT/$BUILD_DIR"

    # Capture coverage data
    if [ $VERBOSE -eq 1 ]; then
        lcov --directory . --capture --output-file coverage.info
    else
        lcov --directory . --capture --output-file coverage.info > /dev/null 2>&1
    fi

    # Remove unwanted files from coverage (system headers, tests, build artifacts)
    lcov --remove coverage.info \
        '/usr/*' \
        '*/tests/*' \
        '*/build/*' \
        '*/build-coverage/*' \
        '*/examples/*' \
        '*/benchmarks/*' \
        --output-file coverage.info.cleaned > /dev/null 2>&1

    log_success "Coverage data collected"
}

# Generate HTML report
generate_html_report() {
    log_info "Generating HTML coverage report..."

    cd "$PROJECT_ROOT/$BUILD_DIR"

    # Create output directory
    mkdir -p "$OUTPUT_DIR"

    # Generate HTML report
    if [ $VERBOSE -eq 1 ]; then
        genhtml coverage.info.cleaned \
            --output-directory "$OUTPUT_DIR" \
            --demangle-cpp \
            --title "cpptoc Coverage Report" \
            --legend \
            --show-details
    else
        genhtml coverage.info.cleaned \
            --output-directory "$OUTPUT_DIR" \
            --demangle-cpp \
            --title "cpptoc Coverage Report" \
            --legend \
            --show-details > /dev/null 2>&1
    fi

    log_success "HTML report generated in $BUILD_DIR/$OUTPUT_DIR/"
}

# Generate summary
generate_summary() {
    log_info "Generating coverage summary..."

    cd "$PROJECT_ROOT/$BUILD_DIR"

    echo ""
    echo "=========================================="
    echo "       Coverage Report Summary"
    echo "=========================================="

    # Generate and display summary
    lcov --summary coverage.info.cleaned 2>&1 | grep -E "(lines|functions|branches)"

    echo "=========================================="
    echo ""

    log_info "Detailed HTML report: $BUILD_DIR/$OUTPUT_DIR/index.html"
    log_info "To view the report, run: ./scripts/view_coverage.sh"
}

# Main execution
main() {
    log_info "Starting coverage report generation for cpptoc project"
    log_info "Project root: $PROJECT_ROOT"
    log_info "Build directory: $BUILD_DIR"
    log_info "Output directory: $OUTPUT_DIR"
    echo ""

    check_dependencies
    clean_build_dir
    configure_cmake
    build_project
    run_tests
    generate_coverage_data
    generate_html_report
    generate_summary

    log_success "Coverage report generation complete!"
}

# Run main function
main
