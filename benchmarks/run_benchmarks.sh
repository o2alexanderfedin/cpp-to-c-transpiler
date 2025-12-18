#!/bin/bash
#
# run_benchmarks.sh
#
# Performance Benchmark Suite Runner for C++ to C Transpiler
#
# This script runs all performance benchmarks and generates a comprehensive
# performance report. It can be used for local development, CI/CD pipelines,
# and performance regression detection.
#
# Usage:
#   ./benchmarks/run_benchmarks.sh [options]
#
# Options:
#   --quick         Run quick benchmarks (fewer iterations)
#   --verbose       Show detailed output from each benchmark
#   --baseline      Save results as baseline for future comparisons
#   --compare FILE  Compare current results against baseline
#   --ci            CI mode (fail on any regression)
#   --help          Show this help message
#
# Examples:
#   ./benchmarks/run_benchmarks.sh
#   ./benchmarks/run_benchmarks.sh --quick
#   ./benchmarks/run_benchmarks.sh --baseline
#   ./benchmarks/run_benchmarks.sh --compare baseline.json --ci

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
BOLD='\033[1m'
NC='\033[0m' # No Color

# Script configuration
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_DIR="$PROJECT_ROOT/build"
RESULTS_DIR="$PROJECT_ROOT/benchmark-results"
TIMESTAMP=$(date +"%Y%m%d_%H%M%S")
RESULTS_FILE="$RESULTS_DIR/benchmark_${TIMESTAMP}.txt"
JSON_FILE="$RESULTS_DIR/benchmark_${TIMESTAMP}.json"

# Parse command-line options
QUICK_MODE=false
VERBOSE_MODE=false
BASELINE_MODE=false
COMPARE_FILE=""
CI_MODE=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --quick)
            QUICK_MODE=true
            shift
            ;;
        --verbose)
            VERBOSE_MODE=true
            shift
            ;;
        --baseline)
            BASELINE_MODE=true
            shift
            ;;
        --compare)
            COMPARE_FILE="$2"
            shift 2
            ;;
        --ci)
            CI_MODE=true
            shift
            ;;
        --help)
            grep '^#' "$0" | grep -v '#!/bin/bash' | sed 's/^# //' | sed 's/^#//'
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            echo "Use --help for usage information"
            exit 1
            ;;
    esac
done

# Create results directory
mkdir -p "$RESULTS_DIR"

# Function to print colored messages
print_header() {
    echo -e "${BOLD}${BLUE}========================================${NC}"
    echo -e "${BOLD}${BLUE}$1${NC}"
    echo -e "${BOLD}${BLUE}========================================${NC}"
}

print_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

print_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

print_pass() {
    echo -e "${GREEN}✓ PASS${NC} $1"
}

print_fail() {
    echo -e "${RED}✗ FAIL${NC} $1"
}

# Function to check if benchmarks are built
check_benchmarks_built() {
    local all_built=true

    for benchmark in benchmark_ast_traversal benchmark_name_mangling benchmark_code_generation \
                     benchmark_e2e_transpilation benchmark_memory_usage benchmark_virtual_functions; do
        if [ ! -f "$BUILD_DIR/$benchmark" ]; then
            print_error "Benchmark not found: $benchmark"
            print_info "Build benchmarks with: cmake -B build -DBUILD_BENCHMARKS=ON && cmake --build build"
            all_built=false
        fi
    done

    if [ "$all_built" = false ]; then
        exit 1
    fi
}

# Function to run a single benchmark
run_benchmark() {
    local benchmark_name="$1"
    local benchmark_path="$BUILD_DIR/$benchmark_name"
    local benchmark_title="$2"

    echo ""
    print_header "$benchmark_title"

    if [ ! -f "$benchmark_path" ]; then
        print_error "Benchmark executable not found: $benchmark_path"
        return 1
    fi

    # Run benchmark
    if [ "$VERBOSE_MODE" = true ]; then
        "$benchmark_path" | tee -a "$RESULTS_FILE"
    else
        "$benchmark_path" >> "$RESULTS_FILE" 2>&1
    fi

    local exit_code=${PIPESTATUS[0]}

    # Check result
    if [ $exit_code -eq 0 ]; then
        print_pass "$benchmark_title completed successfully"
        return 0
    else
        print_fail "$benchmark_title failed with exit code $exit_code"
        return 1
    fi
}

# Function to extract performance metrics from benchmark output
extract_metrics() {
    local benchmark_output="$1"

    # This is a placeholder - actual implementation would parse benchmark output
    # and extract metrics like mean, median, min, max, std dev, pass/fail status

    echo "Metrics extraction not yet implemented"
}

# Function to generate JSON report
generate_json_report() {
    cat > "$JSON_FILE" <<EOF
{
  "timestamp": "$(date -u +"%Y-%m-%dT%H:%M:%SZ")",
  "git_commit": "$(cd "$PROJECT_ROOT" && git rev-parse HEAD 2>/dev/null || echo 'unknown')",
  "git_branch": "$(cd "$PROJECT_ROOT" && git rev-parse --abbrev-ref HEAD 2>/dev/null || echo 'unknown')",
  "hostname": "$(hostname)",
  "os": "$(uname -s)",
  "cpu_cores": "$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 'unknown')",
  "quick_mode": $QUICK_MODE,
  "benchmarks": {
    "ast_traversal": {},
    "name_mangling": {},
    "code_generation": {},
    "e2e_transpilation": {},
    "memory_usage": {},
    "virtual_functions": {}
  },
  "summary": {
    "total_benchmarks": 6,
    "passed": 0,
    "failed": 0,
    "warnings": 0
  }
}
EOF

    print_info "JSON report saved to: $JSON_FILE"
}

# Function to compare with baseline
compare_with_baseline() {
    local baseline_file="$1"

    if [ ! -f "$baseline_file" ]; then
        print_error "Baseline file not found: $baseline_file"
        return 1
    fi

    print_header "Baseline Comparison"
    print_info "Comparing against: $baseline_file"
    echo ""

    # This is a placeholder - actual implementation would parse both JSON files
    # and compare performance metrics, highlighting regressions and improvements

    print_warn "Baseline comparison not yet fully implemented"
    echo ""
}

# Function to save as baseline
save_as_baseline() {
    local baseline_file="$RESULTS_DIR/baseline.json"

    cp "$JSON_FILE" "$baseline_file"
    print_info "Results saved as baseline: $baseline_file"
}

# Main execution
print_header "C++ to C Transpiler - Performance Benchmark Suite"

# Print configuration
echo ""
print_info "Configuration:"
echo "  Project Root:   $PROJECT_ROOT"
echo "  Build Dir:      $BUILD_DIR"
echo "  Results Dir:    $RESULTS_DIR"
echo "  Quick Mode:     $QUICK_MODE"
echo "  Verbose Mode:   $VERBOSE_MODE"
echo "  CI Mode:        $CI_MODE"
echo "  Baseline Mode:  $BASELINE_MODE"
if [ -n "$COMPARE_FILE" ]; then
    echo "  Compare File:   $COMPARE_FILE"
fi
echo ""

# Print system info
print_info "System Information:"
echo "  Hostname:       $(hostname)"
echo "  OS:             $(uname -s) $(uname -r)"
echo "  CPU Cores:      $(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 'unknown')"
echo "  Git Commit:     $(cd "$PROJECT_ROOT" && git rev-parse --short HEAD 2>/dev/null || echo 'unknown')"
echo "  Git Branch:     $(cd "$PROJECT_ROOT" && git rev-parse --abbrev-ref HEAD 2>/dev/null || echo 'unknown')"
echo ""

# Check if benchmarks are built
print_info "Checking benchmark executables..."
check_benchmarks_built
print_info "All benchmark executables found"
echo ""

# Initialize results file
cat > "$RESULTS_FILE" <<EOF
C++ to C Transpiler - Performance Benchmark Results
====================================================
Date: $(date)
Git Commit: $(cd "$PROJECT_ROOT" && git rev-parse HEAD 2>/dev/null || echo 'unknown')
Git Branch: $(cd "$PROJECT_ROOT" && git rev-parse --abbrev-ref HEAD 2>/dev/null || echo 'unknown')
Hostname: $(hostname)
OS: $(uname -s) $(uname -r)
CPU Cores: $(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 'unknown')
Quick Mode: $QUICK_MODE
====================================================

EOF

# Counters for summary
TOTAL_BENCHMARKS=0
PASSED_BENCHMARKS=0
FAILED_BENCHMARKS=0

# Run all benchmarks
BENCHMARKS=(
    "benchmark_ast_traversal|AST Traversal Performance"
    "benchmark_name_mangling|Name Mangling Performance"
    "benchmark_code_generation|Code Generation Performance"
    "benchmark_e2e_transpilation|End-to-End Transpilation Performance"
    "benchmark_memory_usage|Memory Usage Profiling"
    "benchmark_virtual_functions|Virtual Function Resolution Performance"
)

for benchmark_spec in "${BENCHMARKS[@]}"; do
    IFS='|' read -r benchmark_name benchmark_title <<< "$benchmark_spec"

    TOTAL_BENCHMARKS=$((TOTAL_BENCHMARKS + 1))

    if run_benchmark "$benchmark_name" "$benchmark_title"; then
        PASSED_BENCHMARKS=$((PASSED_BENCHMARKS + 1))
    else
        FAILED_BENCHMARKS=$((FAILED_BENCHMARKS + 1))
    fi
done

# Generate summary
echo "" | tee -a "$RESULTS_FILE"
print_header "Benchmark Summary"
echo "" | tee -a "$RESULTS_FILE"
echo "Total Benchmarks:   $TOTAL_BENCHMARKS" | tee -a "$RESULTS_FILE"
echo "Passed:             $PASSED_BENCHMARKS" | tee -a "$RESULTS_FILE"
echo "Failed:             $FAILED_BENCHMARKS" | tee -a "$RESULTS_FILE"

if [ $TOTAL_BENCHMARKS -gt 0 ]; then
    SUCCESS_RATE=$(awk "BEGIN {printf \"%.1f\", ($PASSED_BENCHMARKS/$TOTAL_BENCHMARKS)*100}")
    echo "Success Rate:       $SUCCESS_RATE%" | tee -a "$RESULTS_FILE"
else
    SUCCESS_RATE=0
fi

echo "" | tee -a "$RESULTS_FILE"

# Determine overall status
if [ $FAILED_BENCHMARKS -eq 0 ]; then
    print_pass "All benchmarks passed!" | tee -a "$RESULTS_FILE"
    OVERALL_STATUS=0
elif [ $PASSED_BENCHMARKS -ge $((TOTAL_BENCHMARKS * 6 / 10)) ]; then
    print_warn "Some benchmarks failed (>= 60% passed)" | tee -a "$RESULTS_FILE"
    OVERALL_STATUS=0
else
    print_fail "Too many benchmark failures (< 60% passed)" | tee -a "$RESULTS_FILE"
    OVERALL_STATUS=1
fi

echo "" | tee -a "$RESULTS_FILE"
print_info "Results saved to: $RESULTS_FILE"

# Generate JSON report
generate_json_report

# Save as baseline if requested
if [ "$BASELINE_MODE" = true ]; then
    save_as_baseline
fi

# Compare with baseline if requested
if [ -n "$COMPARE_FILE" ]; then
    compare_with_baseline "$COMPARE_FILE"
fi

# Print final summary
echo ""
print_header "Benchmark Run Complete"
echo ""
print_info "Results Directory: $RESULTS_DIR"
print_info "Text Report:       $RESULTS_FILE"
print_info "JSON Report:       $JSON_FILE"

if [ "$BASELINE_MODE" = true ]; then
    print_info "Baseline:          $RESULTS_DIR/baseline.json"
fi

echo ""

# Exit with appropriate code
if [ "$CI_MODE" = true ]; then
    # In CI mode, fail on any benchmark failure
    if [ $FAILED_BENCHMARKS -gt 0 ]; then
        print_error "CI mode: Failing due to benchmark failures"
        exit 1
    fi
fi

exit $OVERALL_STATUS
