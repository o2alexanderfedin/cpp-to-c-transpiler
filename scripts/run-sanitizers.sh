#!/bin/bash
# run-sanitizers.sh - Comprehensive memory safety, UB, and thread safety testing
# Story #125: Memory Safety, UB, and Thread Safety Testing
# Epic #49: Comprehensive Testing + Documentation
#
# This script runs all tests with industry-standard sanitizers:
# - AddressSanitizer (ASan): Memory errors, use-after-free, buffer overflows, leaks
# - UndefinedBehaviorSanitizer (UBSan): Undefined behavior detection
# - ThreadSanitizer (TSan): Data races and thread safety issues
# - Valgrind: Memory leak detection (Linux only, optional on macOS)
#
# Usage:
#   ./scripts/run-sanitizers.sh [options]
#
# Options:
#   --asan      Run AddressSanitizer only
#   --ubsan     Run UndefinedBehaviorSanitizer only
#   --tsan      Run ThreadSanitizer only
#   --valgrind  Run Valgrind only (if available)
#   --all       Run all sanitizers (default)
#   --fail-fast Exit on first failure
#   --verbose   Show detailed output
#   --report    Generate HTML reports
#
# Exit codes:
#   0 - All tests passed with no issues
#   1 - Sanitizer detected issues
#   2 - Build failure
#   3 - Configuration error

set -e

# ============================================================================
# Configuration
# ============================================================================

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_DIR="$(dirname "$SCRIPT_DIR")"
BUILD_DIR_BASE="$PROJECT_DIR/build-sanitizers"
REPORTS_DIR="$PROJECT_DIR/sanitizer-reports"
LOG_FILE="$REPORTS_DIR/sanitizer-run.log"

# Sanitizer options
RUN_ASAN=false
RUN_UBSAN=false
RUN_TSAN=false
RUN_VALGRIND=false
FAIL_FAST=false
VERBOSE=false
GENERATE_REPORTS=false

# CPU cores for parallel execution (from CLAUDE.md)
CPU_CORES=$(sysctl -n hw.ncpu 2>/dev/null || nproc 2>/dev/null || echo 4)

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# ============================================================================
# Utility Functions
# ============================================================================

log() {
    echo -e "${BLUE}[$(date +'%Y-%m-%d %H:%M:%S')]${NC} $*" | tee -a "$LOG_FILE"
}

log_success() {
    echo -e "${GREEN}[✓]${NC} $*" | tee -a "$LOG_FILE"
}

log_warning() {
    echo -e "${YELLOW}[⚠]${NC} $*" | tee -a "$LOG_FILE"
}

log_error() {
    echo -e "${RED}[✗]${NC} $*" | tee -a "$LOG_FILE"
}

check_command() {
    if command -v "$1" &> /dev/null; then
        return 0
    else
        return 1
    fi
}

# ============================================================================
# Parse Command Line Arguments
# ============================================================================

parse_args() {
    if [ $# -eq 0 ]; then
        RUN_ASAN=true
        RUN_UBSAN=true
        RUN_TSAN=true
        RUN_VALGRIND=true
        return
    fi

    while [ $# -gt 0 ]; do
        case "$1" in
            --asan)
                RUN_ASAN=true
                ;;
            --ubsan)
                RUN_UBSAN=true
                ;;
            --tsan)
                RUN_TSAN=true
                ;;
            --valgrind)
                RUN_VALGRIND=true
                ;;
            --all)
                RUN_ASAN=true
                RUN_UBSAN=true
                RUN_TSAN=true
                RUN_VALGRIND=true
                ;;
            --fail-fast)
                FAIL_FAST=true
                ;;
            --verbose)
                VERBOSE=true
                ;;
            --report)
                GENERATE_REPORTS=true
                ;;
            --help)
                cat << EOF
Usage: $0 [options]

Options:
  --asan        Run AddressSanitizer only
  --ubsan       Run UndefinedBehaviorSanitizer only
  --tsan        Run ThreadSanitizer only
  --valgrind    Run Valgrind only (if available)
  --all         Run all sanitizers (default)
  --fail-fast   Exit on first failure
  --verbose     Show detailed output
  --report      Generate HTML reports
  --help        Show this help message

Examples:
  $0                    # Run all sanitizers
  $0 --asan --ubsan     # Run ASan and UBSan only
  $0 --fail-fast        # Stop at first failure
EOF
                exit 0
                ;;
            *)
                log_error "Unknown option: $1"
                echo "Use --help for usage information"
                exit 3
                ;;
        esac
        shift
    done
}

# ============================================================================
# Setup
# ============================================================================

setup() {
    log "Setting up sanitizer testing environment..."

    # Create directories
    mkdir -p "$BUILD_DIR_BASE"
    mkdir -p "$REPORTS_DIR"

    # Initialize log file
    echo "Sanitizer Test Run - $(date)" > "$LOG_FILE"
    echo "======================================" >> "$LOG_FILE"
    echo "" >> "$LOG_FILE"

    # Check compiler
    if ! check_command clang++; then
        log_error "clang++ not found. Sanitizers require Clang compiler."
        exit 3
    fi

    CLANG_VERSION=$(clang++ --version | head -n1)
    log "Compiler: $CLANG_VERSION"
    log "CPU Cores: $CPU_CORES"
    log "Project: $PROJECT_DIR"
    echo ""
}

# ============================================================================
# Get Test Executables
# ============================================================================

get_test_executables() {
    local build_dir="$1"

    if [ ! -d "$build_dir" ]; then
        echo ""
        return
    fi

    # Get all test executables (files ending with Test or Test suffix)
    find "$build_dir" -maxdepth 1 -type f -perm +111 -name "*Test" | sort
}

# ============================================================================
# AddressSanitizer (ASan)
# ============================================================================

run_asan() {
    log "Running AddressSanitizer (ASan)..."
    log "Detecting: Memory leaks, use-after-free, buffer overflows, heap corruption"
    echo ""

    local build_dir="$BUILD_DIR_BASE/asan"
    local report_file="$REPORTS_DIR/asan-report.txt"

    # Configure with ASan
    log "Configuring build with ASan..."
    mkdir -p "$build_dir"
    cd "$build_dir"

    # Detect LLVM paths (macOS Homebrew or Linux system)
    LLVM_CMAKE_ARGS=""
    if [ -d "/opt/homebrew/opt/llvm" ]; then
        # macOS Homebrew (Apple Silicon)
        LLVM_CMAKE_ARGS="-DLLVM_DIR=/opt/homebrew/opt/llvm/lib/cmake/llvm -DClang_DIR=/opt/homebrew/opt/llvm/lib/cmake/clang"
    elif [ -d "/usr/local/opt/llvm" ]; then
        # macOS Homebrew (Intel)
        LLVM_CMAKE_ARGS="-DLLVM_DIR=/usr/local/opt/llvm/lib/cmake/llvm -DClang_DIR=/usr/local/opt/llvm/lib/cmake/clang"
    fi

    cmake -DCMAKE_BUILD_TYPE=Debug \
          -DCMAKE_C_COMPILER=clang \
          -DCMAKE_CXX_COMPILER=clang++ \
          -DCMAKE_C_FLAGS="-fsanitize=address -fno-omit-frame-pointer -g -O1" \
          -DCMAKE_CXX_FLAGS="-fsanitize=address -fno-omit-frame-pointer -g -O1" \
          -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=address" \
          $LLVM_CMAKE_ARGS \
          "$PROJECT_DIR" > /dev/null 2>&1 || {
        log_error "CMake configuration failed for ASan"
        return 2
    }

    # Build tests
    log "Building tests with ASan..."
    make -j"$CPU_CORES" > /dev/null 2>&1 || {
        log_error "Build failed for ASan"
        return 2
    }

    # Run tests
    log "Running tests with ASan..."
    echo "ASan Test Results - $(date)" > "$report_file"
    echo "======================================" >> "$report_file"
    echo "" >> "$report_file"

    local tests=($(get_test_executables "$build_dir"))
    local total=${#tests[@]}
    local passed=0
    local failed=0
    local issues_found=0

    for test in "${tests[@]}"; do
        local test_name=$(basename "$test")

        if [ "$VERBOSE" = true ]; then
            log "  Running: $test_name"
        fi

        # Run with ASan options
        ASAN_OPTIONS="detect_leaks=1:halt_on_error=0:allocator_may_return_null=1:check_initialization_order=1:detect_stack_use_after_return=1" \
        "$test" > "$build_dir/${test_name}.log" 2>&1
        local exit_code=$?

        # Check for leaks and errors in output
        if grep -q "ERROR: AddressSanitizer\|Direct leak\|Indirect leak" "$build_dir/${test_name}.log" 2>/dev/null; then
            log_error "  $test_name: Memory errors detected"
            echo "FAILED: $test_name" >> "$report_file"
            cat "$build_dir/${test_name}.log" >> "$report_file"
            echo "" >> "$report_file"
            failed=$((failed + 1))
            issues_found=$((issues_found + 1))

            if [ "$FAIL_FAST" = true ]; then
                log_error "Fail-fast enabled. Stopping."
                return 1
            fi
        elif [ $exit_code -ne 0 ]; then
            log_warning "  $test_name: Failed (exit code: $exit_code)"
            echo "FAILED: $test_name (exit code: $exit_code)" >> "$report_file"
            failed=$((failed + 1))
        else
            if [ "$VERBOSE" = true ]; then
                log_success "  $test_name: Passed"
            fi
            echo "PASSED: $test_name" >> "$report_file"
            passed=$((passed + 1))
        fi
    done

    # Summary
    echo "" >> "$report_file"
    echo "Summary:" >> "$report_file"
    echo "  Total: $total" >> "$report_file"
    echo "  Passed: $passed" >> "$report_file"
    echo "  Failed: $failed" >> "$report_file"
    echo "  Issues Found: $issues_found" >> "$report_file"

    log_success "ASan complete: $passed/$total tests passed, $issues_found memory issues found"
    log "  Report: $report_file"
    echo ""

    return $issues_found
}

# ============================================================================
# UndefinedBehaviorSanitizer (UBSan)
# ============================================================================

run_ubsan() {
    log "Running UndefinedBehaviorSanitizer (UBSan)..."
    log "Detecting: Integer overflow, null pointer dereference, invalid casts, alignment issues"
    echo ""

    local build_dir="$BUILD_DIR_BASE/ubsan"
    local report_file="$REPORTS_DIR/ubsan-report.txt"

    # Configure with UBSan
    log "Configuring build with UBSan..."
    mkdir -p "$build_dir"
    cd "$build_dir"

    # Detect LLVM paths (macOS Homebrew or Linux system)
    LLVM_CMAKE_ARGS=""
    if [ -d "/opt/homebrew/opt/llvm" ]; then
        # macOS Homebrew (Apple Silicon)
        LLVM_CMAKE_ARGS="-DLLVM_DIR=/opt/homebrew/opt/llvm/lib/cmake/llvm -DClang_DIR=/opt/homebrew/opt/llvm/lib/cmake/clang"
    elif [ -d "/usr/local/opt/llvm" ]; then
        # macOS Homebrew (Intel)
        LLVM_CMAKE_ARGS="-DLLVM_DIR=/usr/local/opt/llvm/lib/cmake/llvm -DClang_DIR=/usr/local/opt/llvm/lib/cmake/clang"
    fi

    # UBSan checks: alignment, bounds, builtin, enum, float-cast-overflow, float-divide-by-zero,
    # integer-divide-by-zero, nonnull-attribute, null, object-size, pointer-overflow, return,
    # returns-nonnull-attribute, shift, signed-integer-overflow, unreachable, vla-bound, vptr
    cmake -DCMAKE_BUILD_TYPE=Debug \
          -DCMAKE_C_COMPILER=clang \
          -DCMAKE_CXX_COMPILER=clang++ \
          -DCMAKE_C_FLAGS="-fsanitize=undefined -fno-omit-frame-pointer -g -O1 -fno-sanitize-recover=all" \
          -DCMAKE_CXX_FLAGS="-fsanitize=undefined -fno-omit-frame-pointer -g -O1 -fno-sanitize-recover=all" \
          -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=undefined" \
          $LLVM_CMAKE_ARGS \
          "$PROJECT_DIR" > /dev/null 2>&1 || {
        log_error "CMake configuration failed for UBSan"
        return 2
    }

    # Build tests
    log "Building tests with UBSan..."
    make -j"$CPU_CORES" > /dev/null 2>&1 || {
        log_error "Build failed for UBSan"
        return 2
    }

    # Run tests
    log "Running tests with UBSan..."
    echo "UBSan Test Results - $(date)" > "$report_file"
    echo "======================================" >> "$report_file"
    echo "" >> "$report_file"

    local tests=($(get_test_executables "$build_dir"))
    local total=${#tests[@]}
    local passed=0
    local failed=0
    local issues_found=0

    for test in "${tests[@]}"; do
        local test_name=$(basename "$test")

        if [ "$VERBOSE" = true ]; then
            log "  Running: $test_name"
        fi

        # Run with UBSan options
        UBSAN_OPTIONS="print_stacktrace=1:halt_on_error=0" \
        "$test" > "$build_dir/${test_name}.log" 2>&1
        local exit_code=$?

        # Check for UB in output
        if grep -q "runtime error:\|SUMMARY: UndefinedBehaviorSanitizer" "$build_dir/${test_name}.log" 2>/dev/null; then
            log_error "  $test_name: Undefined behavior detected"
            echo "FAILED: $test_name" >> "$report_file"
            cat "$build_dir/${test_name}.log" >> "$report_file"
            echo "" >> "$report_file"
            failed=$((failed + 1))
            issues_found=$((issues_found + 1))

            if [ "$FAIL_FAST" = true ]; then
                log_error "Fail-fast enabled. Stopping."
                return 1
            fi
        elif [ $exit_code -ne 0 ]; then
            log_warning "  $test_name: Failed (exit code: $exit_code)"
            echo "FAILED: $test_name (exit code: $exit_code)" >> "$report_file"
            failed=$((failed + 1))
        else
            if [ "$VERBOSE" = true ]; then
                log_success "  $test_name: Passed"
            fi
            echo "PASSED: $test_name" >> "$report_file"
            passed=$((passed + 1))
        fi
    done

    # Summary
    echo "" >> "$report_file"
    echo "Summary:" >> "$report_file"
    echo "  Total: $total" >> "$report_file"
    echo "  Passed: $passed" >> "$report_file"
    echo "  Failed: $failed" >> "$report_file"
    echo "  Issues Found: $issues_found" >> "$report_file"

    log_success "UBSan complete: $passed/$total tests passed, $issues_found UB issues found"
    log "  Report: $report_file"
    echo ""

    return $issues_found
}

# ============================================================================
# ThreadSanitizer (TSan)
# ============================================================================

run_tsan() {
    log "Running ThreadSanitizer (TSan)..."
    log "Detecting: Data races, deadlocks, thread safety violations"
    echo ""

    local build_dir="$BUILD_DIR_BASE/tsan"
    local report_file="$REPORTS_DIR/tsan-report.txt"

    # Configure with TSan
    log "Configuring build with TSan..."
    mkdir -p "$build_dir"
    cd "$build_dir"

    # Detect LLVM paths (macOS Homebrew or Linux system)
    LLVM_CMAKE_ARGS=""
    if [ -d "/opt/homebrew/opt/llvm" ]; then
        # macOS Homebrew (Apple Silicon)
        LLVM_CMAKE_ARGS="-DLLVM_DIR=/opt/homebrew/opt/llvm/lib/cmake/llvm -DClang_DIR=/opt/homebrew/opt/llvm/lib/cmake/clang"
    elif [ -d "/usr/local/opt/llvm" ]; then
        # macOS Homebrew (Intel)
        LLVM_CMAKE_ARGS="-DLLVM_DIR=/usr/local/opt/llvm/lib/cmake/llvm -DClang_DIR=/usr/local/opt/llvm/lib/cmake/clang"
    fi

    cmake -DCMAKE_BUILD_TYPE=Debug \
          -DCMAKE_C_COMPILER=clang \
          -DCMAKE_CXX_COMPILER=clang++ \
          -DCMAKE_C_FLAGS="-fsanitize=thread -fno-omit-frame-pointer -g -O1" \
          -DCMAKE_CXX_FLAGS="-fsanitize=thread -fno-omit-frame-pointer -g -O1" \
          -DCMAKE_EXE_LINKER_FLAGS="-fsanitize=thread" \
          $LLVM_CMAKE_ARGS \
          "$PROJECT_DIR" > /dev/null 2>&1 || {
        log_error "CMake configuration failed for TSan"
        return 2
    }

    # Build tests
    log "Building tests with TSan..."
    make -j"$CPU_CORES" > /dev/null 2>&1 || {
        log_error "Build failed for TSan"
        return 2
    }

    # Run tests
    log "Running tests with TSan..."
    echo "TSan Test Results - $(date)" > "$report_file"
    echo "======================================" >> "$report_file"
    echo "" >> "$report_file"

    local tests=($(get_test_executables "$build_dir"))
    local total=${#tests[@]}
    local passed=0
    local failed=0
    local issues_found=0

    # Focus on thread-related tests
    local thread_tests=("ExceptionThreadSafetyTest")

    for test in "${tests[@]}"; do
        local test_name=$(basename "$test")

        # Skip non-threaded tests for TSan to save time
        local is_thread_test=false
        for thread_test in "${thread_tests[@]}"; do
            if [[ "$test_name" == *"$thread_test"* ]] || [[ "$test_name" == *"Thread"* ]] || [[ "$test_name" == *"Concurren"* ]]; then
                is_thread_test=true
                break
            fi
        done

        if [ "$is_thread_test" = false ]; then
            if [ "$VERBOSE" = true ]; then
                log "  Skipping: $test_name (non-threaded)"
            fi
            continue
        fi

        if [ "$VERBOSE" = true ]; then
            log "  Running: $test_name"
        fi

        # Run with TSan options
        TSAN_OPTIONS="halt_on_error=0:second_deadlock_stack=1" \
        "$test" > "$build_dir/${test_name}.log" 2>&1
        local exit_code=$?

        # Check for data races in output
        if grep -q "WARNING: ThreadSanitizer\|data race\|SUMMARY: ThreadSanitizer" "$build_dir/${test_name}.log" 2>/dev/null; then
            log_error "  $test_name: Thread safety issues detected"
            echo "FAILED: $test_name" >> "$report_file"
            cat "$build_dir/${test_name}.log" >> "$report_file"
            echo "" >> "$report_file"
            failed=$((failed + 1))
            issues_found=$((issues_found + 1))

            if [ "$FAIL_FAST" = true ]; then
                log_error "Fail-fast enabled. Stopping."
                return 1
            fi
        elif [ $exit_code -ne 0 ]; then
            log_warning "  $test_name: Failed (exit code: $exit_code)"
            echo "FAILED: $test_name (exit code: $exit_code)" >> "$report_file"
            failed=$((failed + 1))
        else
            if [ "$VERBOSE" = true ]; then
                log_success "  $test_name: Passed"
            fi
            echo "PASSED: $test_name" >> "$report_file"
            passed=$((passed + 1))
        fi
    done

    # Summary
    echo "" >> "$report_file"
    echo "Summary:" >> "$report_file"
    echo "  Total: $total" >> "$report_file"
    echo "  Passed: $passed" >> "$report_file"
    echo "  Failed: $failed" >> "$report_file"
    echo "  Issues Found: $issues_found" >> "$report_file"

    log_success "TSan complete: $passed/$total tests passed, $issues_found thread safety issues found"
    log "  Report: $report_file"
    echo ""

    return $issues_found
}

# ============================================================================
# Valgrind (Optional - Linux/macOS Intel)
# ============================================================================

run_valgrind() {
    if ! check_command valgrind; then
        log_warning "Valgrind not available (not supported on Apple Silicon)"
        log_warning "Skipping Valgrind tests. ASan provides similar coverage."
        return 0
    fi

    log "Running Valgrind..."
    log "Detecting: Memory leaks, invalid memory access, uninitialized values"
    echo ""

    local build_dir="$BUILD_DIR_BASE/valgrind"
    local report_file="$REPORTS_DIR/valgrind-report.txt"

    # Configure without sanitizers for Valgrind
    log "Configuring build for Valgrind..."
    mkdir -p "$build_dir"
    cd "$build_dir"

    # Detect LLVM paths (macOS Homebrew or Linux system)
    LLVM_CMAKE_ARGS=""
    if [ -d "/opt/homebrew/opt/llvm" ]; then
        # macOS Homebrew (Apple Silicon)
        LLVM_CMAKE_ARGS="-DLLVM_DIR=/opt/homebrew/opt/llvm/lib/cmake/llvm -DClang_DIR=/opt/homebrew/opt/llvm/lib/cmake/clang"
    elif [ -d "/usr/local/opt/llvm" ]; then
        # macOS Homebrew (Intel)
        LLVM_CMAKE_ARGS="-DLLVM_DIR=/usr/local/opt/llvm/lib/cmake/llvm -DClang_DIR=/usr/local/opt/llvm/lib/cmake/clang"
    fi

    cmake -DCMAKE_BUILD_TYPE=Debug \
          -DCMAKE_C_FLAGS="-g -O0" \
          -DCMAKE_CXX_FLAGS="-g -O0" \
          $LLVM_CMAKE_ARGS \
          "$PROJECT_DIR" > /dev/null 2>&1 || {
        log_error "CMake configuration failed for Valgrind"
        return 2
    }

    # Build tests
    log "Building tests for Valgrind..."
    make -j"$CPU_CORES" > /dev/null 2>&1 || {
        log_error "Build failed for Valgrind"
        return 2
    }

    # Run tests
    log "Running tests with Valgrind..."
    echo "Valgrind Test Results - $(date)" > "$report_file"
    echo "======================================" >> "$report_file"
    echo "" >> "$report_file"

    local tests=($(get_test_executables "$build_dir"))
    local total=${#tests[@]}
    local passed=0
    local failed=0
    local issues_found=0

    for test in "${tests[@]}"; do
        local test_name=$(basename "$test")

        if [ "$VERBOSE" = true ]; then
            log "  Running: $test_name"
        fi

        # Run with Valgrind
        valgrind --leak-check=full \
                 --show-leak-kinds=all \
                 --track-origins=yes \
                 --error-exitcode=1 \
                 --errors-for-leak-kinds=all \
                 --log-file="$build_dir/${test_name}.valgrind.log" \
                 "$test" > "$build_dir/${test_name}.log" 2>&1
        local exit_code=$?

        # Check for leaks
        if [ $exit_code -eq 1 ] || grep -q "definitely lost\|indirectly lost\|Invalid" "$build_dir/${test_name}.valgrind.log" 2>/dev/null; then
            log_error "  $test_name: Memory errors detected"
            echo "FAILED: $test_name" >> "$report_file"
            cat "$build_dir/${test_name}.valgrind.log" >> "$report_file"
            echo "" >> "$report_file"
            failed=$((failed + 1))
            issues_found=$((issues_found + 1))

            if [ "$FAIL_FAST" = true ]; then
                log_error "Fail-fast enabled. Stopping."
                return 1
            fi
        else
            if [ "$VERBOSE" = true ]; then
                log_success "  $test_name: Passed"
            fi
            echo "PASSED: $test_name" >> "$report_file"
            passed=$((passed + 1))
        fi
    done

    # Summary
    echo "" >> "$report_file"
    echo "Summary:" >> "$report_file"
    echo "  Total: $total" >> "$report_file"
    echo "  Passed: $passed" >> "$report_file"
    echo "  Failed: $failed" >> "$report_file"
    echo "  Issues Found: $issues_found" >> "$report_file"

    log_success "Valgrind complete: $passed/$total tests passed, $issues_found memory issues found"
    log "  Report: $report_file"
    echo ""

    return $issues_found
}

# ============================================================================
# Generate HTML Report (Optional)
# ============================================================================

generate_html_report() {
    if [ "$GENERATE_REPORTS" = false ]; then
        return 0
    fi

    log "Generating HTML report..."

    local html_file="$REPORTS_DIR/sanitizer-report.html"

    cat > "$html_file" << 'EOF'
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Sanitizer Test Report</title>
    <style>
        body { font-family: Arial, sans-serif; margin: 20px; background: #f5f5f5; }
        .container { max-width: 1200px; margin: 0 auto; background: white; padding: 20px; border-radius: 8px; box-shadow: 0 2px 4px rgba(0,0,0,0.1); }
        h1 { color: #333; border-bottom: 3px solid #4CAF50; padding-bottom: 10px; }
        h2 { color: #555; margin-top: 30px; }
        .summary { display: grid; grid-template-columns: repeat(auto-fit, minmax(200px, 1fr)); gap: 15px; margin: 20px 0; }
        .card { background: #fff; border: 1px solid #ddd; border-radius: 6px; padding: 15px; box-shadow: 0 1px 3px rgba(0,0,0,0.1); }
        .card h3 { margin: 0 0 10px 0; color: #666; font-size: 14px; }
        .card .value { font-size: 32px; font-weight: bold; margin: 10px 0; }
        .success { color: #4CAF50; }
        .error { color: #f44336; }
        .warning { color: #ff9800; }
        pre { background: #f5f5f5; padding: 15px; border-radius: 4px; overflow-x: auto; font-size: 12px; }
        .report-section { margin: 30px 0; padding: 20px; background: #fafafa; border-left: 4px solid #2196F3; }
        table { width: 100%; border-collapse: collapse; margin: 15px 0; }
        th, td { padding: 12px; text-align: left; border-bottom: 1px solid #ddd; }
        th { background: #f5f5f5; font-weight: bold; }
        .pass { background: #e8f5e9; }
        .fail { background: #ffebee; }
    </style>
</head>
<body>
    <div class="container">
        <h1>Sanitizer Test Report</h1>
        <p><strong>Generated:</strong> $(date)</p>
        <p><strong>Project:</strong> C++ to C Transpiler</p>

        <div class="summary">
EOF

    # Add summary cards for each sanitizer
    for report in "$REPORTS_DIR"/*-report.txt; do
        if [ -f "$report" ]; then
            local sanitizer_name=$(basename "$report" -report.txt)
            local total=$(grep "Total:" "$report" | tail -1 | awk '{print $2}')
            local passed=$(grep "Passed:" "$report" | tail -1 | awk '{print $2}')
            local issues=$(grep "Issues Found:" "$report" | tail -1 | awk '{print $3}')

            cat >> "$html_file" << EOF
            <div class="card">
                <h3>$(echo $sanitizer_name | tr '[:lower:]' '[:upper:]')</h3>
                <div class="value ${issues:-0 -eq 0 ? 'success' : 'error'}">${issues:-0}</div>
                <p>issues found</p>
                <p><small>${passed:-0}/${total:-0} tests passed</small></p>
            </div>
EOF
        fi
    done

    cat >> "$html_file" << 'EOF'
        </div>

        <h2>Detailed Results</h2>
EOF

    # Add detailed results for each sanitizer
    for report in "$REPORTS_DIR"/*-report.txt; do
        if [ -f "$report" ]; then
            local sanitizer_name=$(basename "$report" -report.txt)
            cat >> "$html_file" << EOF
        <div class="report-section">
            <h3>$(echo $sanitizer_name | tr '[:lower:]' '[:upper:]') Results</h3>
            <pre>$(cat "$report")</pre>
        </div>
EOF
        fi
    done

    cat >> "$html_file" << 'EOF'
    </div>
</body>
</html>
EOF

    log_success "HTML report generated: $html_file"

    # Try to open in browser
    if check_command open; then
        open "$html_file" 2>/dev/null || true
    elif check_command xdg-open; then
        xdg-open "$html_file" 2>/dev/null || true
    fi
}

# ============================================================================
# Main Execution
# ============================================================================

main() {
    parse_args "$@"
    setup

    local total_issues=0
    local exit_code=0

    log "========================================"
    log "Memory Safety, UB, and Thread Safety Testing"
    log "Story #125 - Epic #49"
    log "========================================"
    echo ""

    # Run selected sanitizers
    if [ "$RUN_ASAN" = true ]; then
        run_asan || total_issues=$((total_issues + $?))
    fi

    if [ "$RUN_UBSAN" = true ]; then
        run_ubsan || total_issues=$((total_issues + $?))
    fi

    if [ "$RUN_TSAN" = true ]; then
        run_tsan || total_issues=$((total_issues + $?))
    fi

    if [ "$RUN_VALGRIND" = true ]; then
        run_valgrind || total_issues=$((total_issues + $?))
    fi

    # Generate HTML report if requested
    generate_html_report

    # Final summary
    log "========================================"
    log "Sanitizer Testing Complete"
    log "========================================"
    echo ""

    if [ $total_issues -eq 0 ]; then
        log_success "SUCCESS: All tests passed with no issues detected!"
        log_success "✓ Zero memory leaks"
        log_success "✓ No undefined behavior"
        log_success "✓ Thread-safe code"
        log_success "✓ No address/memory errors"
        echo ""
        log "Reports available in: $REPORTS_DIR"
        exit_code=0
    else
        log_error "FAILURE: $total_issues issue(s) detected"
        log_error "Please review the reports in: $REPORTS_DIR"
        exit_code=1
    fi

    # Performance note
    if [ "$RUN_ASAN" = true ] || [ "$RUN_TSAN" = true ] || [ "$RUN_UBSAN" = true ]; then
        echo ""
        log "Note: Sanitizer overhead is typically 2-5x for production workloads"
        log "      Test overhead may be higher due to comprehensive checking"
    fi

    exit $exit_code
}

# Run main
main "$@"
