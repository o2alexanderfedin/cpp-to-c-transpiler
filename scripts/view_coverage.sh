#!/bin/bash
#
# View Code Coverage Report
#
# This script opens the HTML coverage report in the default browser.
# It also provides options to view specific metrics or generate text reports.
#
# Usage:
#   ./scripts/view_coverage.sh [options]
#
# Options:
#   --build-dir DIR  Specify build directory (default: build-coverage)
#   --output-dir DIR Specify output directory (default: coverage)
#   --summary        Show coverage summary in terminal
#   --text           Generate text coverage report
#   --no-browser     Don't open browser
#   --help           Show this help message
#

set -e  # Exit on error

# Default configuration
BUILD_DIR="build-coverage"
OUTPUT_DIR="coverage"
SHOW_SUMMARY=0
GENERATE_TEXT=0
OPEN_BROWSER=1
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
        --build-dir)
            BUILD_DIR="$2"
            shift 2
            ;;
        --output-dir)
            OUTPUT_DIR="$2"
            shift 2
            ;;
        --summary)
            SHOW_SUMMARY=1
            shift
            ;;
        --text)
            GENERATE_TEXT=1
            shift
            ;;
        --no-browser)
            OPEN_BROWSER=0
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

log_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Check if coverage report exists
check_coverage_exists() {
    local coverage_file="$PROJECT_ROOT/$BUILD_DIR/coverage.info.cleaned"
    local html_index="$PROJECT_ROOT/$BUILD_DIR/$OUTPUT_DIR/index.html"

    if [ ! -f "$coverage_file" ]; then
        log_error "Coverage data not found at: $coverage_file"
        log_info "Please run './scripts/generate_coverage.sh' first"
        exit 1
    fi

    if [ ! -f "$html_index" ]; then
        log_error "HTML coverage report not found at: $html_index"
        log_info "Please run './scripts/generate_coverage.sh' first"
        exit 1
    fi
}

# Show summary in terminal
show_summary() {
    log_info "Coverage Summary:"
    echo ""
    echo "=========================================="
    echo "       Coverage Report Summary"
    echo "=========================================="

    cd "$PROJECT_ROOT/$BUILD_DIR"

    # Display summary
    lcov --summary coverage.info.cleaned 2>&1 | grep -E "(lines|functions|branches)" | while read line; do
        if [[ $line =~ ([0-9.]+%) ]]; then
            percentage="${BASH_REMATCH[1]}"
            percentage_value=$(echo "$percentage" | tr -d '%')

            # Color code based on percentage
            if (( $(echo "$percentage_value >= 80" | bc -l) )); then
                echo -e "${GREEN}$line${NC}"
            elif (( $(echo "$percentage_value >= 60" | bc -l) )); then
                echo -e "${YELLOW}$line${NC}"
            else
                echo -e "${RED}$line${NC}"
            fi
        else
            echo "$line"
        fi
    done

    echo "=========================================="
    echo ""
}

# Generate text report
generate_text_report() {
    log_info "Generating text coverage report..."

    cd "$PROJECT_ROOT/$BUILD_DIR"

    local text_report="coverage_report.txt"

    # Generate detailed text report
    {
        echo "Code Coverage Report"
        echo "===================="
        echo ""
        echo "Generated: $(date)"
        echo "Project: cpptoc - C++ to C Transpiler"
        echo ""
        echo "Overall Coverage:"
        echo "-----------------"
        lcov --summary coverage.info.cleaned 2>&1 | grep -E "(lines|functions|branches)"
        echo ""
        echo "Per-File Coverage:"
        echo "------------------"
        lcov --list coverage.info.cleaned 2>&1
    } > "$text_report"

    log_success "Text report generated: $BUILD_DIR/$text_report"
}

# Open coverage report in browser
open_in_browser() {
    local html_index="$PROJECT_ROOT/$BUILD_DIR/$OUTPUT_DIR/index.html"

    log_info "Opening coverage report in browser..."

    if [[ "$OSTYPE" == "darwin"* ]]; then
        # macOS
        open "$html_index"
    elif [[ "$OSTYPE" == "linux-gnu"* ]]; then
        # Linux
        if command -v xdg-open &> /dev/null; then
            xdg-open "$html_index"
        else
            log_error "Cannot open browser automatically. Please open manually:"
            echo "  file://$html_index"
            return 1
        fi
    else
        log_error "Cannot open browser automatically on this platform. Please open manually:"
        echo "  file://$html_index"
        return 1
    fi

    log_success "Coverage report opened in browser"
}

# Display coverage statistics by category
show_detailed_stats() {
    cd "$PROJECT_ROOT/$BUILD_DIR"

    echo ""
    echo "=========================================="
    echo "    Detailed Coverage Statistics"
    echo "=========================================="
    echo ""

    # Show files with lowest coverage
    echo "Files with Lowest Coverage:"
    echo "---------------------------"
    lcov --list coverage.info.cleaned 2>&1 | \
        grep -E '\.cpp|\.c' | \
        sort -t'|' -k2 -n | \
        head -10 | \
        sed 's/^/  /'

    echo ""
}

# Main execution
main() {
    log_info "Code Coverage Report Viewer"
    log_info "Project root: $PROJECT_ROOT"
    echo ""

    check_coverage_exists

    if [ $SHOW_SUMMARY -eq 1 ]; then
        show_summary
        show_detailed_stats
    fi

    if [ $GENERATE_TEXT -eq 1 ]; then
        generate_text_report
    fi

    if [ $OPEN_BROWSER -eq 1 ]; then
        open_in_browser
    fi

    if [ $SHOW_SUMMARY -eq 0 ] && [ $GENERATE_TEXT -eq 0 ] && [ $OPEN_BROWSER -eq 0 ]; then
        log_info "No action specified. Use --help for usage information"
        exit 1
    fi

    log_success "Done!"
}

# Run main function
main
