#!/bin/bash
# generate-coverage.sh - Code coverage report generation
set -e

BUILD_DIR="${BUILD_DIR:-build}"
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

echo "=========================================="
echo "Code Coverage Report Generation"
echo "=========================================="

# Check for required tools
if ! command -v lcov &> /dev/null; then
    echo -e "${RED}ERROR: lcov not found. Install with: brew install lcov${NC}"
    exit 1
fi

if ! command -v genhtml &> /dev/null; then
    echo -e "${RED}ERROR: genhtml not found. Install with: brew install lcov${NC}"
    exit 1
fi

# Rebuild with coverage enabled
echo -e "${YELLOW}Rebuilding with coverage enabled...${NC}"
mkdir -p "$PROJECT_ROOT/$BUILD_DIR"
cd "$PROJECT_ROOT/$BUILD_DIR"
cmake -DENABLE_COVERAGE=ON ..
make -j$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

# Initialize coverage data
echo -e "${YELLOW}Initializing coverage data...${NC}"
lcov --directory . --zerocounters

# Run all tests
echo -e "${YELLOW}Running tests...${NC}"
ctest --parallel $(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

# Capture coverage data
echo -e "${YELLOW}Capturing coverage data...${NC}"
lcov --directory . --capture --output-file coverage.info

# Remove system and test files from coverage
echo -e "${YELLOW}Filtering coverage data...${NC}"
lcov --remove coverage.info \
    '/usr/*' \
    '*/tests/*' \
    '*/build/*' \
    '*/examples/*' \
    '*/benchmarks/*' \
    --output-file coverage.info.cleaned

# Generate HTML report
echo -e "${YELLOW}Generating HTML report...${NC}"
genhtml coverage.info.cleaned \
    --output-directory coverage \
    --demangle-cpp \
    --title "C++ to C Transpiler Coverage" \
    --legend \
    --show-details

# Summary
echo ""
echo "=========================================="
echo -e "${GREEN}Coverage report generated!${NC}"
echo "=========================================="
echo "HTML report: $BUILD_DIR/coverage/index.html"
echo ""
echo "Open with: open $BUILD_DIR/coverage/index.html"
echo ""

# Extract summary statistics
lcov --summary coverage.info.cleaned
