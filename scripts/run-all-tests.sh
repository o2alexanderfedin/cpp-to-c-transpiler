#!/bin/bash
# run-all-tests.sh - Unified test execution for C++ to C transpiler
set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Configuration
BUILD_DIR="${BUILD_DIR:-build}"
PARALLEL_JOBS="${PARALLEL_JOBS:-$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)}"
VERBOSE="${VERBOSE:-0}"
COVERAGE="${COVERAGE:-0}"
PROJECT_ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

echo "=========================================="
echo "C++ to C Transpiler - Test Suite Runner"
echo "=========================================="
echo "Project root: $PROJECT_ROOT"
echo "Build directory: $BUILD_DIR"
echo "Parallel jobs: $PARALLEL_JOBS"
echo ""

# Build tests if needed
if [ ! -d "$PROJECT_ROOT/$BUILD_DIR" ] || [ "$1" == "--rebuild" ]; then
    echo -e "${YELLOW}Building tests...${NC}"
    mkdir -p "$PROJECT_ROOT/$BUILD_DIR"
    cd "$PROJECT_ROOT/$BUILD_DIR"

    if [ "$COVERAGE" == "1" ]; then
        cmake -DENABLE_COVERAGE=ON ..
    else
        cmake ..
    fi

    make -j"$PARALLEL_JOBS"
    cd "$PROJECT_ROOT"
fi

# Run tests
echo -e "${YELLOW}Running tests...${NC}"
cd "$PROJECT_ROOT/$BUILD_DIR"

if [ "$VERBOSE" == "1" ]; then
    ctest --output-on-failure --parallel "$PARALLEL_JOBS"
else
    ctest --parallel "$PARALLEL_JOBS"
fi

TEST_RESULT=$?

# Summary
echo ""
echo "=========================================="
if [ $TEST_RESULT -eq 0 ]; then
    echo -e "${GREEN}✓ All tests passed!${NC}"
else
    echo -e "${RED}✗ Some tests failed${NC}"
fi
echo "=========================================="

# Coverage report if enabled
if [ "$COVERAGE" == "1" ]; then
    echo ""
    echo -e "${YELLOW}Generating coverage report...${NC}"
    make coverage
    echo -e "${GREEN}Coverage report generated in $BUILD_DIR/coverage/index.html${NC}"
fi

exit $TEST_RESULT
