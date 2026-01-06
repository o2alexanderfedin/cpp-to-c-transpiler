#!/bin/bash
#
# HandlerContext Retirement Verification Script
#
# This script verifies the state of HandlerContext retirement in the C++ to C transpiler codebase.
#
# Exit codes:
#   0 - All checks passed (HandlerContext fully retired)
#   1 - One or more checks failed (HandlerContext still in use)
#

set -e

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
BUILD_DIR="$PROJECT_ROOT/build"

echo -e "${BLUE}=== HandlerContext Retirement Verification ===${NC}\n"

TOTAL_CHECKS=7
PASSED_CHECKS=0
FAILED_CHECKS=0

# Check 1: HandlerContext references in production code
echo -e "${BLUE}1. Checking for HandlerContext references in production code...${NC}"
INCLUDE_REFS=$(grep -r "HandlerContext" "$PROJECT_ROOT/include" --include="*.cpp" --include="*.h" 2>/dev/null | wc -l)
SRC_REFS=$(grep -r "HandlerContext" "$PROJECT_ROOT/src" --include="*.cpp" --include="*.h" 2>/dev/null | wc -l)
TOTAL_PROD_REFS=$((INCLUDE_REFS + SRC_REFS))

if [ $TOTAL_PROD_REFS -eq 0 ]; then
    echo -e "${GREEN}✓ PASS: No HandlerContext references in production code${NC}"
    ((PASSED_CHECKS++))
else
    echo -e "${RED}❌ FAIL: Found $TOTAL_PROD_REFS HandlerContext references${NC}"
    echo -e "   include/: $INCLUDE_REFS references"
    echo -e "   src/: $SRC_REFS references"
    echo -e "\n   Files with references:"
    grep -r "HandlerContext" "$PROJECT_ROOT/include" "$PROJECT_ROOT/src" --include="*.cpp" --include="*.h" 2>/dev/null | cut -d: -f1 | sort -u | sed 's/^/   - /'
    ((FAILED_CHECKS++))
fi
echo ""

# Check 2: Build status
echo -e "${BLUE}2. Building project...${NC}"
if [ ! -d "$BUILD_DIR" ]; then
    echo -e "${YELLOW}⚠️  WARNING: Build directory not found at $BUILD_DIR${NC}"
    echo -e "   Creating build directory and running cmake..."
    mkdir -p "$BUILD_DIR"
    cd "$BUILD_DIR"
    cmake .. > /dev/null 2>&1
fi

cd "$BUILD_DIR"
if cmake --build . --clean-first > /tmp/verify_build.log 2>&1; then
    echo -e "${GREEN}✓ PASS: Build successful${NC}"
    ((PASSED_CHECKS++))
else
    echo -e "${RED}❌ FAIL: Build failed${NC}"
    echo -e "   Last 20 lines of build output:"
    tail -20 /tmp/verify_build.log | sed 's/^/   /'
    ((FAILED_CHECKS++))
fi
echo ""

# Check 3: Run all tests
echo -e "${BLUE}3. Running all tests...${NC}"
cd "$BUILD_DIR"
TEST_OUTPUT=$(ctest --output-on-failure 2>&1)
TEST_SUMMARY=$(echo "$TEST_OUTPUT" | grep "tests passed" || echo "No summary found")

if echo "$TEST_OUTPUT" | grep -q "100% tests passed"; then
    echo -e "${GREEN}✓ PASS: All tests passing${NC}"
    echo -e "   $TEST_SUMMARY"
    ((PASSED_CHECKS++))
else
    echo -e "${RED}❌ FAIL: Some tests failing${NC}"
    echo -e "   $TEST_SUMMARY"

    # Show which tests failed
    FAILED_TESTS=$(echo "$TEST_OUTPUT" | grep "FAILED:" | sed 's/^/   /')
    if [ ! -z "$FAILED_TESTS" ]; then
        echo -e "\n   Failed tests:"
        echo "$FAILED_TESTS"
    fi
    ((FAILED_CHECKS++))
fi
echo ""

# Check 4: Disabled tests
echo -e "${BLUE}4. Checking for disabled tests...${NC}"
DISABLED_COUNT=$(grep -r "DISABLED_" "$PROJECT_ROOT/tests" --include="*.cpp" 2>/dev/null | wc -l | tr -d ' ')

if [ $DISABLED_COUNT -eq 0 ]; then
    echo -e "${GREEN}✓ PASS: No disabled tests${NC}"
    ((PASSED_CHECKS++))
else
    echo -e "${YELLOW}⚠️  WARNING: $DISABLED_COUNT disabled tests found${NC}"
    echo -e "   Breakdown by file:"
    grep -r "DISABLED_" "$PROJECT_ROOT/tests" --include="*.cpp" 2>/dev/null | cut -d: -f1 | sort | uniq -c | sed 's/^/   /'
    ((FAILED_CHECKS++))
fi
echo ""

# Check 5: CMakeLists.txt TODOs
echo -e "${BLUE}5. Checking CMakeLists.txt for HandlerContext TODOs...${NC}"
CMAKE_TODOS=$(grep -i "# TODO.*HandlerContext" "$PROJECT_ROOT/CMakeLists.txt" 2>/dev/null | wc -l | tr -d ' ')

if [ $CMAKE_TODOS -eq 0 ]; then
    echo -e "${GREEN}✓ PASS: No HandlerContext TODOs in CMakeLists.txt${NC}"
    ((PASSED_CHECKS++))
else
    echo -e "${YELLOW}⚠️  WARNING: $CMAKE_TODOS HandlerContext TODOs in CMakeLists.txt${NC}"
    grep -i "# TODO.*HandlerContext" "$PROJECT_ROOT/CMakeLists.txt" 2>/dev/null | sed 's/^/   /'
    ((FAILED_CHECKS++))
fi
echo ""

# Check 6: Commented-out test targets
echo -e "${BLUE}6. Checking for commented-out test targets...${NC}"
COMMENTED_TESTS=$(grep "^[[:space:]]*#[[:space:]]*add_executable.*Test" "$PROJECT_ROOT/CMakeLists.txt" 2>/dev/null | wc -l | tr -d ' ')

if [ $COMMENTED_TESTS -eq 0 ]; then
    echo -e "${GREEN}✓ PASS: No commented-out test targets${NC}"
    ((PASSED_CHECKS++))
else
    echo -e "${YELLOW}⚠️  WARNING: $COMMENTED_TESTS commented-out test targets found${NC}"
    echo -e "   (This may be intentional for deprecated tests)"
    ((FAILED_CHECKS++))
fi
echo ""

# Check 7: Test counts verification
echo -e "${BLUE}7. Verifying test counts...${NC}"
cd "$BUILD_DIR"
TOTAL_TESTS=$(ctest -N 2>&1 | grep "Total Tests:" | awk '{print $3}')
E2E_TESTS=$(ctest -N -R "E2E" 2>&1 | grep -c "Test.*#" || echo "0")

echo -e "   Total tests registered: ${TOTAL_TESTS}"
echo -e "   E2E test cases: ${E2E_TESTS}"

if [ $TOTAL_TESTS -gt 0 ]; then
    echo -e "${GREEN}✓ PASS: Tests are registered and counted${NC}"
    ((PASSED_CHECKS++))
else
    echo -e "${RED}❌ FAIL: No tests found${NC}"
    ((FAILED_CHECKS++))
fi
echo ""

# Summary
echo -e "${BLUE}=== VERIFICATION SUMMARY ===${NC}\n"
echo -e "Total checks: $TOTAL_CHECKS"
echo -e "${GREEN}Passed: $PASSED_CHECKS${NC}"
echo -e "${RED}Failed: $FAILED_CHECKS${NC}"

PASS_PERCENTAGE=$((PASSED_CHECKS * 100 / TOTAL_CHECKS))
echo -e "\nPass rate: ${PASS_PERCENTAGE}%"

if [ $FAILED_CHECKS -eq 0 ]; then
    echo -e "\n${GREEN}✅ ALL CHECKS PASSED - HandlerContext retirement is COMPLETE${NC}\n"
    exit 0
else
    echo -e "\n${RED}❌ VERIFICATION FAILED - HandlerContext retirement is INCOMPLETE${NC}"
    echo -e "\nSee ${PROJECT_ROOT}/HANDLERCONTEXT_RETIREMENT_VERIFICATION.md for detailed analysis.\n"
    exit 1
fi
