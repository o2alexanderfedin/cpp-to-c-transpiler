#!/bin/bash

# Simple Real-World Validation Script
# Tests all 5 STL-free projects (C++ original and transpiled C)

set -e  # Exit on error disabled to allow collecting all results
cd "$(dirname "$0")"

PASS=0
FAIL=0
RESULTS_FILE="validation_results.txt"

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo "========================================" | tee "$RESULTS_FILE"
echo "Simple Real-World Validation (STL-Free)" | tee -a "$RESULTS_FILE"
echo "========================================" | tee -a "$RESULTS_FILE"
echo "" | tee -a "$RESULTS_FILE"

test_project() {
    local project_dir=$1
    local project_name=$2

    echo -e "${YELLOW}Testing $project_name...${NC}" | tee -a "$RESULTS_FILE"
    cd "$project_dir"

    # Phase 1: Test C++ original
    echo "  [1/5] Building C++ version..." | tee -a "../$RESULTS_FILE"
    mkdir -p build
    cd build
    if cmake .. >> "../../$RESULTS_FILE" 2>&1 && make >> "../../$RESULTS_FILE" 2>&1; then
        echo "    ✓ C++ build successful" | tee -a "../../$RESULTS_FILE"
    else
        echo -e "    ${RED}✗ C++ build failed${NC}" | tee -a "../../$RESULTS_FILE"
        cd ../..
        return 1
    fi

    # Phase 2: Run C++ executable
    echo "  [2/5] Running C++ version..." | tee -a "../../$RESULTS_FILE"
    # Find executable by known naming pattern
    local cpp_exe=""
    if [ -f "./math_library" ]; then cpp_exe="./math_library"
    elif [ -f "./custom_container" ]; then cpp_exe="./custom_container"
    elif [ -f "./state_machine" ]; then cpp_exe="./state_machine"
    elif [ -f "./simple_parser" ]; then cpp_exe="./simple_parser"
    elif [ -f "./game_logic" ]; then cpp_exe="./game_logic"
    fi

    if [ -z "$cpp_exe" ]; then
        echo -e "    ${RED}✗ No C++ executable found${NC}" | tee -a "../../$RESULTS_FILE"
        cd ../..
        return 1
    fi

    if $cpp_exe >> "../../$RESULTS_FILE" 2>&1; then
        local cpp_exit=$?
        if [ $cpp_exit -eq 0 ]; then
            echo "    ✓ C++ execution successful (exit code: 0)" | tee -a "../../$RESULTS_FILE"
        else
            echo -e "    ${RED}✗ C++ execution failed (exit code: $cpp_exit)${NC}" | tee -a "../../$RESULTS_FILE"
            cd ../..
            return 1
        fi
    else
        echo -e "    ${RED}✗ C++ execution failed${NC}" | tee -a "../../$RESULTS_FILE"
        cd ../..
        return 1
    fi
    cd ..

    # Phase 3: Transpile to C
    echo "  [3/5] Transpiling to C..." | tee -a "../$RESULTS_FILE"
    rm -rf transpiled
    mkdir -p transpiled

    # Use absolute path to transpiler
    # Phase 34's transpiler requires --source-dir and auto-discovers files
    local transpiler="/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build_working/cpptoc"
    local project_root=$(pwd)

    # Check for per-project configuration
    local extra_args=""
    if [ -f ".cpptoc.json" ]; then
        # Extract transpiler_args from JSON (simple grep-based parsing)
        # Match both "--extra-arg=..." and "--extra-arg=-isystem..." formats
        local config_args=$(grep -A 20 '"transpiler_args"' .cpptoc.json | grep -E '"\-\-extra-arg=' | sed 's/.*"\(--extra-arg=[^"]*\)".*/\1/' | tr '\n' ' ')
        if [ -n "$config_args" ]; then
            extra_args="$config_args"
            echo "    [Config] Using project-specific args" | tee -a "../$RESULTS_FILE"
        fi
    fi

    if $transpiler --source-dir "$project_root" --output-dir transpiled/ $extra_args >> "../$RESULTS_FILE" 2>&1; then
        echo "    ✓ Transpilation successful" | tee -a "../$RESULTS_FILE"
    else
        echo -e "    ${RED}✗ Transpilation failed${NC}" | tee -a "../$RESULTS_FILE"
        cd ..
        return 1
    fi

    # Phase 4: Build transpiled C code
    echo "  [4/5] Building transpiled C version..." | tee -a "../$RESULTS_FILE"
    cd transpiled

    # Find all .c files
    local c_files=$(find . -name "*.c" 2>/dev/null)
    if [ -z "$c_files" ]; then
        echo -e "    ${RED}✗ No C files generated${NC}" | tee -a "../../$RESULTS_FILE"
        cd ../..
        return 1
    fi

    if gcc -I . $c_files -o test_c -lm >> "../../$RESULTS_FILE" 2>&1; then
        echo "    ✓ C build successful" | tee -a "../../$RESULTS_FILE"
    else
        echo -e "    ${RED}✗ C build failed${NC}" | tee -a "../../$RESULTS_FILE"
        cd ../..
        return 1
    fi

    # Phase 5: Run transpiled C executable
    echo "  [5/5] Running transpiled C version..." | tee -a "../../$RESULTS_FILE"
    if ./test_c >> "../../$RESULTS_FILE" 2>&1; then
        local c_exit=$?
        if [ $c_exit -eq 0 ]; then
            echo "    ✓ C execution successful (exit code: 0)" | tee -a "../../$RESULTS_FILE"
        else
            echo -e "    ${RED}✗ C execution failed (exit code: $c_exit)${NC}" | tee -a "../../$RESULTS_FILE"
            cd ../..
            return 1
        fi
    else
        echo -e "    ${RED}✗ C execution failed${NC}" | tee -a "../../$RESULTS_FILE"
        cd ../..
        return 1
    fi

    cd ../..
    return 0
}

# Test all projects
projects=(
    "01-math-library:Math Library"
    "02-custom-container:Custom Container"
    "03-state-machine:State Machine"
    "04-simple-parser:Simple Parser"
    "05-game-logic:Game Logic"
)

for project in "${projects[@]}"; do
    IFS=':' read -r dir name <<< "$project"

    if test_project "$dir" "$name"; then
        echo -e "${GREEN}✅ PASS: $name${NC}" | tee -a "$RESULTS_FILE"
        PASS=$((PASS+1))
    else
        echo -e "${RED}❌ FAIL: $name${NC}" | tee -a "$RESULTS_FILE"
        FAIL=$((FAIL+1))
    fi
    echo "" | tee -a "$RESULTS_FILE"
done

# Summary
echo "========================================" | tee -a "$RESULTS_FILE"
echo "SUMMARY" | tee -a "$RESULTS_FILE"
echo "========================================" | tee -a "$RESULTS_FILE"
echo "Total:  5 projects" | tee -a "$RESULTS_FILE"
echo "Passed: $PASS" | tee -a "$RESULTS_FILE"
echo "Failed: $FAIL" | tee -a "$RESULTS_FILE"
PERCENT=$((PASS * 100 / 5))
echo "Pass Rate: $PASS/5 ($PERCENT%)" | tee -a "$RESULTS_FILE"
echo "" | tee -a "$RESULTS_FILE"

if [ $PASS -ge 4 ]; then
    echo -e "${GREEN}✅ SUCCESS: 80%+ pass rate achieved ($PERCENT%)${NC}" | tee -a "$RESULTS_FILE"
    exit 0
else
    echo -e "${RED}❌ FAIL: Less than 80% pass rate ($PERCENT%)${NC}" | tee -a "$RESULTS_FILE"
    exit 1
fi
