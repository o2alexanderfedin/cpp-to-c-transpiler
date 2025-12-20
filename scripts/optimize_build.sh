#!/bin/bash
#
# optimize_build.sh
#
# Story #119: Implement Size Optimization with LTO/PGO Support
# Epic #16: Runtime Optimization & Configuration
#
# Build script for size-optimized binaries
#
# Usage:
#   ./scripts/optimize_build.sh [optimization_level]
#
# Optimization levels:
#   baseline    - No optimizations (-O0)
#   size        - Optimize for size (-Os)
#   size_lto    - Size + LTO (-Os -flto)
#   full        - Size + LTO + dead code elimination (default)
#   pgo_gen     - Generate PGO profile data
#   pgo_use     - Use PGO profile data
#
# Examples:
#   ./scripts/optimize_build.sh baseline
#   ./scripts/optimize_build.sh full
#   ./scripts/optimize_build.sh pgo_gen

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

# Default optimization level
OPT_LEVEL="${1:-full}"

# Build directory
BUILD_DIR="build"
PROFILE_DIR="pgo_profiles"

echo "=========================================="
echo "Size Optimization Build Script"
echo "Story #119: LTO/PGO Support"
echo "=========================================="
echo ""

# Function to print colored messages
print_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

print_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Function to measure binary size
measure_size() {
    local binary="$1"
    if [ -f "$binary" ]; then
        local size=$(stat -f%z "$binary" 2>/dev/null || stat -c%s "$binary" 2>/dev/null)
        local size_kb=$((size / 1024))
        echo "${size_kb} KB (${size} bytes)"
    else
        echo "N/A"
    fi
}

# Create build directory
mkdir -p "$BUILD_DIR"
cd "$BUILD_DIR"

# Configure based on optimization level
print_info "Optimization level: $OPT_LEVEL"
echo ""

case "$OPT_LEVEL" in
    baseline)
        print_info "Building with baseline configuration (no optimizations)"
        cmake -DCMAKE_C_FLAGS="-O0" \
              -DCMAKE_CXX_FLAGS="-O0" \
              -DCMAKE_PREFIX_PATH=/opt/homebrew/opt/llvm \
              ..
        ;;

    size)
        print_info "Building with size optimization (-Os)"
        cmake -DCMAKE_C_FLAGS="-Os" \
              -DCMAKE_CXX_FLAGS="-Os" \
              -DCMAKE_PREFIX_PATH=/opt/homebrew/opt/llvm \
              ..
        ;;

    size_lto)
        print_info "Building with size optimization + LTO (-Os -flto)"
        cmake -DCMAKE_C_FLAGS="-Os -flto" \
              -DCMAKE_CXX_FLAGS="-Os -flto" \
              -DCMAKE_EXE_LINKER_FLAGS="-flto" \
              -DCMAKE_INTERPROCEDURAL_OPTIMIZATION=TRUE \
              -DCMAKE_PREFIX_PATH=/opt/homebrew/opt/llvm \
              ..
        ;;

    full)
        print_info "Building with full optimization (-Os -flto -ffunction-sections -fdata-sections --gc-sections)"
        cmake -DCMAKE_C_FLAGS="-Os -flto -ffunction-sections -fdata-sections" \
              -DCMAKE_CXX_FLAGS="-Os -flto -ffunction-sections -fdata-sections" \
              -DCMAKE_EXE_LINKER_FLAGS="-flto -Wl,--gc-sections" \
              -DCMAKE_INTERPROCEDURAL_OPTIMIZATION=TRUE \
              -DCMAKE_PREFIX_PATH=/opt/homebrew/opt/llvm \
              ..
        ;;

    pgo_gen)
        print_info "Building with PGO profile generation (-fprofile-generate)"
        mkdir -p "../$PROFILE_DIR"
        cmake -DCMAKE_C_FLAGS="-Os -fprofile-generate=../$PROFILE_DIR" \
              -DCMAKE_CXX_FLAGS="-Os -fprofile-generate=../$PROFILE_DIR" \
              -DCMAKE_EXE_LINKER_FLAGS="-fprofile-generate=../$PROFILE_DIR" \
              -DCMAKE_PREFIX_PATH=/opt/homebrew/opt/llvm \
              ..
        print_warn "After building, run your program with typical workload to generate profile data"
        print_warn "Then rebuild with: ./scripts/optimize_build.sh pgo_use"
        ;;

    pgo_use)
        if [ ! -d "../$PROFILE_DIR" ]; then
            print_error "Profile directory not found. Run 'pgo_gen' first."
            exit 1
        fi
        print_info "Building with PGO profile usage (-fprofile-use)"
        cmake -DCMAKE_C_FLAGS="-Os -fprofile-use=../$PROFILE_DIR" \
              -DCMAKE_CXX_FLAGS="-Os -fprofile-use=../$PROFILE_DIR" \
              -DCMAKE_EXE_LINKER_FLAGS="-fprofile-use=../$PROFILE_DIR" \
              -DCMAKE_PREFIX_PATH=/opt/homebrew/opt/llvm \
              ..
        ;;

    *)
        print_error "Unknown optimization level: $OPT_LEVEL"
        echo ""
        echo "Valid levels: baseline, size, size_lto, full, pgo_gen, pgo_use"
        exit 1
        ;;
esac

echo ""
print_info "Building project..."
make -j$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4)

echo ""
print_info "Build complete!"
echo ""

# Measure sizes of key binaries
print_info "Binary sizes:"
echo "  cpptoc:                  $(measure_size cpptoc)"
echo "  SizeOptimizationTest:    $(measure_size SizeOptimizationTest)"
echo "  Runtime library:         $(measure_size runtime/libcpptoc_runtime.a)"
echo ""

# Return to original directory
cd ..

# Generate size comparison report
if [ "$OPT_LEVEL" = "full" ]; then
    print_info "Generating size comparison report..."

    # Build baseline for comparison
    print_info "Building baseline for comparison..."
    mkdir -p build_baseline
    cd build_baseline
    cmake -DCMAKE_C_FLAGS="-O0" \
          -DCMAKE_CXX_FLAGS="-O0" \
          -DCMAKE_PREFIX_PATH=/opt/homebrew/opt/llvm \
          .. > /dev/null 2>&1
    make cpptoc -j$(nproc 2>/dev/null || sysctl -n hw.ncpu 2>/dev/null || echo 4) > /dev/null 2>&1

    baseline_size=$(stat -f%z cpptoc 2>/dev/null || stat -c%s cpptoc 2>/dev/null)
    optimized_size=$(stat -f%z ../build/cpptoc 2>/dev/null || stat -c%s ../build/cpptoc 2>/dev/null)

    reduction=$((baseline_size - optimized_size))
    reduction_percent=$((reduction * 100 / baseline_size))

    cd ..

    echo ""
    echo "=========================================="
    echo "Size Reduction Report"
    echo "=========================================="
    echo "  Baseline size:     $((baseline_size / 1024)) KB"
    echo "  Optimized size:    $((optimized_size / 1024)) KB"
    echo "  Reduction:         $((reduction / 1024)) KB ($reduction_percent%)"
    echo "  Target:            35-45% reduction"
    if [ $reduction_percent -ge 35 ] && [ $reduction_percent -le 45 ]; then
        echo -e "  ${GREEN}✓ Target achieved!${NC}"
    elif [ $reduction_percent -gt 45 ]; then
        echo -e "  ${GREEN}✓ Exceeded target!${NC}"
    else
        echo -e "  ${YELLOW}⚠ Below target${NC}"
    fi
    echo "=========================================="
    echo ""
fi

print_info "Done!"
