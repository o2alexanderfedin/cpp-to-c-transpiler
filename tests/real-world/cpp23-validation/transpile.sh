#!/bin/bash
# C++23 to C99 Transpilation Script
# Transpiles all C++23 source files to C99

set -e  # Exit on error

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m' # No Color

echo -e "${GREEN}==================================================${NC}"
echo -e "${GREEN}  C++23 to C99 Transpilation${NC}"
echo -e "${GREEN}==================================================${NC}"

# Paths
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
CPP_SRC_DIR="$SCRIPT_DIR/cpp/src"
CPP_INCLUDE_DIR="$SCRIPT_DIR/cpp/include"
OUTPUT_DIR="$SCRIPT_DIR/transpiled"
TRANSPILER="/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build_working_new/cpptoc"

# Clean output directory
echo -e "${YELLOW}Cleaning output directory...${NC}"
rm -rf "$OUTPUT_DIR"
mkdir -p "$OUTPUT_DIR"

# Check transpiler exists
if [ ! -f "$TRANSPILER" ]; then
    echo -e "${RED}Error: Transpiler not found at $TRANSPILER${NC}"
    echo -e "${YELLOW}Building transpiler...${NC}"
    cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c
    mkdir -p build_working_new
    cd build_working_new
    cmake .. -DCMAKE_BUILD_TYPE=Release
    make cpptoc -j8
    cd "$SCRIPT_DIR"
fi

# Create a temporary project directory with all sources
TEMP_PROJECT="$SCRIPT_DIR/temp_project"
rm -rf "$TEMP_PROJECT"
mkdir -p "$TEMP_PROJECT"

# Copy all source files to temp project
echo -e "${YELLOW}Preparing source files...${NC}"
cp -r "$CPP_SRC_DIR"/* "$TEMP_PROJECT/"
cp -r "$CPP_INCLUDE_DIR"/* "$TEMP_PROJECT/"

# List files to be transpiled
echo -e "${YELLOW}Files to transpile:${NC}"
find "$TEMP_PROJECT" -name "*.cpp" -o -name "*.hpp" | sort

# Run transpiler
echo -e "${YELLOW}Running transpiler...${NC}"
"$TRANSPILER" \
    --source-dir="$TEMP_PROJECT" \
    --output-dir="$OUTPUT_DIR" \
    --enable-exceptions \
    --enable-rtti \
    --template-monomorphization \
    2>&1 | tee "$SCRIPT_DIR/transpilation.log"

# Check if transpilation succeeded
if [ $? -eq 0 ]; then
    echo -e "${GREEN}Transpilation successful!${NC}"
else
    echo -e "${RED}Transpilation failed! Check transpilation.log for details.${NC}"
    rm -rf "$TEMP_PROJECT"
    exit 1
fi

# Clean up temp project
rm -rf "$TEMP_PROJECT"

# Organize output
echo -e "${YELLOW}Organizing output files...${NC}"
mkdir -p "$OUTPUT_DIR/src" "$OUTPUT_DIR/include"

# Move .c files to src/ and .h files to include/
find "$OUTPUT_DIR" -maxdepth 1 -name "*.c" -exec mv {} "$OUTPUT_DIR/src/" \;
find "$OUTPUT_DIR" -maxdepth 1 -name "*.h" -exec mv {} "$OUTPUT_DIR/include/" \;

# List generated files
echo -e "${YELLOW}Generated files:${NC}"
echo -e "${YELLOW}Headers (.h):${NC}"
ls -lh "$OUTPUT_DIR/include/" 2>/dev/null || echo "  (none)"
echo -e "${YELLOW}Sources (.c):${NC}"
ls -lh "$OUTPUT_DIR/src/" 2>/dev/null || echo "  (none)"

# Count lines of code
echo -e "${YELLOW}Lines of code:${NC}"
echo -n "  C headers: "
find "$OUTPUT_DIR/include" -name "*.h" -exec wc -l {} + 2>/dev/null | tail -1 | awk '{print $1}' || echo "0"
echo -n "  C source: "
find "$OUTPUT_DIR/src" -name "*.c" -exec wc -l {} + 2>/dev/null | tail -1 | awk '{print $1}' || echo "0"

echo -e "${GREEN}==================================================${NC}"
echo -e "${GREEN}  Transpilation complete!${NC}"
echo -e "${GREEN}==================================================${NC}"
