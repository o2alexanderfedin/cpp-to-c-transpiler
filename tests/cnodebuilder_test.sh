#!/bin/bash
# Test script for CNodeBuilder unit tests
# Compiles and runs CNodeBuilderTest.cpp

set -e

echo "=== CNodeBuilder Unit Test ==="

# Get LLVM config paths
LLVM_CONFIG="/opt/homebrew/opt/llvm/bin/llvm-config"
LLVM_CXXFLAGS=$($LLVM_CONFIG --cxxflags)
LLVM_LDFLAGS=$($LLVM_CONFIG --ldflags)
LLVM_LIBS=$($LLVM_CONFIG --libs core support)

# Add Clang libraries
CLANG_LIBS="-lclangTooling -lclangFrontend -lclangAST -lclangBasic"

# Compile test (disable exceptions to match LLVM's build)
echo "Compiling CNodeBuilderTest..."
clang++ -std=c++17 \
    $LLVM_CXXFLAGS \
    -fno-exceptions \
    -I../include \
    -o cnodebuilder_test \
    CNodeBuilderTest.cpp \
    $LLVM_LDFLAGS \
    $CLANG_LIBS \
    $LLVM_LIBS

# Run test
echo "Running CNodeBuilderTest..."
./cnodebuilder_test

if [ $? -eq 0 ]; then
    echo "✓ All CNodeBuilder tests passed!"
else
    echo "✗ CNodeBuilder tests failed!"
    exit 1
fi
