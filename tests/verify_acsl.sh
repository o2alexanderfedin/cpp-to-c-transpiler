#!/bin/bash
# Test script for ACSL annotation validation
# Story #185: ACSL Annotation Infrastructure for Runtime Library
#
# This script validates ACSL annotations using Frama-C parser
# Following TDD principles - this test will fail initially

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
RUNTIME_DIR="$PROJECT_ROOT/runtime"

echo "========================================="
echo "ACSL Annotation Validation Test"
echo "========================================="
echo ""

# Test 1: Verify exception_runtime.h has valid ACSL
echo "[Test 1] Validating exception_runtime.h ACSL annotations..."
if frama-c -cpp-extra-args="-I$RUNTIME_DIR" "$RUNTIME_DIR/exception_runtime.h" > /dev/null 2>&1; then
    echo "✓ exception_runtime.h: ACSL syntax valid"
else
    echo "✗ exception_runtime.h: ACSL syntax errors detected"
    frama-c -cpp-extra-args="-I$RUNTIME_DIR" "$RUNTIME_DIR/exception_runtime.h" 2>&1 | grep -i "error\|warning" || true
    exit 1
fi

# Test 2: Verify rtti_runtime.h has valid ACSL
echo "[Test 2] Validating rtti_runtime.h ACSL annotations..."
if frama-c -cpp-extra-args="-I$RUNTIME_DIR" "$RUNTIME_DIR/rtti_runtime.h" > /dev/null 2>&1; then
    echo "✓ rtti_runtime.h: ACSL syntax valid"
else
    echo "✗ rtti_runtime.h: ACSL syntax errors detected"
    frama-c -cpp-extra-args="-I$RUNTIME_DIR" "$RUNTIME_DIR/rtti_runtime.h" 2>&1 | grep -i "error\|warning" || true
    exit 1
fi

# Test 3: Verify rtti_runtime.c has valid ACSL
echo "[Test 3] Validating rtti_runtime.c ACSL annotations..."
if frama-c -cpp-extra-args="-I$RUNTIME_DIR" "$RUNTIME_DIR/rtti_runtime.c" > /dev/null 2>&1; then
    echo "✓ rtti_runtime.c: ACSL syntax valid"
else
    echo "✗ rtti_runtime.c: ACSL syntax errors detected"
    frama-c -cpp-extra-args="-I$RUNTIME_DIR" "$RUNTIME_DIR/rtti_runtime.c" 2>&1 | grep -i "error\|warning" || true
    exit 1
fi

echo ""
echo "========================================="
echo "All ACSL validation tests passed!"
echo "========================================="
