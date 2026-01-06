# GCC C++23 Test Suite for Phase 33.1

## Overview

This directory contains **130 selected C++23 test cases** extracted from the official GCC test suite to validate the C++ to C transpiler's C++23 compliance.

## Source Information

- **Repository**: [GCC Mirror](https://github.com/gcc-mirror/gcc)
- **Commit Hash**: `3735bbb7d918e88cac9818b477121cf03558a7cc`
- **Commit Date**: 2025-12-21 20:10:14 +0800
- **Commit Message**: RISC-V: Add test for vec_duplicate + vmsleu.vv combine with GR2VR cost 0, 1 and 15
- **Source Directory**: `gcc/testsuite/g++.dg/cpp23/`
- **Extraction Date**: 2025-12-24 21:06:13 UTC

## Test Organization

Tests are organized by C++23 feature (P-numbers indicate ISO C++ proposals):

### 1. if-consteval-P1938 (13 tests)
- **Feature**: Conditional evaluation with `if consteval`
- **Proposal**: P1938R0 - "If consteval blocks"
- **Purpose**: Tests for compile-time conditional execution
- **Tests**: `consteval-if{1..13}.C`

### 2. multidim-subscript-P2128 (16 tests)
- **Feature**: Multidimensional subscript operator
- **Proposal**: P2128R6 - "Multidimensional subscript operator"
- **Purpose**: Tests for `operator[]` with multiple parameters
- **Tests**: `subscript{1..12}.C`, `explicit-obj-ops-mem-subscript.C`, etc.

### 3. static-operators-P1169 (8 tests)
- **Feature**: Static operator overloads
- **Proposal**: P1169R4 - "Static operator()"
- **Purpose**: Tests for static operator functions (especially `operator()`)
- **Tests**: `static-operator-call{1..8}.C`

### 4. auto-deduction-P0849 (22 tests)
- **Feature**: Deduced type with `auto(x)` and `auto{x}`
- **Proposal**: P0849R8 - "auto(x): decay copy in the language"
- **Purpose**: Tests for explicit deduced type declarations
- **Tests**: `auto-array{1..4}.C`, `auto-fncast{1..18}.C`

### 5. constexpr-enhancements (19 tests)
- **Features**: Various constexpr improvements (P1938, P1900, etc.)
- **Purpose**: Tests for constexpr-specific capabilities
- **Tests**: `constexpr-nonlit{1..19}.C`

### 6. class-template-deduction-inherited (10 tests)
- **Feature**: Class template argument deduction with inheritance
- **Purpose**: Tests for CTAD with inherited constructors
- **Tests**: `class-deduction-inherited{1..10}.C`

### 7. attributes-P2180 (13 tests)
- **Feature**: `[[assume]]` attribute
- **Proposal**: P2180R1 - "Language support for assuming expressions are true"
- **Purpose**: Tests for compile-time assertions and optimizations
- **Tests**: `attr-assume{1,opt}.C`, `attr-assume{1..12}.C`

### 8. ranges-P2678 (10 tests)
- **Feature**: Range-based for loop improvements
- **Purpose**: Tests for modern range-based iteration
- **Tests**: `range-for{1..10}.C`

### 9. miscellaneous (19 tests)
- **Features**: Various other C++23 features
- **Purpose**: Extended coverage of additional C++23 capabilities
- **Tests**: Additional test files covering:
  - Character literal encoding
  - Charset handling
  - Various language extensions

## Total:      130 tests

## Usage for Phase 33.1

These tests validate:
1. **Syntax Parsing**: C++23 syntax features can be parsed correctly
2. **Semantic Analysis**: C++23 semantic rules are properly handled
3. **Code Generation**: Valid C code can be emitted for C++23 constructs

## Integration with Transpiler

The tests in this directory should be:

1. **Analyzed** to understand C++23 features
2. **Translated** by the C++ to C transpiler
3. **Validated** to ensure generated C code is correct
4. **Tracked** in transpilation success metrics

## Notes

- Tests are `.C` files (C++ extension used by GCC)
- Some tests may require C++23 compilation flags (`-std=c++23`)
- Tests are self-contained and independent
- Source comments in each test file explain the feature being tested

## Phase 33.1 Objectives

This test suite supports Phase 33.1 objectives:
- Validate C++23 feature support in transpiler
- Establish baseline metrics for C++23 compatibility
- Identify feature-specific translation patterns
- Document C++ to C mapping for C++23 constructs

