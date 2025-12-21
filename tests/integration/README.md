# ACSL Integration Tests

This directory contains integration tests for ACSL annotation generation.

## Test Organization

### basic/
Basic ACSL annotation tests:
- Function contracts (requires, ensures, assigns)
- Simple loop invariants
- Basic class invariants

### advanced/
Advanced ACSL features:
- Behaviors (multiple execution paths)
- Complex loop invariants with quantifiers
- Type invariants
- Axiomatic definitions (when implemented)
- Ghost code (when implemented)

### edge_cases/
Edge case handling:
- Null pointer handling
- Empty arrays
- Boundary conditions
- Error paths

## Running Tests

```bash
# Run all integration tests
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c
./run_integration_tests.sh

# Run specific test category
./run_integration_tests.sh basic
./run_integration_tests.sh advanced
./run_integration_tests.sh edge_cases
```

## Test Structure

Each test consists of:
1. **Input**: C++ source file (*.cpp)
2. **Expected**: Expected ACSL output (*.acsl)
3. **Verification**: Script to compare actual vs expected output

## Current Status

Phase 1 (Pipeline Integration) - ✅ COMPLETED
- All 9 ACSL annotator classes wired into CppToCVisitor
- Basic compilation and execution verified
- Manual testing with test_acsl.cpp successful

Phase 2 (Integration Testing) - 🚧 IN PROGRESS
- Test structure created
- Basic tests to be implemented
