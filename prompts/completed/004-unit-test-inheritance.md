<objective>
Create comprehensive unit tests for multiple inheritance and virtual inheritance handlers, ensuring each component is thoroughly tested in isolation.

Unit tests verify that individual handler components work correctly without requiring the full transpilation pipeline. This enables faster development cycles and easier debugging.
</objective>

<context>
Read the audit report for context on what needs testing:
@./audit-reports/inheritance-handlers-audit.md

Read project architecture:
@CLAUDE.md

The transpiler follows TDD practices with 100% test pass rate requirement. Current test count: 41/41 passing.

Unit test patterns to follow:
- Examine existing handler tests in `tests/unit/handlers/` and `tests/unit/dispatch/`
- Use GTest framework (see tests ending in `_GTest.cpp`)
- Test files use pattern: `[Component]Test.cpp` or `[Component]Test_GTest.cpp`
- Each test should be focused, independent, and fast
</context>

<requirements>
Create unit tests for all inheritance-related handler components identified in the audit. Tests should cover:

1. **Virtual Inheritance Detection**:
   - Correctly identifies virtual base classes
   - Distinguishes virtual from non-virtual bases
   - Handles complex hierarchies (diamond pattern)

2. **Inheritance Graph Analysis**:
   - Builds correct inheritance graph
   - Finds all paths from derived to base
   - Detects diamond patterns
   - Computes correct base offsets

3. **VTable Generation for Virtual Inheritance**:
   - Generates vtables with virtual base offsets
   - Creates VTT (Virtual Table Table) for construction
   - Handles multiple virtual bases
   - Coordinates with existing virtual method vtables

4. **Handler Dispatch**:
   - Handler predicates match correctly
   - Handlers are registered in dispatch system
   - No handler conflicts or duplicates
   - Proper handler priority ordering

5. **C AST Node Creation**:
   - Handlers create correct C AST nodes (not text)
   - Struct definitions have correct layout
   - Offset calculations are accurate
   - Type information is preserved

6. **Edge Cases**:
   - Empty virtual base classes
   - Deep inheritance hierarchies
   - Multiple paths to same virtual base
   - Mix of virtual and non-virtual inheritance
</requirements>

<test_structure>
For each component, create tests following this pattern:

```cpp
// File: tests/unit/handlers/VirtualInheritanceHandlerTest.cpp

#include <gtest/gtest.h>
#include "VirtualInheritanceHandler.h"
#include "TestHelpers.h"

class VirtualInheritanceHandlerTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Setup test fixtures
    }
};

TEST_F(VirtualInheritanceHandlerTest, DetectsSingleVirtualBase) {
    // Arrange: Create C++ AST with virtual base
    // Act: Run handler
    // Assert: Verify correct detection
}

TEST_F(VirtualInheritanceHandlerTest, HandlesDiamondInheritance) {
    // Test diamond pattern
}

TEST_F(VirtualInheritanceHandlerTest, GeneratesCorrectOffsets) {
    // Test offset calculation
}

// ... more tests
```

Use the AAA (Arrange-Act-Assert) pattern consistently.
</test_structure>

<implementation>
1. **Identify test gaps** from audit report:
   - List all components that need unit tests
   - Prioritize by importance (critical handlers first)

2. **Create test files**:
   - Follow naming convention: `[Component]Test.cpp` or `[Component]Test_GTest.cpp`
   - Place in appropriate directory (`tests/unit/handlers/` or `tests/unit/dispatch/`)
   - Add to CMakeLists.txt for build system

3. **Write focused tests**:
   - Each test should verify ONE behavior
   - Use descriptive test names (e.g., `HandlesMultipleVirtualBasesCorrectly`)
   - Include edge cases and error conditions
   - Test both success and failure paths

4. **Ensure tests are independent**:
   - No shared state between tests
   - Each test can run in isolation
   - Tests can run in any order

5. **Follow existing patterns**:
   - Study existing unit tests for reference
   - Use the same test helpers and utilities
   - Match the assertion style and structure

For maximum efficiency, create multiple test files in parallel if they test independent components.
</implementation>

<output>
Create unit test files in the appropriate directories:

Likely files to create (based on typical inheritance handler structure):
- `tests/unit/handlers/VirtualInheritanceHandlerTest.cpp`
- `tests/unit/VirtualBaseOffsetCalculatorTest.cpp`
- `tests/unit/VTTGeneratorTest.cpp` (may already exist - enhance if needed)
- `tests/unit/dispatch/VirtualInheritanceHandlerDispatcherTest.cpp`

Update:
- `tests/CMakeLists.txt` - Add new test executables
- `.github/workflows/ci.yml` - Add tests to CI (if not auto-discovered)
- `scripts/test-cicd-local-parity.sh` - Add tests to local parity script
</output>

<verification>
After creating unit tests:

1. **Build and run tests**:
   ```bash
   cmake --build build
   ./scripts/test-cicd-local-parity.sh
   ```

2. **Verify test quality**:
   - Each test has clear arrange-act-assert structure
   - Test names describe what's being tested
   - All assertions are meaningful and specific

3. **Check coverage**:
   - All public methods of handlers are tested
   - All edge cases from requirements are covered
   - Both success and failure paths are tested

4. **Verify independence**:
   - Run tests multiple times - should always pass
   - Run tests in different orders - results should be consistent

5. **Performance check**:
   - Unit tests should be fast (< 1 second each typically)
   - No unnecessary file I/O or external dependencies
</verification>

<success_criteria>
Unit testing is complete when:

- ✅ All handler components identified in audit have unit tests
- ✅ Each component has tests for normal cases, edge cases, and error conditions
- ✅ Tests follow established patterns and naming conventions
- ✅ All tests pass independently and in any order
- ✅ Tests are added to build system and CI
- ✅ Test coverage is comprehensive (all public methods, all branches)
- ✅ Tests run fast (unit test suite completes in seconds)
- ✅ No test flakiness (100% consistent results)
</success_criteria>
