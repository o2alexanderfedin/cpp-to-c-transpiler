<objective>
Create comprehensive integration tests for multiple inheritance and virtual inheritance, verifying that handler components work correctly together within the transpiler pipeline.

Integration tests validate that the complete handler chain produces correct C AST from C++ AST, ensuring proper coordination between:
- Inheritance analyzers
- VTable generators
- Constructor handlers
- Type translators
- Handler dispatch system

These tests catch issues that unit tests miss, such as handler interaction bugs, incorrect C AST node relationships, and pipeline integration problems.
</objective>

<context>
Read the audit report:
@./audit-reports/inheritance-handlers-audit.md

Read project architecture:
@CLAUDE.md

Integration test patterns:
- Located in `tests/integration/handlers/` or `tests/integration/`
- Test multiple handlers working together
- Verify C AST structure (not just C source output)
- Check handler coordination and data flow
- Example: `tests/integration/handlers/VirtualMethodsIntegrationTest.cpp`

The transpiler has 3 stages:
1. C++ AST (input)
2. Handler Chain → C AST (integration tests verify this stage)
3. C Source (output)

Integration tests focus on stage 2: ensuring handlers create correct C AST.
</context>

<requirements>
Create integration tests covering:

1. **Simple Virtual Inheritance**:
   - Single virtual base class
   - Verify C AST has correct struct layout
   - Check virtual base offset is calculated
   - Ensure constructor initializes virtual base

2. **Diamond Inheritance Pattern**:
   - Classic diamond: D inherits from B and C, both inherit virtually from A
   - Verify only ONE instance of virtual base A in C AST
   - Check VTT generation for construction
   - Validate offset adjustments in all constructors

3. **Multiple Virtual Bases**:
   - Class with multiple virtual base classes
   - Verify each virtual base has correct offset
   - Check VTT handles multiple virtual bases
   - Ensure proper initialization order

4. **Mixed Virtual and Non-Virtual Inheritance**:
   - Some bases virtual, some non-virtual
   - Verify correct layout in C AST
   - Check offset calculations distinguish virtual/non-virtual
   - Validate constructor coordination

5. **Deep Inheritance Hierarchies**:
   - Virtual inheritance through multiple levels
   - Verify offset propagation through hierarchy
   - Check VTT generation for complex hierarchies
   - Ensure all constructors coordinate correctly

6. **Virtual Inheritance with Virtual Methods**:
   - Combine virtual inheritance and virtual methods
   - Verify vtable and VTT are both generated
   - Check pointer adjustments for virtual calls
   - Ensure proper interaction between features

7. **Handler Coordination**:
   - VirtualInheritanceHandler + RecordHandler
   - VtableGenerator + ConstructorHandler
   - TypeTranslator + NameMangler
   - Verify no duplicate logic or conflicts
</requirements>

<test_structure>
Integration tests should:

1. **Create realistic C++ AST**:
   - Use Clang's ASTContext to build real C++ AST
   - Or use test helpers to parse C++ code snippets
   - Include complete class definitions

2. **Run handler chain**:
   - Invoke the full handler dispatch system
   - Or invoke specific handler combinations
   - Let handlers create C AST

3. **Verify C AST structure**:
   - Check C struct definitions are correct
   - Verify field layout and types
   - Validate function declarations
   - Inspect VTT and vtable structures

4. **Assert coordination**:
   - Handlers don't duplicate work
   - Data flows correctly between handlers
   - C AST nodes reference each other properly

Example test structure:
```cpp
// File: tests/integration/handlers/VirtualInheritanceIntegrationTest.cpp

#include <gtest/gtest.h>
#include "TranspilerAPI.h"
#include "TestHelpers.h"

TEST(VirtualInheritanceIntegrationTest, SimpleVirtualBase) {
    // Arrange: C++ code with virtual base
    const char* cppCode = R"(
        struct Base { int x; };
        struct Derived : virtual Base { int y; };
    )";

    // Act: Run transpiler to generate C AST
    auto result = transpileToCAST(cppCode);

    // Assert: Verify C AST structure
    ASSERT_TRUE(result.hasStruct("Base"));
    ASSERT_TRUE(result.hasStruct("Derived"));

    auto derivedStruct = result.getStruct("Derived");
    EXPECT_TRUE(derivedStruct.hasVirtualBaseOffset("Base"));
    EXPECT_EQ(derivedStruct.fieldCount(), 2); // y + vbase offset

    // Verify constructor
    auto derivedCtor = result.getFunction("Derived__init");
    EXPECT_TRUE(derivedCtor.initializesVirtualBase("Base"));
}

TEST(VirtualInheritanceIntegrationTest, DiamondPattern) {
    const char* cppCode = R"(
        struct A { int a; };
        struct B : virtual A { int b; };
        struct C : virtual A { int c; };
        struct D : B, C { int d; };
    )";

    auto result = transpileToCAST(cppCode);

    // Assert: Only ONE A instance in D
    auto dStruct = result.getStruct("D");
    EXPECT_EQ(dStruct.countBaseInstances("A"), 1);

    // Verify VTT
    EXPECT_TRUE(result.hasVTT("D"));
    auto vtt = result.getVTT("D");
    EXPECT_GT(vtt.entryCount(), 0);
}
```
</test_structure>

<implementation>
1. **Study existing integration tests**:
   - Read `tests/integration/handlers/VirtualMethodsIntegrationTest.cpp`
   - Read `tests/integration/handlers/MultipleInheritanceIntegrationTest.cpp`
   - Understand test helpers and utilities

2. **Create test file(s)**:
   - `tests/integration/handlers/VirtualInheritanceIntegrationTest.cpp`
   - Or split into multiple files if needed for organization

3. **Write tests progressively**:
   - Start with simplest case (single virtual base)
   - Add complexity gradually
   - Ensure each test is focused and clear

4. **Use test helpers**:
   - Leverage existing helper functions for creating C++ AST
   - Use assertion helpers for C AST validation
   - Create new helpers if needed for inheritance-specific checks

5. **Verify against real C++ behavior**:
   - Each test should match how real C++ handles the case
   - Reference C++ ABI documentation if needed
   - Ensure generated C code would have same semantics

For maximum efficiency, when writing multiple independent test cases, create them in parallel.
</implementation>

<output>
Create integration test files:
- `tests/integration/handlers/VirtualInheritanceIntegrationTest.cpp` (primary)
- Additional files if tests are logically grouped differently

Update:
- `tests/CMakeLists.txt` - Add integration test executables
- `scripts/test-cicd-local-parity.sh` - Add to test list if not auto-discovered
</output>

<verification>
After creating integration tests:

1. **Build and run**:
   ```bash
   cmake --build build
   ./build/VirtualInheritanceIntegrationTest
   ```

2. **Verify test quality**:
   - Tests use realistic C++ code
   - Assertions check C AST structure (not text output)
   - Tests cover handler interactions, not just individual handlers

3. **Check completeness**:
   - All scenarios from requirements are tested
   - Edge cases are included
   - Both success and failure paths tested

4. **Validate correctness**:
   - Test expectations match real C++ behavior
   - C AST structure is what C code printer expects
   - No false positives (tests pass when they shouldn't)

5. **Performance**:
   - Integration tests should be reasonably fast (seconds, not minutes)
   - No unnecessary transpilation runs
</verification>

<success_criteria>
Integration testing is complete when:

- ✅ All inheritance scenarios from requirements have tests
- ✅ Tests verify C AST structure and handler coordination
- ✅ Diamond pattern, multiple virtual bases, deep hierarchies all tested
- ✅ Virtual inheritance + virtual methods combination tested
- ✅ Tests use realistic C++ code examples
- ✅ All tests pass consistently
- ✅ Tests are added to build system and CI
- ✅ No handler interaction bugs found (tests catch coordination issues)
- ✅ Test coverage complements unit tests (different focus)
</success_criteria>
