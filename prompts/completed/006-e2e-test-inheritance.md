<objective>
Create comprehensive end-to-end (E2E) tests for multiple inheritance and virtual inheritance, validating that the complete transpiler pipeline produces correct, compilable C code that matches C++ ABI semantics.

E2E tests verify the entire transpilation flow:
- C++ source → C++ AST → Handler chain → C AST → C source
- Generated C code compiles without errors
- Generated C code has the same runtime behavior as original C++
- Memory layout follows C++ ABI (Itanium ABI for virtual inheritance)
- Virtual base offsets match C++ ABI specifications

These tests provide the highest confidence that the transpiler works correctly in real-world scenarios.
</objective>

<context>
Read the audit report:
@./audit-reports/inheritance-handlers-audit.md

Read project architecture:
@CLAUDE.md

E2E test patterns:
- Located in `tests/e2e/` or `tests/integration/cpp23/`
- Use real C++ source files
- Run complete transpilation
- Compile generated C code
- Execute and verify behavior
- Example: `tests/e2e/phase45/VirtualMethodsE2ETest.cpp`

**Critical: C++ ABI Compliance**
The transpiler must follow the Itanium C++ ABI for virtual inheritance:
- Virtual base offsets stored in vtable
- VTT (Virtual Table Table) for construction
- Correct memory layout with virtual base pointer
- Runtime type information compatibility
- Reference: https://itanium-cxx-abi.github.io/cxx-abi/abi.html#vtable
</context>

<requirements>
Create E2E tests with real-world C++ code examples covering:

1. **Simple Virtual Inheritance**:
   - Basic virtual base class scenario
   - Verify: compiles, runs, produces correct output
   - Check: memory layout matches C++ ABI

2. **Diamond Inheritance (Classic)**:
   ```cpp
   struct A { int data; virtual ~A() {} };
   struct B : virtual A { int b_data; };
   struct C : virtual A { int c_data; };
   struct D : B, C { int d_data; };
   ```
   - Verify: single A instance in D (ABI-compliant)
   - Check: VTT generation for D construction
   - Test: accessing A members through B and C paths

3. **Multiple Virtual Bases**:
   ```cpp
   struct Base1 { virtual void f1(); };
   struct Base2 { virtual void f2(); };
   struct Derived : virtual Base1, virtual Base2 { };
   ```
   - Verify: both virtual bases initialized
   - Check: correct vtable and VTT layout
   - Test: virtual method calls work correctly

4. **Deep Virtual Inheritance Hierarchy**:
   - 3+ levels of virtual inheritance
   - Verify: offset propagation through levels
   - Check: ABI-compliant memory layout at each level
   - Test: construction and destruction order

5. **Virtual Inheritance + Virtual Methods**:
   ```cpp
   struct Base {
       virtual void foo() = 0;
       int x;
   };
   struct Derived1 : virtual Base {
       void foo() override { }
   };
   struct Derived2 : virtual Base {
       void foo() override { }
   };
   struct Final : Derived1, Derived2 {
       void foo() override { }
   };
   ```
   - Verify: virtual call resolution
   - Check: vtable contains both virtual method pointers and vbase offsets
   - Test: polymorphic behavior works

6. **Non-POD Virtual Bases**:
   - Virtual base with constructor, destructor
   - Verify: correct initialization order (vbases first)
   - Check: destructor called exactly once
   - Test: exception safety during construction

7. **Casting with Virtual Inheritance**:
   - `static_cast`, `dynamic_cast` with virtual bases
   - Verify: pointer adjustments are correct
   - Check: follows C++ ABI casting rules
   - Test: runtime type information works

8. **Real-World Scenario**:
   - Complex class hierarchy from actual use case
   - Multiple virtual bases, virtual methods, constructors
   - Verify: complete transpilation succeeds
   - Check: ABI compliance with g++/clang++ layout
   - Test: functionality equivalent to original C++
</requirements>

<abi_compliance>
**Mandatory ABI Checks**

For each E2E test, verify C++ ABI compliance:

1. **Memory Layout**:
   - Compare struct sizes: C struct size == C++ class size
   - Verify field offsets match C++ ABI
   - Check alignment requirements are met
   - Use `offsetof()` to validate layout

2. **VTable Structure**:
   - Virtual base offsets at correct vtable positions
   - Virtual method pointers in correct order
   - RTTI information present (if enabled)
   - VTable pointer placement follows ABI

3. **VTT (Virtual Table Table)**:
   - VTT generated for classes with virtual bases
   - VTT entries point to correct vtable positions
   - Construction vtables present
   - Subobject vtables correctly linked

4. **Validation Method**:
   ```cpp
   // In test: compare C and C++ layouts
   struct CppClass : virtual Base { };

   // Generated C:
   struct CppClass__C {
       void** __vptr;
       // ... fields
   };

   // Test:
   EXPECT_EQ(sizeof(CppClass__C), sizeof(CppClass));
   EXPECT_EQ(offsetof(CppClass__C, field), offsetof(CppClass, field));
   ```

5. **Reference Implementation**:
   - For each test, compile original C++ with g++ -fdump-class-hierarchy
   - Compare transpiler output against g++ layout
   - Ensure compatibility
</abi_compliance>

<test_structure>
E2E tests should:

1. **Define C++ source**:
   ```cpp
   const char* cpp_source = R"(
       struct Base { virtual ~Base() {} int x; };
       struct Derived : virtual Base { int y; };

       int main() {
           Derived d;
           d.x = 42;
           d.y = 100;
           return d.x + d.y;  // Should return 142
       }
   )";
   ```

2. **Run transpilation**:
   ```cpp
   auto result = transpile(cpp_source);
   ASSERT_TRUE(result.success());
   ```

3. **Compile generated C**:
   ```cpp
   auto c_code = result.getCCode();
   auto compile_result = compileC(c_code);
   ASSERT_TRUE(compile_result.success()) << compile_result.errors();
   ```

4. **Execute and verify**:
   ```cpp
   auto exit_code = execute(compile_result.executable());
   EXPECT_EQ(exit_code, 142);
   ```

5. **Verify ABI compliance**:
   ```cpp
   // Compare layouts
   verifyCppABICompliance(cpp_source, c_code);
   ```

Example full test:
```cpp
// File: tests/e2e/virtual_inheritance/DiamondPatternE2E.cpp

#include <gtest/gtest.h>
#include "E2ETestHelpers.h"
#include "ABIValidator.h"

TEST(VirtualInheritanceE2E, DiamondPattern) {
    const char* cpp_source = R"(
        #include <cstdio>

        struct A {
            int a_data;
            A() : a_data(10) {}
            virtual ~A() {}
        };

        struct B : virtual A {
            int b_data;
            B() : b_data(20) {}
        };

        struct C : virtual A {
            int c_data;
            C() : c_data(30) {}
        };

        struct D : B, C {
            int d_data;
            D() : d_data(40) {}
        };

        int main() {
            D d;
            // Single A instance - all paths see same a_data
            printf("%d\n", d.a_data);  // Should print 10
            return d.a_data + d.b_data + d.c_data + d.d_data;  // Should return 100
        }
    )";

    // Transpile
    auto result = transpileCppToC(cpp_source);
    ASSERT_TRUE(result.success()) << result.errors();

    // Verify ABI compliance
    ABIValidator validator;
    EXPECT_TRUE(validator.verifySizesMatch(cpp_source, result.cCode()));
    EXPECT_TRUE(validator.verifyOffsetsMatch(cpp_source, result.cCode()));
    EXPECT_TRUE(validator.verifyVTableLayout(cpp_source, result.cCode()));

    // Compile C code
    auto compile_result = compileWithGCC(result.cCode());
    ASSERT_TRUE(compile_result.success()) << compile_result.errors();

    // Execute and verify output
    auto exec_result = executeAndCapture(compile_result.executable());
    EXPECT_EQ(exec_result.exitCode(), 100);
    EXPECT_EQ(exec_result.stdout(), "10\n");
}
```
</test_structure>

<implementation>
1. **Create test files**:
   - `tests/e2e/virtual_inheritance/SimpleVirtualBaseE2E.cpp`
   - `tests/e2e/virtual_inheritance/DiamondPatternE2E.cpp`
   - `tests/e2e/virtual_inheritance/MultipleVirtualBasesE2E.cpp`
   - Additional files for other scenarios

2. **Implement ABI validator**:
   - Create helper class to compare C++ and C layouts
   - Use compiler introspection or manual comparison
   - Validate vtable structure matches ABI

3. **Use realistic examples**:
   - Draw from real-world C++ codebases
   - Include complex scenarios (not just toy examples)
   - Test error conditions and edge cases

4. **Verify incrementally**:
   - Start with simplest test (single virtual base)
   - Ensure it passes before moving to complex cases
   - Each test should be independently runnable

5. **Document expected behavior**:
   - Add comments explaining C++ ABI requirements
   - Reference ABI specification sections
   - Note any transpiler limitations
</implementation>

<output>
Create E2E test files in:
- `tests/e2e/virtual_inheritance/` (new directory)

Create helper utilities:
- `tests/e2e/ABIValidator.h` and `.cpp` (if not exists)
- `tests/e2e/E2ETestHelpers.h` (enhance if exists)

Update:
- `tests/CMakeLists.txt` - Add E2E test executables
- `scripts/test-cicd-local-parity.sh` - Add E2E tests to CI
</output>

<verification>
After creating E2E tests:

1. **Build and run**:
   ```bash
   cmake --build build
   ./scripts/test-cicd-local-parity.sh
   ```

2. **Manual verification**:
   - Run transpiler on test C++ files manually
   - Inspect generated C code for correctness
   - Compile with gcc/clang and verify it works
   - Compare memory layout with C++ compiler output

3. **ABI validation**:
   ```bash
   # Compile C++ with layout dump
   g++ -fdump-class-hierarchy test.cpp

   # Compare with transpiler output
   # Sizes, offsets, vtable entries should match
   ```

4. **Regression testing**:
   - All E2E tests should pass
   - No failures when run multiple times
   - No platform-specific issues

5. **Performance check**:
   - E2E tests should complete in reasonable time (< 30 seconds total)
   - Compilation should succeed quickly
</verification>

<success_criteria>
E2E testing is complete when:

- ✅ All inheritance scenarios from requirements have E2E tests
- ✅ Tests use real C++ code with meaningful examples
- ✅ Generated C code compiles without errors
- ✅ Generated C code executes with correct behavior
- ✅ **Memory layout matches C++ ABI (Itanium ABI)**
- ✅ **VTable structure follows ABI specification**
- ✅ **VTT generation is ABI-compliant**
- ✅ Diamond pattern test validates single virtual base instance
- ✅ Deep hierarchies test offset propagation
- ✅ Virtual methods + virtual inheritance tested together
- ✅ ABI validator confirms layout compatibility
- ✅ Tests pass consistently on target platforms
- ✅ Documentation includes ABI compliance notes
</success_criteria>
