# Quick Start: Complete the Virtual/Inheritance Test Migration

## TL;DR

Infrastructure is 100% ready. Follow these steps to complete the migration:

## Step 1: Fix Linking (5 minutes)

Edit `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/virtual_inheritance_tests/CMakeLists.txt`

Find this section (around line 49):
```cmake
add_executable(test_vtable_generator
    VtableGeneratorTest.cpp
)
```

Change to:
```cmake
add_executable(test_vtable_generator
    VtableGeneratorTest.cpp
    ../../src/VtableGenerator.cpp
    ../../src/VirtualMethodAnalyzer.cpp
    ../../src/OverrideResolver.cpp
    ../../src/CNodeBuilder.cpp
)
```

Repeat for each test executable, adding the implementation files it needs.

**Or use this simpler approach - create a shared library:**

Add this before the test executables:
```cmake
# Create shared test library with all implementations
add_library(cpp2c_impl STATIC
    ../../src/VtableGenerator.cpp
    ../../src/VirtualMethodAnalyzer.cpp
    ../../src/OverrideResolver.cpp
    ../../src/VptrInjector.cpp
    ../../src/VtableInitializer.cpp
    ../../src/VirtualCallTranslator.cpp
    ../../src/VirtualInheritanceAnalyzer.cpp
    ../../src/VTTGenerator.cpp
    ../../src/DynamicCastTranslator.cpp
    ../../src/TypeidTranslator.cpp
    ../../src/TypeInfoGenerator.cpp
    ../../src/PureVirtualHandler.cpp
    ../../src/CNodeBuilder.cpp
)

target_link_libraries(cpp2c_impl
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)
```

Then change COMMON_LIBS to:
```cmake
set(COMMON_LIBS
    cpp2c_impl  # Add this first
    GTest::gtest
    GTest::gtest_main
    clangTooling
    clangFrontend
    clangBasic
    clangAST
    clangLex
)
```

## Step 2: Build and Test (2 minutes)

```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/virtual_inheritance_tests/build
make clean
make test_vtable_generator
./test_vtable_generator
```

Should output:
```
[==========] Running 8 tests from 1 test suite.
[----------] Global test environment set-up.
[----------] 8 tests from VtableGeneratorTest
[ RUN      ] VtableGeneratorTest.GenerateSimpleVtable
[       OK ] VtableGeneratorTest.GenerateSimpleVtable
...
[==========] 8 tests from 1 test suite ran.
[  PASSED  ] 8 tests.
```

## Step 3: Migrate One File (10-15 minutes per file)

Example: VirtualMethodAnalyzerTest.cpp

### 3.1: Copy file
```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests
cp VirtualMethodAnalyzerTest.cpp virtual_inheritance_tests/
```

### 3.2: Edit the file

Replace header:
```cpp
// OLD
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualMethodAnalyzer.h"
#include <iostream>
#include <cassert>

// NEW
#include <gtest/gtest.h>
#include "../VirtualTableTestBase.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualMethodAnalyzer.h"
```

Remove macros:
```cpp
// DELETE THESE
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }
```

Remove helpers (use inherited):
```cpp
// DELETE buildAST() function - use inherited version
// DELETE findClass() function - use inherited version
```

Add fixture:
```cpp
// ADD THIS before the tests
class VirtualMethodAnalyzerTest : public VirtualTableTestBase {
};
```

Convert each test:
```cpp
// OLD
void test_DetectSingleVirtualMethod() {
    TEST_START("DetectSingleVirtualMethod");

    // ... test code ...

    ASSERT(analyzer.isPolymorphic(Base), "Base should be polymorphic");

    TEST_PASS("DetectSingleVirtualMethod");
}

// NEW
TEST_F(VirtualMethodAnalyzerTest, DetectSingleVirtualMethod) {
    // ... test code ...

    ASSERT_TRUE(analyzer.isPolymorphic(Base)) << "Base should be polymorphic";
}
```

Remove main():
```cpp
// DELETE THIS
int main() {
    test_DetectSingleVirtualMethod();
    test_DetectPureVirtualMethod();
    // ...
    return 0;
}
```

### 3.3: Add to CMakeLists.txt

Add executable (it's already there, just needs the source file):
```cmake
add_executable(test_virtual_method_analyzer
    VirtualMethodAnalyzerTest.cpp  # Already added
)
target_link_libraries(test_virtual_method_analyzer ${COMMON_LIBS})
```

### 3.4: Build and test
```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/virtual_inheritance_tests/build
make test_virtual_method_analyzer
./test_virtual_method_analyzer
```

## Step 4: Repeat for Remaining Files

Use the same pattern for each of the 15 remaining files:
1. Copy to virtual_inheritance_tests/
2. Add #include <gtest/gtest.h> and test base
3. Remove TEST_START/TEST_PASS/ASSERT macros
4. Remove buildAST() and findClass() helpers
5. Add test fixture class
6. Convert test functions to TEST_F
7. Remove main()
8. Build and test

## Quick Conversion Reference

| From | To |
|------|-----|
| `void test_FooBar()` | `TEST_F(ClassName, FooBar)` |
| `TEST_START("name")` | Remove |
| `TEST_PASS("name")` | Remove |
| `ASSERT(x, "msg")` | `ASSERT_TRUE(x) << "msg"` |
| `ASSERT(x == y, "msg")` | `ASSERT_EQ(x, y) << "msg"` |
| `ASSERT(x != y, "msg")` | `ASSERT_NE(x, y) << "msg"` |
| `ASSERT(x, "Expected...")` | `EXPECT_TRUE(x) << "Expected..."` |
| `buildAST(code)` | `buildAST(code)` (from base class) |
| `findClass(TU, "Foo")` | `findClass(TU, "Foo")` (from base class) |

## Files by Priority

### Do First (Core vtable)
1. VirtualMethodAnalyzerTest.cpp
2. VtableInitializerTest.cpp

### Do Second (Virtual inheritance)
3. VirtualBaseDetectionTest.cpp
4. VirtualBaseOffsetTableTest.cpp
5. VTTGeneratorTest.cpp

### Do Third (Override/hierarchy)
6. OverrideResolverTest.cpp
7. HierarchyTraversalTest.cpp
8. VirtualCallTranslatorTest.cpp

### Do Fourth (Vptr/pure virtual)
9. VptrInjectorTest.cpp
10. PureVirtualHandlerTest.cpp

### Do Fifth (Dynamic cast)
11. DynamicCastTranslatorTest.cpp
12. DynamicCastCrossCastTest.cpp
13. CrossCastTraversalTest.cpp

### Do Last (Type info)
14. TypeidTranslatorTest.cpp
15. TypeInfoGeneratorTest.cpp

## Automated Option

Run the Python script (requires manual review):
```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests
python3 migrate_to_gtest.py
```

Then review and fix each generated file.

## Verify All Tests Pass

```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/virtual_inheritance_tests/build
make -j8  # Parallel build
ctest --output-on-failure
```

Expected output:
```
Test project /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/virtual_inheritance_tests/build
      Start  1: VtableGeneratorTest.GenerateSimpleVtable
 1/127 Test  #1: VtableGeneratorTest.GenerateSimpleVtable ....   Passed    0.02 sec
      ...
127/127 Test #127: PureVirtualHandlerTest.ComplexHierarchy ....   Passed    0.03 sec

100% tests passed, 0 tests failed out of 127
```

## Done!

All 127 tests migrated and passing. Time to commit and celebrate!
