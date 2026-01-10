# Phase 56: Virtual Inheritance E2E Tests

## Overview

This directory contains comprehensive end-to-end tests for virtual inheritance transpilation. These tests validate the complete pipeline from C++ source code with virtual inheritance to executable C code that maintains C++ ABI (Application Binary Interface) compliance.

## Test Status

**Current Status**: ⚠️ All tests DISABLED (pending handler implementation)

All tests are currently disabled with `DISABLED_` prefix because virtual inheritance handler integration is incomplete. According to the [inheritance handlers audit report](../../../audit-reports/inheritance-handlers-audit.md), the following components need integration:

1. **Handler Integration** - VirtualInheritanceAnalyzer, VTTGenerator, and ConstructorSplitter need to be integrated into the handler dispatch chain
2. **C1/C2 Constructor Generation** - Constructor splitting for most-derived vs base-object construction
3. **VTT Emission** - Virtual Table Table (VTT) struct and instance generation
4. **vbptr Injection** - Virtual base pointer field injection into structs
5. **Virtual Base Offsets** - Vtable generation with virtual base offset tables

**Estimated completion**: 43-55 hours of development work (see audit report)

## Test Coverage

### Test 1: SimpleVirtualBase
**File**: `VirtualInheritanceE2ETest.cpp::DISABLED_SimpleVirtualBase`

Basic virtual inheritance scenario with single virtual base class.

```cpp
struct Base { int x; virtual ~Base() {} };
struct Derived : virtual Base { int y; };
```

**Validates**:
- Single virtual base detection
- vbptr field injection
- Basic VTT generation
- Constructor initialization order

**Expected Exit Code**: 30 (10 + 20)

---

### Test 2: DiamondPattern
**File**: `VirtualInheritanceE2ETest.cpp::DISABLED_DiamondPattern`

Classic diamond inheritance pattern - the canonical virtual inheritance use case.

```cpp
struct A { int a_data; virtual ~A() {} };
struct B : virtual A { int b_data; };
struct C : virtual A { int c_data; };
struct D : B, C { int d_data; };
```

**Validates**:
- Single A instance in D (diamond problem solved)
- VTT generation for diamond hierarchy
- Virtual base construction by most-derived class
- Multiple inheritance paths to virtual base
- C1/C2 constructor variants

**Expected Exit Code**: 100 (10 + 20 + 30 + 40)

**ABI Compliance**: This test specifically validates that the generated C code creates only ONE instance of class A, not multiple copies as would happen with non-virtual inheritance.

---

### Test 3: MultipleVirtualBases
**File**: `VirtualInheritanceE2ETest.cpp::DISABLED_MultipleVirtualBases`

Multiple independent virtual bases (not forming a diamond).

```cpp
struct Base1 { int x; virtual ~Base1() {} };
struct Base2 { int y; virtual ~Base2() {} };
struct Derived : virtual Base1, virtual Base2 { int z; };
```

**Validates**:
- Multiple vbptr management
- Multiple VTT entries
- Independent virtual base construction
- Correct offset calculation for each virtual base

**Expected Exit Code**: 60 (10 + 20 + 30)

---

### Test 4: DeepVirtualInheritance
**File**: `VirtualInheritanceE2ETest.cpp::DISABLED_DeepVirtualInheritance`

Three or more levels of virtual inheritance hierarchy.

```cpp
struct Level0 { virtual ~Level0() {} };
struct Level1 : virtual Level0 { };
struct Level2 : virtual Level1 { };
struct Level3 : virtual Level2 { };
```

**Validates**:
- Offset propagation through multiple levels
- VTT chaining across hierarchy
- Construction order (Level0 → Level1 → Level2 → Level3)
- Transitive virtual base handling

**Expected Exit Code**: 15 (1 + 2 + 4 + 8)

---

### Test 5: VirtualInheritanceWithVirtualMethods
**File**: `VirtualInheritanceE2ETest.cpp::DISABLED_VirtualInheritanceWithVirtualMethods`

Combined virtual inheritance and virtual methods (polymorphism).

```cpp
struct Base { virtual int getValue() { return 10; } };
struct Derived1 : virtual Base { int getValue() override { return 20; } };
struct Derived2 : virtual Base { int getValue() override { return 30; } };
struct Final : Derived1, Derived2 { int getValue() override { return 40; } };
```

**Validates**:
- Vtable with both virtual method pointers AND virtual base offsets
- Virtual call dispatch through vptr
- Override resolution in virtual inheritance hierarchy
- COM-style vtable layout with virtual inheritance

**Expected Exit Code**: 40

**Critical**: This test validates that the vtable contains BOTH the virtual method function pointers AND the virtual base offset table, as required by Itanium C++ ABI.

---

### Test 6: NonPODVirtualBases
**File**: `VirtualInheritanceE2ETest.cpp::DISABLED_NonPODVirtualBases`

Virtual bases with constructors and destructors.

```cpp
struct Base {
    int id;
    Base() : id(++counter) {}
    virtual ~Base() { --counter; }
};
struct Final : Derived1, Derived2 { /* diamond with Base */ };
```

**Validates**:
- Virtual base constructed exactly once (counter = 1)
- Virtual base destructed exactly once (counter back to 0)
- Constructor/destructor ordering with virtual inheritance
- Most-derived class responsibility for virtual base construction

**Expected Exit Code**: 0 (counter returns to 0 after destruction)

**Important**: Tests that virtual bases are initialized BEFORE non-virtual bases, and that most-derived class constructs virtual bases (not intermediate classes).

---

### Test 7: CastingWithVirtualInheritance
**File**: `VirtualInheritanceE2ETest.cpp::DISABLED_CastingWithVirtualInheritance`

Pointer casting (upcasts/downcasts) with virtual bases.

```cpp
struct Base { int x; virtual ~Base() {} };
struct Derived : virtual Base { int y; };

Derived d;
Base* basePtr = &d;  // Upcast requires pointer adjustment
```

**Validates**:
- Upcast to virtual base (pointer adjustment via vbptr + offset)
- Pointer arithmetic for virtual base access
- Correct memory location calculation at runtime
- ABI-compliant casting behavior

**Expected Exit Code**: 35 (10 + 25)

**Critical**: Virtual base access requires runtime offset calculation using `vbptr + offset`, not compile-time static offset.

---

### Test 8: RealWorldIOStreamStyle
**File**: `VirtualInheritanceE2ETest.cpp::DISABLED_RealWorldIOStreamStyle`

Real-world iostream-style hierarchy (the motivating use case for virtual inheritance).

```cpp
struct ios_base { int flags; virtual ~ios_base() {} };
struct istream : virtual ios_base { int read_pos; };
struct ostream : virtual ios_base { int write_pos; };
struct iostream : istream, ostream { };
```

**Validates**:
- Complex real-world virtual inheritance pattern
- Single shared base (ios_base) accessed by multiple paths
- Correct field layout in memory
- Full pipeline with realistic C++ code

**Expected Exit Code**: 30 (5 + 10 + 15)

**Real-World Impact**: This pattern is used in C++ standard library's iostream hierarchy. Transpiler must handle it correctly for real C++ codebases.

---

### Test 9: MixedInheritance
**File**: `VirtualInheritanceE2ETest.cpp::DISABLED_MixedInheritance`

Mix of virtual and non-virtual inheritance in same hierarchy.

```cpp
struct VirtualBase { virtual ~VirtualBase() {} };
struct NonVirtualBase { };
struct Derived : virtual VirtualBase, NonVirtualBase { };
```

**Validates**:
- Correct classification of virtual vs non-virtual bases
- Separate handling of each inheritance type
- Field layout with mixed inheritance
- VTT only for virtual bases, not non-virtual

**Expected Exit Code**: 31 (1 + 2 + 4 + 8 + 16)

---

### Test 10: VirtualBaseAccessMultiplePaths
**File**: `VirtualInheritanceE2ETest.cpp::DISABLED_VirtualBaseAccessMultiplePaths`

Accessing virtual base members through different inheritance paths.

```cpp
struct Base { int value; virtual ~Base() {} };
struct Left : virtual Base { void setViaLeft(int v) { value = v; } };
struct Right : virtual Base { int getViaRight() { return value; } };
struct Derived : Left, Right { };
```

**Validates**:
- Single virtual base instance shared by all paths
- Consistent virtual base access regardless of path
- vbptr-based access works correctly from any path
- ABI compliance for multi-path access

**Expected Exit Code**: 42

**Critical**: Verifies that modifying virtual base through one path (Left) is visible through another path (Right) - proving single instance semantics.

---

## ABI Compliance Validation

All tests use the `ABIValidator` helper class (see `../ABIValidator.h`) to verify:

1. **Memory Layout**:
   - C struct sizes match C++ class sizes
   - Field offsets match Itanium C++ ABI
   - Alignment requirements preserved

2. **VTable Structure**:
   - Virtual method pointers present
   - Virtual base offset table included
   - Correct vtable layout per ABI spec

3. **VTT (Virtual Table Table)**:
   - VTT generated for classes with virtual bases
   - VTT entries correct (construction vtables)
   - VTT passed to constructors

4. **Constructor Variants**:
   - C1 (complete object constructor) constructs virtual bases
   - C2 (base object constructor) skips virtual bases
   - Most-derived class uses C1, intermediate classes use C2

## Running Tests

### Build
```bash
cmake -B build_working -S .
cmake --build build_working --target VirtualInheritanceE2ETest
```

### Run (Current - All Disabled)
```bash
./build_working/VirtualInheritanceE2ETest
```

Output:
```
YOU HAVE 10 DISABLED TESTS
```

### Run (Future - After Implementation)
```bash
# Run all virtual inheritance E2E tests
./build_working/VirtualInheritanceE2ETest

# Run specific test
./build_working/VirtualInheritanceE2ETest --gtest_filter="*DiamondPattern"

# Run with verbose output
./build_working/VirtualInheritanceE2ETest --gtest_filter="*DiamondPattern" --gtest_also_run_disabled_tests
```

### Enable Tests (For Development)

To enable tests during development, remove the `DISABLED_` prefix:

```cpp
// Before (disabled):
TEST_F(VirtualInheritanceE2ETest, DISABLED_DiamondPattern) { ... }

// After (enabled):
TEST_F(VirtualInheritanceE2ETest, DiamondPattern) { ... }
```

## Implementation Progress

Track implementation progress using these checkpoints:

- [ ] **Handler Integration** (Priority 1) - 12-15 hours
  - [ ] VirtualInheritanceAnalyzer integrated into RecordHandler
  - [ ] VTTGenerator called by RecordHandler
  - [ ] ConstructorSplitter integrated into ConstructorHandler

- [ ] **C1/C2 Constructor Generation** (Priority 2) - 8-10 hours
  - [ ] C1 constructor (constructs virtual bases first)
  - [ ] C2 constructor (skips virtual bases)
  - [ ] VTT parameter passing

- [ ] **VTT Emission** (Priority 3) - 6-8 hours
  - [ ] VTT struct definition generation
  - [ ] VTT instance generation
  - [ ] VTT emission to output files

- [ ] **vbptr and Vtable Offsets** (Priority 4) - 6-8 hours
  - [ ] vbptr field injection
  - [ ] Virtual base offset table in vtable
  - [ ] vbptr initialization in constructors

- [ ] **Tests Enabled** (Priority 5)
  - [ ] Test 1: SimpleVirtualBase passes
  - [ ] Test 2: DiamondPattern passes
  - [ ] Test 3: MultipleVirtualBases passes
  - [ ] Test 4: DeepVirtualInheritance passes
  - [ ] Test 5: VirtualInheritanceWithVirtualMethods passes
  - [ ] Test 6: NonPODVirtualBases passes
  - [ ] Test 7: CastingWithVirtualInheritance passes
  - [ ] Test 8: RealWorldIOStreamStyle passes
  - [ ] Test 9: MixedInheritance passes
  - [ ] Test 10: VirtualBaseAccessMultiplePaths passes

## Success Criteria

Virtual inheritance E2E testing is complete when:

- ✅ All 10 E2E tests enabled (no `DISABLED_` prefix)
- ✅ All tests compile generated C code without errors
- ✅ All tests execute and return expected exit codes
- ✅ ABI validation passes for all tests
- ✅ Diamond pattern test confirms single virtual base instance
- ✅ Constructor/destructor ordering correct
- ✅ Virtual method calls work with virtual inheritance
- ✅ Casting with pointer adjustment works
- ✅ Real-world iostream-style hierarchy transpiles correctly

## References

1. **Itanium C++ ABI**: https://itanium-cxx-abi.github.io/cxx-abi/abi.html
   - Section 2.5: Virtual Table Layout
   - Section 2.6: Virtual Base Offsets
   - Section 5.2: Constructor Variants (C1/C2)

2. **Audit Report**: `../../../audit-reports/inheritance-handlers-audit.md`
   - Current implementation status
   - Gap analysis
   - Implementation recommendations

3. **Architecture**: `../../../CLAUDE.md`
   - 3-stage transpiler pipeline
   - Handler chain architecture
   - C++ AST → C AST → C source flow

## Notes

- Tests are disabled by default to prevent false failures
- Enable tests incrementally as implementation progresses
- Each test is independent and can be enabled separately
- Tests use realistic C++ code patterns from real-world projects
- ABI compliance is mandatory - tests will fail if ABI is violated
