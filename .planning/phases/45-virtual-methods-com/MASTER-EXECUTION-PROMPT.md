# Phase 45 Groups 3-5: Complete Implementation Prompt

## Context

You are completing Phase 45 (Virtual Methods with COM-Style Vtables) Groups 3-5.

**Already Complete:**
- Group 1: Vtable Infrastructure (22/22 tests ✅)
- Group 2: Struct Layout (18/18 tests ✅)
- **Total so far**: 40/40 tests passing

**Your Mission:**
Complete Groups 3-5 following strict TDD, implementing ~70 new tests.

## Project Structure

**Base Directory**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c`
**Build Directory**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build`

**Key Files:**
- `include/handlers/ConstructorHandler.h` and `.cpp`
- `include/handlers/ExpressionHandler.h` and `.cpp`
- `include/helpers/VtableTypedefGenerator.h` (already exists)
- Test pattern: See `tests/unit/handlers/ConstructorHandlerTest.cpp` for reference

## Group 3: Constructor lpVtbl Initialization

### Task: Create `tests/unit/handlers/ConstructorHandlerTest_lpVtbl.cpp`

**Pattern to Follow**: Copy structure from `ConstructorHandlerTest.cpp`

**8-10 Tests to Implement:**

```cpp
1. lpVtblInDefaultConstructor - verify default ctor initializes lpVtbl
2. lpVtblInParameterizedConstructor - verify parameterized ctor initializes lpVtbl
3. lpVtblBeforeFieldInit - verify lpVtbl init is FIRST statement
4. lpVtblInDerivedConstructor - derived class uses correct vtable
5. lpVtblInMultipleConstructors - all overloaded ctors initialize lpVtbl
6. lpVtblWithMemberInitList - lpVtbl before member init list
7. lpVtblCorrectType - verify correct vtable instance reference
8. lpVtblStaticVtableReference - uses &ClassName_vtable_instance
9. NoLpVtblForNonPolymorphic - non-virtual classes don't get lpVtbl
10. lpVtblInVirtualDestructor - ctor with virtual dtor initializes lpVtbl
```

**Expected Pattern:**
```c
void Animal_init_int(struct Animal *this, int a) {
    this->lpVtbl = &Animal_vtable_instance;  /* FIRST */
    this->age = a;
}
```

### Implementation in `ConstructorHandler.cpp`:

1. Check if class is polymorphic: `CXXRecordDecl::isPolymorphic()`
2. If polymorphic, inject lpVtbl initialization as first statement
3. Use CNodeBuilder to create assignment: `this->lpVtbl = &ClassName_vtable_instance`

## Group 4: Virtual Call Translation

### Task 6: Create `tests/unit/handlers/ExpressionHandlerTest_VirtualDetect.cpp`

**6-8 Tests:**
```cpp
1. DetectVirtualMethodCall - obj.virtualMethod() detected as virtual
2. DetectNonVirtualMethodCall - obj.regularMethod() detected as non-virtual
3. DetectVirtualCallOnBasePointer - basePtr->virtualMethod() is virtual
4. DetectVirtualCallOnDerivedPointer - derivedPtr->virtualMethod() is virtual
5. DetectVirtualDestructor - virtual destructor detection
6. StaticMethodNotVirtual - static methods are never virtual
7. InlineMethodNotVirtual - inline methods as non-virtual
8. FinalMethodNotVirtual - final methods don't use vtable
```

**Detection Logic:**
```cpp
bool isVirtualCall(const CXXMemberCallExpr* call) {
    const CXXMethodDecl* method = call->getMethodDecl();
    return method && method->isVirtual();
}
```

### Task 7: Create `tests/unit/handlers/ExpressionHandlerTest_VirtualCall.cpp`

**12-15 Tests:**
```cpp
1. VirtualCallOnValue - obj.method() → (&obj)->lpVtbl->method(&obj)
2. VirtualCallOnPointer - ptr->method() → ptr->lpVtbl->method(ptr)
3. VirtualCallThroughBase - polymorphic call through base pointer
4. VirtualCallWithArguments - obj.method(a,b) → lpVtbl->method(obj,a,b)
5. VirtualCallWithReturnValue - int x = obj.method()
6. ChainedVirtualCalls - obj.method1().method2()
7. VirtualCallInExpression - x + obj.method()
8. VirtualCallInCondition - if (obj.method())
9. VirtualDestructorCall - delete ptr
10. StaticCastThenVirtualCall - cast then call
11. VirtualCallThroughRefParam - reference parameter call
12. MultipleVirtualCallsSequence - multiple calls in succession
13. VirtualCallComplexArgs - complex argument expressions
14. VirtualCallNoArgs - simple obj.speak()
15. VirtualCallReturnPointer - method returning pointer
```

**Code Generation Pattern:**
```c
// C++: ptr->speak();
// C: ptr->lpVtbl->speak(ptr);

// C++: obj.setAge(5);
// C: (&obj)->lpVtbl->setAge(&obj, 5);
```

## Group 5: Integration & E2E

### Task 8: Create `tests/integration/handlers/VirtualMethodsIntegrationTest.cpp`

**Test Structure:**
```cpp
class VirtualMethodsIntegrationTest : public ::testing::Test {
protected:
    std::string transpile(const std::string& cppCode) {
        // Use TranspilerAPI to translate code
        // Return generated C code as string
    }
};
```

**30-35 Tests across 5 categories:**

**Category 1: Simple (5 tests)**
- SimpleClassOneVirtual
- ClassMultipleVirtual
- VirtualDestructor
- MixedVirtualNonVirtual
- ConstVirtualMethod

**Category 2: Inheritance (10 tests)**
- SingleInheritanceOverride
- SingleInheritanceInherited
- MultiLevelInheritance
- VirtualDestructorInheritance
- OverrideInMultipleLevels
- DerivedAddsVirtualMethod
- BaseVirtualDerivedNonVirtual
- MultipleDerivedFromSameBase
- InheritanceVtableSlotOrder
- InheritanceVtableCompatibility

**Category 3: Pure Virtual (5 tests)**
- PureVirtualInterface
- ConcreteImplementation
- PartialImplementation
- MultipleConcreteImplementations
- AbstractInheritanceChain

**Category 4: Polymorphic Calls (8 tests)**
- VirtualCallThroughBase
- VirtualCallThroughDerived
- PolymorphicArray
- PolymorphicFunctionParameter
- VirtualCallInLoop
- VirtualCallWithMethodChaining
- VirtualCallWithComplexReturn
- VirtualCallWithRefParams

**Category 5: Advanced (7 tests)**
- VirtualMethodComplexParams
- VirtualMethodReturningPointer
- VirtualMethodOverloadNotOverride
- NestedClassVirtual
- VirtualInTemplateClass
- StaticAndVirtualMixed
- VirtualCallFromConstructor

**Each test verifies:**
- Typedef generated
- Vtable struct created
- lpVtbl field present
- Vtable instance initialized
- Constructor sets lpVtbl
- Virtual calls use lpVtbl->method

### Task 9: Create `tests/e2e/phase45/VirtualMethodsE2ETest.cpp`

**15 Tests (1-3 active, rest DISABLED_):**

**Active:**
1. SimpleVirtualCall - basic virtual method works
2. PolymorphicDispatch - base pointer calls derived method
3. VirtualCallWithReturnValue - return value handled correctly

**Disabled (for future):**
4. DISABLED_ShapeHierarchy
5. DISABLED_AnimalHierarchy
6. DISABLED_StackInterface
7. DISABLED_ListInterface
8. DISABLED_IteratorPattern
9. DISABLED_StrategyPattern
10. DISABLED_ObserverPattern
11. DISABLED_FactoryPattern
12. DISABLED_PluginSystem
13. DISABLED_EventHandlerSystem
14. DISABLED_StatePattern
15. DISABLED_VisitorPattern

## CMakeLists.txt Updates

Add new test targets:
```cmake
# Group 3
add_executable(ConstructorHandlerTest_lpVtbl
    tests/unit/handlers/ConstructorHandlerTest_lpVtbl.cpp)
target_link_libraries(ConstructorHandlerTest_lpVtbl ...)
add_test(NAME ConstructorHandlerTest_lpVtbl ...)

# Group 4
add_executable(ExpressionHandlerTest_VirtualDetect ...)
add_executable(ExpressionHandlerTest_VirtualCall ...)

# Group 5
add_executable(VirtualMethodsIntegrationTest ...)
add_executable(VirtualMethodsE2ETest ...)
```

## Execution Strategy

1. **Group 3** (Sequential):
   - Create test file
   - Modify ConstructorHandler
   - Run tests, verify 8-10 pass
   - Commit: "feat(phase45-g3): Implement lpVtbl initialization"

2. **Group 4** (Can be parallel):
   - Task 6 and Task 7 can be done together
   - Total 18-23 tests
   - Commit: "feat(phase45-g4): Implement virtual call detection and generation"

3. **Group 5** (Sequential):
   - Task 8 first (integration)
   - Task 9 second (E2E)
   - Commit: "feat(phase45-g5): Add integration and E2E tests"

## Success Criteria

- All new tests pass (100%)
- Follow TDD strictly
- Code follows SOLID principles
- Generated C uses COM pattern
- Type-safe (no void*)
- lpVtbl always first member

## Report Format

When complete, report:
1. Tests created and passing (e.g., "Group 3: 10/10 tests pass")
2. Files modified/created
3. Issues encountered and resolved
4. Total test count for Phase 45
5. Git commit IDs
6. Time taken per group

---

**Execute this plan following strict TDD. Good luck!**
