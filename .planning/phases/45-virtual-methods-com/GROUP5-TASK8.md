# Group 5 Task 8: Integration Tests

**Task**: Create comprehensive integration tests for virtual methods
**Status**: PENDING
**Tests Required**: 30-35 integration tests
**Estimated Time**: 4-5 hours

## Task Description

Create `tests/integration/handlers/VirtualMethodsIntegrationTest.cpp` to test the complete virtual method pipeline from C++ source to generated C code.

## Requirements

1. **End-to-end translation**: Parse C++ → Generate C code → Verify output
2. **Complete scenarios**: Test realistic class hierarchies
3. **Verify all components**: Typedef, vtable struct, lpVtbl, vtable instance, calls
4. **Test polymorphism**: Base pointers calling derived implementations

## Implementation Strategy (TDD)

### Test File
`tests/integration/handlers/VirtualMethodsIntegrationTest.cpp`

### Test Categories (30-35 tests)

#### Category 1: Simple Virtual Methods (5 tests)
1. **SimpleClassOneVirtual**: Single virtual method
2. **ClassMultipleVirtual**: Multiple virtual methods
3. **VirtualDestructor**: Virtual destructor handling
4. **MixedVirtualNonVirtual**: Both virtual and non-virtual methods
5. **ConstVirtualMethod**: Const virtual method

#### Category 2: Inheritance (10 tests)
6. **SingleInheritanceOverride**: Derived overrides base virtual method
7. **SingleInheritanceInherited**: Derived inherits without override
8. **MultiLevelInheritance**: A → B → C hierarchy
9. **VirtualDestructorInheritance**: Virtual destructor in hierarchy
10. **OverrideInMultipleLevels**: Override at multiple levels
11. **DerivedAddsVirtualMethod**: Derived adds new virtual method
12. **BaseVirtualDerivedNonVirtual**: Derived doesn't override
13. **MultipleDerivedFromSameBase**: Dog and Cat from Animal
14. **InheritanceVtableSlotOrder**: Verify slot ordering preserved
15. **InheritanceVtableCompatibility**: Derived vtable compatible with base

#### Category 3: Pure Virtual (Abstract Classes) (5 tests)
16. **PureVirtualInterface**: Abstract base class
17. **ConcreteImplementation**: Concrete class implements pure virtual
18. **PartialImplementation**: Some pure virtual, some implemented
19. **MultipleConcreteImplementations**: Multiple classes implement interface
20. **AbstractInheritanceChain**: Abstract → Abstract → Concrete

#### Category 4: Polymorphic Calls (8 tests)
21. **VirtualCallThroughBase**: Base pointer → derived method
22. **VirtualCallThroughDerived**: Derived pointer → derived method
23. **PolymorphicArray**: Array of base pointers
24. **PolymorphicFunctionParameter**: Function accepting base pointer
25. **VirtualCallInLoop**: Loop calling virtual methods
26. **VirtualCallWithMethodChaining**: Chained virtual calls
27. **VirtualCallWithComplexReturn**: Virtual method returning pointer/struct
28. **VirtualCallWithRefParams**: Virtual method with reference parameters

#### Category 5: Advanced Scenarios (7 tests)
29. **VirtualMethodComplexParams**: Virtual with struct/pointer params
30. **VirtualMethodReturningPointer**: Virtual method returns pointer
31. **VirtualMethodOverloadNotOverride**: Overload vs override distinction
32. **NestedClassVirtual**: Virtual methods in nested classes
33. **VirtualInTemplateClass**: Virtual methods in template (monomorphized)
34. **StaticAndVirtualMixed**: Static methods + virtual methods
35. **VirtualCallFromConstructor**: Virtual call in constructor (warning case)

## Test Structure

Each test should verify:
1. ✅ Typedef generated for each virtual method
2. ✅ Vtable struct created with correct layout
3. ✅ lpVtbl field injected as first member
4. ✅ Vtable instance created and initialized
5. ✅ Constructor initializes lpVtbl
6. ✅ Virtual calls use lpVtbl->method pattern
7. ✅ Non-virtual calls use direct function call

## Example Test

```cpp
TEST_F(VirtualMethodsIntegrationTest, SimpleClassOneVirtual) {
    const char* code = R"(
        class Animal {
        public:
            virtual void speak() {}
        };
    )";

    std::string output = transpile(code);

    // Verify typedef
    EXPECT_THAT(output, HasSubstr("typedef void (*Animal_speak_fn)(struct Animal *this)"));

    // Verify vtable struct
    EXPECT_THAT(output, HasSubstr("struct Animal_vtable"));
    EXPECT_THAT(output, HasSubstr("Animal_speak_fn speak;"));

    // Verify lpVtbl field
    EXPECT_THAT(output, HasSubstr("const struct Animal_vtable *lpVtbl;"));

    // Verify vtable instance
    EXPECT_THAT(output, HasSubstr("static const struct Animal_vtable Animal_vtable_instance"));
    EXPECT_THAT(output, HasSubstr(".speak = (Animal_speak_fn)Animal_speak"));

    // Verify constructor initializes lpVtbl
    EXPECT_THAT(output, HasSubstr("this->lpVtbl = &Animal_vtable_instance;"));
}
```

## Files to Create

- `tests/integration/handlers/VirtualMethodsIntegrationTest.cpp`

## Success Criteria

- All 30-35 tests pass
- Tests cover all virtual method scenarios
- Each test verifies complete translation pipeline
- Tests demonstrate COM pattern compliance
