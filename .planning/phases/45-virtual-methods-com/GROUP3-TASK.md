# Group 3: Constructor Integration - lpVtbl Initialization

**Task**: Inject lpVtbl initialization in ConstructorHandler
**Status**: PENDING
**Tests Required**: 8-10 unit tests
**Estimated Time**: 2-3 hours

## Task Description

Extend ConstructorHandler to inject `this->lpVtbl = &ClassName_vtable_instance;` as the first statement in every constructor of a polymorphic class.

## Requirements

1. **Detect polymorphic classes**: Check if the class has virtual methods
2. **Inject lpVtbl initialization**: Must be FIRST statement before field initialization
3. **Pattern**: `this->lpVtbl = &ClassName_vtable_instance;`
4. **Only for polymorphic classes**: Non-polymorphic classes should not get lpVtbl init

## Implementation Strategy (TDD)

### Test File
`tests/unit/handlers/ConstructorHandlerTest_lpVtbl.cpp`

### Tests to Create (8-10 tests)

1. **lpVtblInDefaultConstructor**: Default constructor initializes lpVtbl
2. **lpVtblInParameterizedConstructor**: Constructor with params initializes lpVtbl
3. **lpVtblBeforeFieldInit**: lpVtbl init happens before field assignments
4. **lpVtblInDerivedConstructor**: Derived class uses correct vtable
5. **lpVtblInMultipleConstructors**: All overloaded constructors initialize lpVtbl
6. **lpVtblWithMemberInitList**: lpVtbl init before member init list execution
7. **lpVtblCorrectType**: Verify lpVtbl points to correct vtable instance
8. **lpVtblStaticVtableReference**: Verify uses &ClassName_vtable_instance
9. **NoLpVtblForNonPolymorphic**: Non-virtual classes don't get lpVtbl init
10. **lpVtblInVirtualDestructor**: Constructor with virtual destructor initializes lpVtbl

## Expected Translation

**C++ Input:**
```cpp
class Animal {
    int age;
public:
    Animal(int a) : age(a) {}
    virtual void speak() {}
};
```

**C Output:**
```c
struct Animal {
    const struct Animal_vtable *lpVtbl;
    int age;
};

void Animal_init_int(struct Animal *this, int a) {
    this->lpVtbl = &Animal_vtable_instance;  /* FIRST STATEMENT */
    this->age = a;
}
```

## Implementation Hints

1. **Check if class is polymorphic**: Use `CXXRecordDecl::isPolymorphic()`
2. **Create assignment statement**: Use CNodeBuilder to create BinaryOperator
3. **Inject at beginning**: Prepend to existing body statements
4. **Get vtable instance name**: `ClassName_vtable_instance`

## Files to Modify

- `include/handlers/ConstructorHandler.h` - Add lpVtbl injection method
- `src/handlers/ConstructorHandler.cpp` - Implement lpVtbl injection logic

## Success Criteria

- All 8-10 tests pass
- lpVtbl initialization is ALWAYS first statement
- Only injected for polymorphic classes
- Correct vtable instance reference
- Works with all constructor variants (default, parameterized, multiple)
