# Group 4 Task 7: Virtual Call Code Generation

**Task**: Generate correct C code for virtual method calls
**Status**: PENDING
**Tests Required**: 12-15 unit tests
**Estimated Time**: 3-4 hours

## Task Description

Extend ExpressionHandler to generate `obj->lpVtbl->methodName(obj, args...)` pattern for virtual calls, while keeping non-virtual calls as `ClassName_methodName(obj, args...)`.

## Requirements

1. **Virtual call pattern**: `obj->lpVtbl->methodName(obj, args...)`
2. **Handle different object types**: Value (`obj.`), pointer (`ptr->`), reference
3. **Pass object as first arg**: Object becomes first argument to vtable function
4. **Preserve return value**: Handle methods with return types
5. **Non-virtual unchanged**: Keep existing translation for non-virtual calls

## Implementation Strategy (TDD)

### Test File
`tests/unit/handlers/ExpressionHandlerTest_VirtualCall.cpp`

### Tests to Create (12-15 tests)

1. **VirtualCallOnValue**: `obj.method()` → `(&obj)->lpVtbl->method(&obj)`
2. **VirtualCallOnPointer**: `ptr->method()` → `ptr->lpVtbl->method(ptr)`
3. **VirtualCallThroughBase**: Polymorphic call through base pointer
4. **VirtualCallWithArguments**: `obj.method(a, b)` → `obj.lpVtbl->method(obj, a, b)`
5. **VirtualCallWithReturnValue**: `int x = obj.method()`
6. **ChainedVirtualCalls**: `obj.method1().method2()`
7. **VirtualCallInExpression**: `x + obj.method()`
8. **VirtualCallInCondition**: `if (obj.method())`
9. **VirtualDestructorCall**: `delete ptr` → `ptr->lpVtbl->destructor(ptr)`
10. **StaticCastThenVirtualCall**: Cast followed by virtual call
11. **VirtualCallThroughRefParam**: Virtual call on reference parameter
12. **MultipleVirtualCallsSequence**: Multiple virtual calls in succession
13. **VirtualCallComplexArgs**: Virtual call with complex argument expressions
14. **VirtualCallNoArgs**: Simple `obj.speak()`
15. **VirtualCallReturnPointer**: Virtual method returning pointer

## Expected Translation Patterns

### Pattern 1: Value Object
```cpp
// C++
obj.speak();

// C
(&obj)->lpVtbl->speak(&obj);
```

### Pattern 2: Pointer Object
```cpp
// C++
ptr->speak();

// C
ptr->lpVtbl->speak(ptr);
```

### Pattern 3: With Arguments
```cpp
// C++
obj.setAge(5);

// C
(&obj)->lpVtbl->setAge(&obj, 5);
```

### Pattern 4: With Return Value
```cpp
// C++
int age = ptr->getAge();

// C
int age = ptr->lpVtbl->getAge(ptr);
```

### Pattern 5: Polymorphic (Base Pointer)
```cpp
// C++
Animal* animal = &dog;
animal->speak();

// C
struct Animal *animal = (struct Animal *)&dog;
animal->lpVtbl->speak(animal);
```

## Implementation Hints

1. **Detect call type**: Use Task 6's virtual detection
2. **Get object expression**: Extract `obj` or `ptr` from MemberCallExpr
3. **Build lpVtbl access**: Create `obj->lpVtbl->methodName` expression
4. **Prepend object arg**: Add object as first argument to call
5. **Handle value vs pointer**: Use `&obj` for value, `ptr` for pointer

## Files to Modify

- `src/handlers/ExpressionHandler.cpp` - Extend translateCXXMemberCallExpr()

## Success Criteria

- All 12-15 tests pass
- Correct pattern for value/pointer/reference objects
- Virtual and non-virtual calls both work
- Arguments and return values handled correctly
- Object always passed as first argument
