# Group 4 Task 6: Virtual Call Detection in ExpressionHandler

**Task**: Detect virtual method calls in ExpressionHandler
**Status**: PENDING
**Tests Required**: 6-8 unit tests
**Estimated Time**: 2-3 hours

## Task Description

Extend ExpressionHandler to detect when a method call is virtual vs non-virtual. This detection is critical for choosing the correct translation pattern.

## Requirements

1. **Detect virtual calls**: Check `CXXMethodDecl::isVirtual()`
2. **Distinguish from non-virtual**: Static, inline, final methods are NOT virtual
3. **Handle base pointer calls**: Virtual even when called through base class pointer
4. **Store detection result**: Flag for use by code generation

## Implementation Strategy (TDD)

### Test File
`tests/unit/handlers/ExpressionHandlerTest_VirtualDetect.cpp`

### Tests to Create (6-8 tests)

1. **DetectVirtualMethodCall**: `obj.virtualMethod()` is virtual
2. **DetectNonVirtualMethodCall**: `obj.regularMethod()` is not virtual
3. **DetectVirtualCallOnBasePointer**: `basePtr->virtualMethod()` is virtual
4. **DetectVirtualCallOnDerivedPointer**: `derivedPtr->virtualMethod()` is virtual
5. **DetectVirtualDestructor**: Virtual destructor call detection
6. **StaticMethodNotVirtual**: Static methods are never virtual
7. **InlineMethodNotVirtual**: Inline methods treated as non-virtual
8. **FinalMethodNotVirtual**: Final methods don't use vtable dispatch

## Detection Logic

```cpp
bool isVirtualCall(const CXXMemberCallExpr* call) {
    const CXXMethodDecl* method = call->getMethodDecl();
    if (!method) return false;

    // Check if method is virtual
    if (!method->isVirtual()) return false;

    // Check if called through base pointer (polymorphic)
    // Even derived class virtual calls use vtable in C
    return true;
}
```

## Test Examples

### Test 1: Detect Virtual Method Call
```cpp
class Base {
public:
    virtual void foo() {}
};

void test() {
    Base b;
    b.foo();  // Should detect as virtual
}
```

### Test 2: Non-Virtual Method
```cpp
class Base {
public:
    void foo() {}  // Not virtual
};

void test() {
    Base b;
    b.foo();  // Should detect as NON-virtual
}
```

## Files to Modify

- `include/handlers/ExpressionHandler.h` - Add virtual detection method
- `src/handlers/ExpressionHandler.cpp` - Implement detection logic

## Success Criteria

- All 6-8 tests pass
- Correctly identifies virtual vs non-virtual calls
- Works with base and derived pointers
- Handles special cases (static, final, inline)
