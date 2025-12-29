# CXXOperatorCallExprHandler Integration Guide

## Overview

CXXOperatorCallExprHandler integrates C++ operator overloading (CXXOperatorCallExpr) with the dispatcher framework. It detects overloaded operators and creates placeholder C CallExpr nodes.

## Handler Registration

To use CXXOperatorCallExprHandler, register it with your dispatcher instance:

```cpp
#include "dispatch/CppToCVisitorDispatcher.h"
#include "dispatch/CXXOperatorCallExprHandler.h"

// Create dispatcher with required dependencies
CppToCVisitorDispatcher dispatcher(pathMapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper);

// Register handler (order matters - register dependencies first)
cpptoc::DeclRefExprHandler::registerWith(dispatcher);       // For `this` and function references
cpptoc::LiteralHandler::registerWith(dispatcher);           // For literal arguments
cpptoc::ImplicitCastExprHandler::registerWith(dispatcher); // For implicit casts
cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher); // This handler

// Now dispatcher can handle CXXOperatorCallExpr nodes
bool handled = dispatcher.dispatch(cppCtx, cCtx, someOperatorCall);
```

## Supported Operators (12 Categories)

1. **Instance subscript (operator[])**: `arr[5]`
2. **Instance call (operator())**: `functor(10, 20)`
3. **Smart pointer arrow (operator->)**: `ptr->field`
4. **Smart pointer dereference (operator*)**: `*ptr`
5. **Stream output (operator<<)**: `cout << obj`
6. **Stream input (operator>>)**: `cin >> obj`
7. **Conversion operators (operator T())**: `(int)obj`
8. **Bool conversion (operator bool())**: `if (obj)`
9. **Copy assignment (operator=)**: `a = b`
10. **Move assignment (operator=(T&&))**: `a = move(b)`
11. **Address-of (operator&)**: `&obj` (rare)
12. **Comma (operator,)**: `(a, b)` (very rare)

## Architecture Notes

### Current Implementation (Dispatcher Pattern)

The handler creates **placeholder** C CallExpr nodes because:

1. SpecialOperatorTranslator requires CNodeBuilder and NameMangler (not available in dispatcher)
2. SpecialOperatorTranslator maintains state (m_methodMap, m_conversionMap)
3. Full translation requires C function declaration creation (Stage 2 of pipeline)

### Full Integration with SpecialOperatorTranslator

For complete operator translation, use SpecialOperatorTranslator in CppToCVisitor:

```cpp
// In CppToCVisitor::VisitCXXOperatorCallExpr
if (m_specialOpTrans->isSpecialOperator(E->getOperator())) {
    CallExpr* cCall = m_specialOpTrans->transformCall(E, C_Ctx);
    if (cCall) {
        // Store in ExprMapper
        return true;
    }
}
```

### Future Enhancement

To fully integrate SpecialOperatorTranslator with the dispatcher:

1. Add CNodeBuilder and NameMangler to dispatcher context
2. Make SpecialOperatorTranslator accessible via dispatcher
3. Call SpecialOperatorTranslator::transformCall() in handleOperatorCall()

## Test Coverage

- 14 unit tests covering all 12 operator categories
- Tests verify: handler registration, predicate correctness, ExprMapper integration
- Tests verify distinction from built-in operators (BinaryOperator, UnaryOperator)
- 100% pass rate

## Example Usage

```cpp
// C++ code with operator overloading
class Array {
public:
    int& operator[](size_t index);
};

int test() {
    Array arr;
    return arr[5];  // CXXOperatorCallExpr
}
```

After dispatcher translation:
```cpp
// Placeholder C CallExpr created
// Full translation happens in SpecialOperatorTranslator:
int* Array_operator_subscript_size_t(Array* this, size_t index);
return *Array_operator_subscript_size_t(&arr, 5);
```

## Integration Status

- **Handler Implementation**: Complete
- **Unit Tests**: 14 tests, 100% pass rate
- **CMake Integration**: Complete
- **Dispatcher Registration**: Manual (as per dispatcher pattern)
- **SpecialOperatorTranslator Integration**: Partial (see Architecture Notes)

## Next Steps

For production use:
1. Extend dispatcher context to include CNodeBuilder and NameMangler
2. Modify handleOperatorCall() to call SpecialOperatorTranslator::transformCall()
3. Remove placeholder CallExpr creation
4. Verify full translation pipeline works end-to-end
