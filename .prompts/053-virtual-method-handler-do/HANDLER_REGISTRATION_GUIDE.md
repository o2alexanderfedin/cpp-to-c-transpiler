# VirtualMethodHandler Registration Guide

## Overview

This guide shows how to register VirtualMethodHandler in the dispatcher framework for production code and tests.

## Handler Registration Order

**CRITICAL:** Handlers must be registered in dependency order. Each handler may use outputs from previously registered handlers.

### Complete Registration Sequence

```cpp
// 1. Foundation Handlers (Types, Scopes, Parameters)
cpptoc::TypeHandler::registerWith(dispatcher);          // Types first (base dependency)
cpptoc::NamespaceHandler::registerWith(dispatcher);     // Namespace tracking
cpptoc::ParameterHandler::registerWith(dispatcher);     // Parameters (depends on TypeHandler)

// 2. Declaration Handlers (Functions, Records)
cpptoc::FunctionHandler::registerWith(dispatcher);      // Free functions
cpptoc::RecordHandler::registerWith(dispatcher);        // Structs/classes

// 3. Method Handlers (Static, Instance, Virtual)
cpptoc::StaticMethodHandler::registerWith(dispatcher);  // Static methods (NO this, NO vtable)
cpptoc::InstanceMethodHandler::registerWith(dispatcher); // Instance methods (WITH this, NO vtable)
cpptoc::VirtualMethodHandler::registerWith(dispatcher); // Virtual methods (WITH this, WITH vtable)

// 4. Statement Handlers (Body Translation)
cpptoc::CompoundStmtHandler::registerWith(dispatcher);  // Compound statements
cpptoc::ReturnStmtHandler::registerWith(dispatcher);    // Return statements

// 5. Expression Handlers (Values, Operations)
cpptoc::LiteralHandler::registerWith(dispatcher);       // Literal values
cpptoc::DeclRefExprHandler::registerWith(dispatcher);   // Variable references
cpptoc::BinaryOperatorHandler::registerWith(dispatcher); // Binary operations
cpptoc::UnaryOperatorHandler::registerWith(dispatcher); // Unary operations
cpptoc::ParenExprHandler::registerWith(dispatcher);     // Parenthesized expressions
cpptoc::ImplicitCastExprHandler::registerWith(dispatcher); // Implicit casts
```

## Method Handler Comparison

| Handler | Predicate | Has `this`? | Has vtable? | Output Example |
|---------|-----------|-------------|-------------|----------------|
| **StaticMethodHandler** | `isStatic() == true` | NO | NO | `int Math__add(int a, int b)` |
| **InstanceMethodHandler** | `!isStatic() && !isVirtual()` | YES | NO | `void Counter__increment(struct Counter* this)` |
| **VirtualMethodHandler** | `!isStatic() && isVirtual()` | YES | YES | `int Shape__getArea(struct Shape* this)` + vtable |

**All three exclude:** Constructors (CXXConstructorDecl) and Destructors (CXXDestructorDecl)

## Integration Test Example

From `tests/integration/FunctionTranslationIntegrationTest.cpp`:

```cpp
std::unique_ptr<CppToCVisitorDispatcher> createDispatcher(
    cpptoc::PathMapper& mapper,
    cpptoc::DeclLocationMapper& locMapper,
    cpptoc::DeclMapper& declMapper,
    cpptoc::TypeMapper& typeMapper,
    cpptoc::ExprMapper& exprMapper)
{
    auto dispatcher = std::make_unique<CppToCVisitorDispatcher>(
        mapper, locMapper, declMapper, typeMapper, exprMapper);

    // Register handlers in dependency order
    cpptoc::TypeHandler::registerWith(*dispatcher);
    cpptoc::ParameterHandler::registerWith(*dispatcher);
    cpptoc::FunctionHandler::registerWith(*dispatcher);

    cpptoc::CompoundStmtHandler::registerWith(*dispatcher);
    cpptoc::ReturnStmtHandler::registerWith(*dispatcher);

    cpptoc::LiteralHandler::registerWith(*dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(*dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(*dispatcher);
    cpptoc::ParenExprHandler::registerWith(*dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(*dispatcher);

    return dispatcher;
}
```

## Adding VirtualMethodHandler to Integration Tests

```cpp
std::unique_ptr<CppToCVisitorDispatcher> createDispatcherWithVirtual(
    cpptoc::PathMapper& mapper,
    cpptoc::DeclLocationMapper& locMapper,
    cpptoc::DeclMapper& declMapper,
    cpptoc::TypeMapper& typeMapper,
    cpptoc::ExprMapper& exprMapper)
{
    auto dispatcher = std::make_unique<CppToCVisitorDispatcher>(
        mapper, locMapper, declMapper, typeMapper, exprMapper);

    // Foundation
    cpptoc::TypeHandler::registerWith(*dispatcher);
    cpptoc::NamespaceHandler::registerWith(*dispatcher);
    cpptoc::ParameterHandler::registerWith(*dispatcher);

    // Declarations
    cpptoc::FunctionHandler::registerWith(*dispatcher);
    cpptoc::RecordHandler::registerWith(*dispatcher);

    // Methods
    cpptoc::StaticMethodHandler::registerWith(*dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(*dispatcher);
    cpptoc::VirtualMethodHandler::registerWith(*dispatcher);  // ← NEW

    // Statements
    cpptoc::CompoundStmtHandler::registerWith(*dispatcher);
    cpptoc::ReturnStmtHandler::registerWith(*dispatcher);

    // Expressions
    cpptoc::LiteralHandler::registerWith(*dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(*dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(*dispatcher);
    cpptoc::ParenExprHandler::registerWith(*dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(*dispatcher);

    return dispatcher;
}
```

## VirtualMethodHandler Features

### 1. Virtual Method Translation

**C++ Input:**
```cpp
class Shape {
public:
    virtual int getArea() { return 0; }
};
```

**C Output:**
```c
// Static declaration (compile-time type safety)
static int Shape__getArea(struct Shape *this);

// Function implementation
int Shape__getArea(struct Shape *this) {
    return 0;
}
```

### 2. Vtable Struct Generation

```cpp
// C++ Input
class Shape {
public:
    virtual int getArea() { return 0; }
    virtual void draw() {}
};

// C Output
struct Shape__vtable {
    const struct __class_type_info *type_info;  // RTTI
    int (*getArea)(struct Shape *this);          // Strongly typed
    void (*draw)(struct Shape *this);            // Strongly typed
};
```

### 3. Vtable Instance Generation

```cpp
// C Output
static struct Shape__vtable Shape__vtable_instance = {
    .type_info = &Shape__type_info,
    .getArea = Shape__getArea,
    .draw = Shape__draw,
};
```

### 4. Namespace Support

**C++ Input:**
```cpp
namespace game {
    class Entity {
    public:
        virtual void update() {}
    };
}
```

**C Output:**
```c
// Method
static void game__Entity__update(struct game__Entity *this);

// Vtable struct
struct game__Entity__vtable {
    const struct __class_type_info *type_info;
    void (*update)(struct game__Entity *this);
};

// Vtable instance
static struct game__Entity__vtable game__Entity__vtable_instance = {
    .type_info = &game__Entity__type_info,
    .update = game__Entity__update,
};
```

## Production Code Integration

When migrating from old CppToCVisitor to new dispatcher framework:

1. **Create dispatcher instance** in TranspilerAPI.cpp or equivalent
2. **Register all handlers** in dependency order (as shown above)
3. **Replace CppToCVisitor::TraverseDecl** with dispatcher.dispatch calls
4. **Ensure mappers are initialized** (PathMapper, DeclLocationMapper, DeclMapper, TypeMapper, ExprMapper)

### Example Production Setup

```cpp
// In TranspilerConsumer::HandleTranslationUnit()
void HandleTranslationUnit(clang::ASTContext &Context) override {
    // Create mappers
    cpptoc::PathMapper mapper(/* ... */);
    cpptoc::DeclLocationMapper locMapper;
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;

    // Create dispatcher
    CppToCVisitorDispatcher dispatcher(
        mapper, locMapper, declMapper, typeMapper, exprMapper);

    // Register handlers (CRITICAL: Dependency order!)
    cpptoc::TypeHandler::registerWith(dispatcher);
    cpptoc::NamespaceHandler::registerWith(dispatcher);
    cpptoc::ParameterHandler::registerWith(dispatcher);
    cpptoc::FunctionHandler::registerWith(dispatcher);
    cpptoc::RecordHandler::registerWith(dispatcher);
    cpptoc::StaticMethodHandler::registerWith(dispatcher);
    cpptoc::InstanceMethodHandler::registerWith(dispatcher);
    cpptoc::VirtualMethodHandler::registerWith(dispatcher);  // ← NEW
    cpptoc::CompoundStmtHandler::registerWith(dispatcher);
    cpptoc::ReturnStmtHandler::registerWith(dispatcher);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);

    // Dispatch translation unit
    auto *TU = Context.getTranslationUnitDecl();
    dispatcher.dispatch(Context, targetContext, TU);
}
```

## Dependencies

VirtualMethodHandler depends on:
- **TypeHandler** - For translating return types and parameter types
- **ParameterHandler** - For translating method parameters
- **NamespaceHandler** - For namespace prefix computation
- **RecordHandler** - For struct definitions (future: __vptr field coordination)

VirtualMethodHandler provides:
- Virtual method translations (static functions with `this` parameter)
- Static declarations (compile-time type safety)
- Vtable struct definitions (per-class with strongly typed function pointers)
- Vtable instance initializations (designated initializers)

## Testing

All 14 tests pass:
- 10 virtual method translation tests
- 4 vtable generation tests

Run tests:
```bash
./VirtualMethodHandlerDispatcherTest
```

Expected output:
```
[==========] Running 14 tests from 1 test suite.
[  PASSED  ] 14 tests.
```

## Next Steps

1. **Integrate VirtualMethodHandler** in production code (update TranspilerAPI.cpp)
2. **Coordinate __vptr field** with RecordHandler (add vptr to polymorphic structs)
3. **Output vtable structs and instances** during code generation
4. **Implement virtual call translation** (obj->method() → obj->__vptr->method(obj))

## References

- **VirtualMethodHandler Implementation:** `include/dispatch/VirtualMethodHandler.h`, `src/dispatch/VirtualMethodHandler.cpp`
- **Test Suite:** `tests/unit/dispatch/VirtualMethodHandlerDispatcherTest.cpp`
- **COM/DCOM Pattern:** `docs/VTABLE_IMPLEMENTATION.md`
- **StaticMethodHandler:** Commit 505f372
- **InstanceMethodHandler:** Commit b950845
- **VirtualMethodHandler:** Commits 9d60dd8, 6d72f10
