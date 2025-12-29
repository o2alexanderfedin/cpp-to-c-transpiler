# Example Vtable Generation Output

## Test Case: Simple Virtual Method

### C++ Input
```cpp
class Shape {
public:
    virtual int getArea() { return 0; }
};
```

### Generated Vtable Struct
```c
struct Shape__vtable {
    const struct __class_type_info *type_info;
    int (*getArea)(struct Shape *this);
};
```

### Generated Vtable Instance
```c
static struct Shape__vtable Shape__vtable_instance = {
    .type_info = &Shape__type_info,
    .getArea = Shape__getArea,
};
```

## Test Case: Multiple Virtual Methods

### C++ Input
```cpp
class Shape {
public:
    virtual int getArea() { return 0; }
    virtual void draw() {}
};
```

### Generated Vtable Struct
```c
struct Shape__vtable {
    const struct __class_type_info *type_info;
    int (*getArea)(struct Shape *this);
    void (*draw)(struct Shape *this);
};
```

### Generated Vtable Instance
```c
static struct Shape__vtable Shape__vtable_instance = {
    .type_info = &Shape__type_info,
    .getArea = Shape__getArea,
    .draw = Shape__draw,
};
```

## Test Case: Namespaced Class

### C++ Input
```cpp
namespace game {
    class Entity {
    public:
        virtual void update() {}
    };
}
```

### Generated Vtable Struct
```c
struct game__Entity__vtable {
    const struct __class_type_info *type_info;
    void (*update)(struct game__Entity *this);
};
```

### Generated Vtable Instance
```c
static struct game__Entity__vtable game__Entity__vtable_instance = {
    .type_info = &game__Entity__type_info,
    .update = game__Entity__update,
};
```

## Key Features Demonstrated

1. **Strongly Typed Function Pointers**
   - Each method has exact signature: `ReturnType (*methodName)(struct ClassName *this, params...)`
   - NOT generic `void*` pointers

2. **Per-Class Vtable Structs**
   - Each class gets its own struct type: `Shape__vtable`, `Entity__vtable`
   - Different classes have different vtable types

3. **RTTI Type Information**
   - First field: `const struct __class_type_info *type_info`
   - Follows Itanium C++ ABI

4. **Namespace Handling**
   - Namespace prefix applied with `__` separator
   - Example: `game::Entity` → `game__Entity__vtable`

5. **Designated Initializers**
   - C99 style: `.type_info = ...`, `.methodName = ...`
   - Compile-time type checking

## Comparison with COM/DCOM Pattern

### Microsoft COM Interface (C)
```c
typedef struct IUnknownVtbl {
    HRESULT (*QueryInterface)(IUnknown *this, REFIID riid, void **ppvObject);
    ULONG (*AddRef)(IUnknown *this);
    ULONG (*Release)(IUnknown *this);
} IUnknownVtbl;
```

### Our Implementation
```c
struct Shape__vtable {
    const struct __class_type_info *type_info;  // Similar to IID
    int (*getArea)(struct Shape *this);         // Strongly typed like COM
    void (*draw)(struct Shape *this);
};
```

**Similarities**:
- Strongly typed function pointers
- Explicit "this" parameter
- Struct-based vtable

**Differences**:
- We add RTTI type_info for C++ compatibility
- COM uses HRESULT return type convention
- COM has reference counting (AddRef/Release)
