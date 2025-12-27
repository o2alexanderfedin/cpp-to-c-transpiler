# Method Generation in C

## Overview

All C++ methods (virtual and non-virtual) are translated to C with explicit static function declarations for compile-time type safety. This ensures that all method signatures are verified at compile time, preventing type mismatches and improving code reliability.

## Pattern

### C++ Input

```cpp
class Widget {
    int value;
public:
    Widget(int v);
    int getValue() const;
    virtual void update(int v);
    virtual ~Widget();
};
```

### Generated C Output

```c
// All method declarations (static)
static void Widget__ctor_1(struct Widget *this, int v);
static int Widget_getValue(const struct Widget *this);
static void Widget_update(struct Widget *this, int v);
static void Widget__dtor(struct Widget *this);

// Implementations
static void Widget__ctor_1(struct Widget *this, int v) { ... }
static int Widget_getValue(const struct Widget *this) { ... }
static void Widget_update(struct Widget *this, int v) { ... }
static void Widget__dtor(struct Widget *this) { ... }
```

## Benefits

1. **Compile-time signature verification** - All function signatures match vtable function pointer types exactly
2. **Better debugging** - Function names are visible in stack traces and debuggers
3. **Self-documenting code** - Explicit signatures make code intent clear
4. **Consistent code style** - One pattern for all methods (virtual and non-virtual)
5. **No special cases** - Generator logic simplified (no different handling for virtual vs non-virtual)

## Method Name Mangling

### Constructors

Format: `ClassName__ctor[_N]` where N is the parameter count for overload disambiguation

Examples:
```c
static void Point__ctor(struct Point *this);                      // Point()
static void Point__ctor_1(struct Point *this, int v);             // Point(int)
static void Point__ctor_2(struct Point *this, int x, int y);      // Point(int, int)
```

### Destructors

Format: `ClassName__dtor`

Example:
```c
static void Widget__dtor(struct Widget *this);  // ~Widget()
```

### Regular Methods

Format: `ClassName_methodName[_suffix]`

Examples:
```c
static int Counter_getValue(const struct Counter *this);    // int getValue() const
static void Counter_increment(struct Counter *this);        // void increment()
```

## Special Cases

### Const Methods

Const-qualified methods receive a `const` pointer for the `this` parameter:

```cpp
class DataHolder {
    int data;
public:
    int getData() const { return data; }     // const method
    void setData(int d) { data = d; }        // non-const method
};
```

Generated C:
```c
static int DataHolder_getData(const struct DataHolder *this);  // const this
static void DataHolder_setData(struct DataHolder *this, int d); // mutable this
```

### Reference Parameters

C++ references are converted to pointers in C:

```cpp
class Swapper {
public:
    void swap(int& a, int& b) {
        int temp = a;
        a = b;
        b = temp;
    }
};
```

Generated C:
```c
static void Swapper_swap(struct Swapper *this, int* a, int* b);
```

### Overloaded Methods

For constructor overloads, parameter count is appended. For regular methods, future enhancement will use type-based mangling:

```cpp
class Printer {
public:
    void print(int n) { }
    void print(double d) { }
    void print(const char* s) { }
};
```

Currently generates (same base name, differentiated by signature):
```c
static void Printer_print(struct Printer *this, int n);
static void Printer_print(struct Printer *this, double d);
static void Printer_print(struct Printer *this, const char* s);
```

**Note**: Full overload resolution requires name mangling support, which is planned for future enhancement.

### Virtual Methods

Virtual methods follow the same pattern, with additional vtable initialization:

```cpp
class Shape {
public:
    virtual double area() const = 0;
    virtual void draw() const = 0;
    virtual ~Shape() {}
};
```

Generated C:
```c
// Static declarations
static double Shape_area(const struct Shape *this);
static void Shape_draw(const struct Shape *this);
static void Shape__dtor(struct Shape *this);

// Vtable struct
struct Shape_vtable {
    const struct __class_type_info *type_info;
    void (*destructor)(struct Shape *this);
    double (*area)(const struct Shape *this);
    void (*draw)(const struct Shape *this);
};

// Implementations
static double Shape_area(const struct Shape *this) { ... }
static void Shape_draw(const struct Shape *this) { ... }
static void Shape__dtor(struct Shape *this) { ... }
```

## Implementation Details

### MethodSignatureHelper Class

All signature generation is centralized in the `MethodSignatureHelper` class to ensure consistency across:
- VtableGenerator (for virtual method signatures)
- CppToCVisitor (for all method signatures)

This follows the DRY (Don't Repeat Yourself) principle and ensures that vtable function pointers exactly match method signatures.

### Type Translation

C++ types are translated to C types as follows:

| C++ Type | C Type |
|----------|--------|
| `void` | `void` |
| `bool` | `int` |
| `int`, `signed int` | `int` |
| `unsigned int` | `unsigned int` |
| `float` | `float` |
| `double` | `double` |
| `T&` (reference) | `T*` (pointer) |
| `const T&` | `const T*` |
| `class/struct T` | `struct T` |

## Code Organization

The method generation implementation is split across:

1. **MethodSignatureHelper** (`include/MethodSignatureHelper.h`, `src/MethodSignatureHelper.cpp`)
   - Centralized signature generation logic
   - Type string conversion
   - Name mangling for constructors, destructors, and methods

2. **CppToCVisitor** (`src/CppToCVisitor.cpp`)
   - `generateAllMethodDeclarations()` - Generates declarations for all methods in a class
   - Integrates with class-to-struct translation

3. **VtableGenerator** (`src/VtableGenerator.cpp`)
   - Uses MethodSignatureHelper for virtual method signatures
   - Ensures vtable function pointers match method signatures exactly

## Phase History

- **Phase 31-02 (v2.2.0)**: Introduced COM-style static declarations for virtual methods only
- **Phase 31-03 (v2.3.0)**: Extended COM-style declarations to ALL methods (virtual and non-virtual) for consistency and universal type safety
