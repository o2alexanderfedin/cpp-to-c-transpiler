# Constructor/Destructor Translation Guide

## Overview

This guide documents how the C++ to C transpiler translates C++ constructors and destructors into C code. It covers member initialization lists, constructor/destructor chaining, implicit constructors, and special cases like const and reference members.

## Table of Contents

1. [Basic Constructor Translation](#basic-constructor-translation)
2. [Member Initialization Lists](#member-initialization-lists)
3. [Constructor Chaining](#constructor-chaining)
4. [Destructor Chaining](#destructor-chaining)
5. [Implicit Constructors](#implicit-constructors)
6. [Special Cases](#special-cases)
7. [Complex Scenarios](#complex-scenarios)
8. [Best Practices](#best-practices)

## Basic Constructor Translation

### C++ Input

```cpp
class Point {
    int x, y;
public:
    Point(int x, int y) : x(x), y(y) {}
};
```

### C Output

```c
struct Point {
    int x;
    int y;
};

void Point__ctor(struct Point *this, int x, int y) {
    this->x = x;
    this->y = y;
}
```

### Key Points

- Constructors become `void ClassName__ctor(struct ClassName *this, ...)` functions
- The first parameter is always a pointer to the struct being constructed
- Member initialization lists are translated to assignments in declaration order
- Constructor body statements follow the member initializations

## Member Initialization Lists

Member initialization lists are translated to assignment statements in the generated constructor. **Initialization order follows declaration order, not init list order.**

### Example: Declaration Order Matters

#### C++ Input

```cpp
class OrderTest {
    int a, b, c;
public:
    // Init list order: c, a, b
    // Actual initialization order: a, b, c (declaration order!)
    OrderTest(int x, int y, int z) : c(z), a(x), b(y) {}
};
```

#### C Output

```c
struct OrderTest {
    int a;
    int b;
    int c;
};

void OrderTest__ctor(struct OrderTest *this, int x, int y, int z) {
    // Initialization follows DECLARATION order (a, b, c)
    // NOT init list order (c, a, b)
    this->a = x;
    this->b = y;
    this->c = z;
}
```

### Example: Class-Type Members

When members have class types, their constructors are called:

#### C++ Input

```cpp
class Inner {
    int value;
public:
    Inner(int v) : value(v) {}
};

class Outer {
    Inner inner;
public:
    Outer(int v) : inner(v) {}
};
```

#### C Output

```c
struct Inner {
    int value;
};

void Inner__ctor(struct Inner *this, int v) {
    this->value = v;
}

struct Outer {
    struct Inner inner;
};

void Outer__ctor(struct Outer *this, int v) {
    // Call member constructor
    Inner__ctor(&this->inner, v);
}
```

## Constructor Chaining

When a derived class is constructed, the base class constructor is called first, then member constructors, then the derived class body.

### Construction Order

1. **Base class constructors** (in inheritance order)
2. **Member constructors** (in declaration order)
3. **Derived class constructor body**

### Example: Single Inheritance

#### C++ Input

```cpp
class Base {
    int baseValue;
public:
    Base(int v) : baseValue(v) {}
};

class Derived : public Base {
    int derivedValue;
public:
    Derived(int b, int d) : Base(b), derivedValue(d) {}
};
```

#### C Output

```c
struct Base {
    int baseValue;
};

void Base__ctor(struct Base *this, int v) {
    this->baseValue = v;
}

struct Derived {
    // Base class embedded
    int baseValue;  // from Base
    // Derived class members
    int derivedValue;
};

void Derived__ctor(struct Derived *this, int b, int d) {
    // 1. Call base constructor first
    Base__ctor((struct Base*)this, b);

    // 2. Initialize derived members
    this->derivedValue = d;
}
```

### Example: Inheritance + Members

#### C++ Input

```cpp
class Component {
    int id;
public:
    Component(int i) : id(i) {}
};

class Transform {
    float x, y, z;
public:
    Transform(float x, float y, float z) : x(x), y(y), z(z) {}
};

class MeshComponent : public Component {
    Transform transform;
public:
    MeshComponent(int id, float x, float y, float z)
        : Component(id), transform(x, y, z) {}
};
```

#### C Output

```c
struct Component {
    int id;
};

void Component__ctor(struct Component *this, int i) {
    this->id = i;
}

struct Transform {
    float x, y, z;
};

void Transform__ctor(struct Transform *this, float x, float y, float z) {
    this->x = x;
    this->y = y;
    this->z = z;
}

struct MeshComponent {
    // Base embedded
    int id;  // from Component
    // Members
    struct Transform transform;
};

void MeshComponent__ctor(struct MeshComponent *this, int id, float x, float y, float z) {
    // 1. Base constructor
    Component__ctor((struct Component*)this, id);

    // 2. Member constructors (declaration order)
    Transform__ctor(&this->transform, x, y, z);
}
```

## Destructor Chaining

Destructors are called in **reverse** order of construction:

### Destruction Order

1. **Derived class destructor body**
2. **Member destructors** (reverse declaration order)
3. **Base class destructors** (reverse inheritance order)

### Example: Destructor Chaining

#### C++ Input

```cpp
class Base {
public:
    Base() {}
    ~Base() { /* cleanup base */ }
};

class Derived : public Base {
    Resource* resource;
public:
    Derived() : resource(new Resource()) {}
    ~Derived() {
        delete resource;  // Derived destructor body
    }
};
```

#### C Output

```c
struct Base {
    // empty
};

void Base__ctor(struct Base *this) {
    // empty
}

void Base__dtor(struct Base *this) {
    /* cleanup base */
}

struct Derived {
    // Base embedded
    // No Base fields
    // Derived members
    struct Resource* resource;
};

void Derived__ctor(struct Derived *this) {
    // 1. Base constructor
    Base__ctor((struct Base*)this);

    // 2. Allocate resource
    this->resource = /* new Resource() */;
}

void Derived__dtor(struct Derived *this) {
    // 1. Derived destructor body FIRST
    /* delete resource */;

    // 2. Member destructors (reverse order)
    // (resource is a pointer, no destructor call)

    // 3. Base destructor LAST
    Base__dtor((struct Base*)this);
}
```

## Implicit Constructors

The transpiler generates implicit constructors when not explicitly defined:

### Default Constructor (Primitives)

If a class has only primitive members and no explicit constructors, a default constructor is generated.

#### C++ Input

```cpp
class Point {
    int x, y;
};
```

#### C Output

```c
struct Point {
    int x;
    int y;
};

void Point__ctor_default(struct Point *this) {
    // Primitives are left uninitialized (C++ semantics)
    // Or zero-initialized depending on context
}
```

### Default Constructor (Class Members)

If a class has class-type members, the default constructor calls member default constructors.

#### C++ Input

```cpp
class Inner {
public:
    Inner() {}
};

class Outer {
    Inner inner;
};
```

#### C Output

```c
struct Inner {
    // empty
};

void Inner__ctor(struct Inner *this) {
    // empty
}

struct Outer {
    struct Inner inner;
};

void Outer__ctor_default(struct Outer *this) {
    // Call member default constructor
    Inner__ctor(&this->inner);
}
```

### Copy Constructor

The transpiler generates implicit copy constructors that perform memberwise copy.

#### C++ Input

```cpp
class Point {
    int x, y;
};

// Implicit copy constructor: Point(const Point& other)
```

#### C Output

```c
struct Point {
    int x;
    int y;
};

void Point__ctor_copy(struct Point *this, const struct Point *other) {
    // Memberwise copy
    this->x = other->x;
    this->y = other->y;
}
```

### Copy Constructor with Inheritance

#### C++ Input

```cpp
class Base {
    int baseValue;
};

class Derived : public Base {
    int derivedValue;
};
```

#### C Output

```c
void Derived__ctor_copy(struct Derived *this, const struct Derived *other) {
    // 1. Call base copy constructor
    Base__ctor_copy((struct Base*)this, (const struct Base*)other);

    // 2. Copy derived members
    this->derivedValue = other->derivedValue;
}
```

## Special Cases

### Const Members

Const members MUST be initialized through the constructor initialization list. In C, we use a const_cast technique:

#### C++ Input

```cpp
class Immutable {
    const int id;
    int value;
public:
    Immutable(int i, int v) : id(i), value(v) {}
};
```

#### C Output

```c
struct Immutable {
    const int id;
    int value;
};

void Immutable__ctor(struct Immutable *this, int i, int v) {
    // Const member initialization using cast
    *(int*)&this->id = i;

    // Regular member
    this->value = v;
}
```

### Reference Members

Reference members are translated to pointers in C:

#### C++ Input

```cpp
class RefHolder {
    int& ref;
    int value;
public:
    RefHolder(int& r, int v) : ref(r), value(v) {}
};
```

#### C Output

```c
struct RefHolder {
    int* ref;  // Reference becomes pointer
    int value;
};

void RefHolder__ctor(struct RefHolder *this, int* r, int v) {
    // Reference member initialization
    this->ref = r;

    // Regular member
    this->value = v;
}
```

### Empty Classes

Empty classes (no members) still get constructors/destructors translated:

#### C++ Input

```cpp
class Empty {
public:
    Empty() {}
    ~Empty() {}
};
```

#### C Output

```c
struct Empty {
    // C structs cannot be empty, add dummy byte
    char _dummy;
};

void Empty__ctor(struct Empty *this) {
    // Empty body
}

void Empty__dtor(struct Empty *this) {
    // Empty body
}
```

## Complex Scenarios

### Entity System with RAII

A real-world game engine entity system demonstrating all features:

#### C++ Input

```cpp
class Transform {
    float x, y, z;
public:
    Transform(float x, float y, float z) : x(x), y(y), z(z) {}
    ~Transform() {}
};

class Component {
protected:
    int id;
public:
    Component(int id) : id(id) {}
    virtual ~Component() {}
};

class MeshComponent : public Component {
    Transform transform;
    const int vertexCount;
public:
    MeshComponent(int id, float x, float y, float z, int verts)
        : Component(id),
          transform(x, y, z),
          vertexCount(verts) {}

    ~MeshComponent() {}
};
```

#### C Output

```c
struct Transform {
    float x, y, z;
};

void Transform__ctor(struct Transform *this, float x, float y, float z) {
    this->x = x;
    this->y = y;
    this->z = z;
}

void Transform__dtor(struct Transform *this) {
    // Empty
}

struct Component {
    int id;
};

void Component__ctor(struct Component *this, int id) {
    this->id = id;
}

void Component__dtor(struct Component *this) {
    // Empty
}

struct MeshComponent {
    // Base embedded
    int id;  // from Component
    // Members
    struct Transform transform;
    const int vertexCount;
};

void MeshComponent__ctor(struct MeshComponent *this, int id,
                         float x, float y, float z, int verts) {
    // 1. Base constructor
    Component__ctor((struct Component*)this, id);

    // 2. Member constructors (declaration order)
    Transform__ctor(&this->transform, x, y, z);

    // 3. Const member initialization
    *(int*)&this->vertexCount = verts;
}

void MeshComponent__dtor(struct MeshComponent *this) {
    // 1. Derived destructor body (empty)

    // 2. Member destructors (reverse order)
    // vertexCount: primitive, no destructor
    Transform__dtor(&this->transform);

    // 3. Base destructor
    Component__dtor((struct Component*)this);
}
```

### Resource Manager with Dynamic Allocation

#### C++ Input

```cpp
class DynamicArray {
    int* data;
    int size;
public:
    DynamicArray(int s) : size(s), data(new int[s]) {
        for (int i = 0; i < size; ++i) {
            data[i] = 0;
        }
    }

    ~DynamicArray() {
        delete[] data;
    }
};
```

#### C Output

```c
struct DynamicArray {
    int* data;
    int size;
};

void DynamicArray__ctor(struct DynamicArray *this, int s) {
    // Member init list
    this->size = s;
    this->data = malloc(s * sizeof(int));

    // Constructor body
    for (int i = 0; i < this->size; ++i) {
        this->data[i] = 0;
    }
}

void DynamicArray__dtor(struct DynamicArray *this) {
    free(this->data);
}
```

## Best Practices

### 1. Always Initialize Members

Ensure all members are initialized in the constructor initialization list or body.

### 2. Follow Declaration Order

Member initialization order follows declaration order, not init list order. Be aware of dependencies.

### 3. Use RAII

Acquire resources in constructors, release in destructors. The transpiler preserves RAII semantics.

### 4. Virtual Destructors

When using inheritance, declare base destructors as virtual to ensure proper cleanup:

```cpp
class Base {
public:
    virtual ~Base() {}  // Virtual ensures derived destructor is called
};
```

### 5. Const and Reference Members

Initialize const and reference members in the initialization list - they cannot be assigned in the constructor body.

### 6. Copy Constructors

Be explicit about copy constructors when managing resources to avoid shallow copies.

### 7. Constructor Delegation (C++11)

The transpiler supports delegating constructors where one constructor calls another:

```cpp
class Foo {
public:
    Foo() : Foo(0, 0) {}  // Delegates to Foo(int, int)
    Foo(int x, int y) : x(x), y(y) {}
private:
    int x, y;
};
```

## Testing

The transpiler includes comprehensive tests for constructor/destructor features:

- **25 base tests** covering inheritance, constructors, and destructors
- **5 additional Story #64 tests** for advanced scenarios:
  - Const member initialization
  - Reference member initialization
  - Entity system scenario
  - Container class scenario
  - Resource manager scenario

Run tests with:

```bash
cmake --build build
./build/InheritanceTest
```

Expected output:
```
✓ Passed: 30
✗ Failed: 0
```

## See Also

- [Architecture Documentation](ARCHITECTURE.md)
- [Epic #7: Advanced Constructor/Destructor Features](../EPICS.md#epic-7)
- [Story #64: Comprehensive Integration Testing](#)

---

**Document Version:** 1.0
**Last Updated:** 2025-12-08
**Epic:** #7 (Advanced Constructor/Destructor Features)
**Story:** #64 (Comprehensive Integration Testing)

🤖 Generated with [Claude Code](https://claude.com/claude-code)
