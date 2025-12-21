# Phase 9 Plan: Virtual Method Support (v2.2.0)

**Phase**: 9 of 17
**Roadmap**: `../.planning/ROADMAP.md`
**Brief**: `../.planning/BRIEF.md`
**Target Version**: v2.2.0
**Status**: PENDING
**Prerequisite**: None (parallel execution with Phase 8)

## Phase Goal

Integrate virtual method translation to enable object-oriented polymorphism in transpiled C code. Remove virtual method skip condition and activate existing infrastructure (VtableGenerator, VirtualMethodAnalyzer, VirtualCallTranslator) for complete virtual method support.

## Deliverables

### Source Code
- [ ] Remove virtual method skip (CppToCVisitor.cpp:129-131)
- [ ] Vtable struct generation for polymorphic classes
- [ ] Vtable initialization in constructors
- [ ] Virtual method call translation to vtable dispatch
- [ ] Virtual destructor chaining support
- [ ] Pure virtual function handling
- [ ] Covariant return type support

### Tests
- [ ] `tests/VirtualMethodIntegrationTest.cpp` (15+ tests)
  - Single virtual method dispatch
  - Multiple virtual methods
  - Virtual method overrides
  - Inherited virtual methods
  - Virtual destructors
  - Pure virtual methods (abstract classes)
  - Covariant return types
  - Multi-level inheritance
  - Diamond inheritance (virtual base)
  - Virtual call through base pointer
  - Virtual call through reference
  - Constructor vtable initialization
  - Virtual destructor cleanup
  - Mixed virtual/non-virtual methods
  - Performance: call overhead measurement

### CLI Integration
- [ ] Verify existing `--cpp-features={none,basic,full}` includes virtual methods

### Documentation
- [ ] Update `docs/CHANGELOG.md` for v2.2.0
- [ ] Update `README.md` with virtual method examples
- [ ] Update `website/src/pages/features.astro`

### Release
- [ ] Git-flow release v2.2.0

## Technical Design

### Architecture Overview

Virtual method translation follows the Itanium ABI model adapted for C:

```
C++ Class with Virtual Methods
             |
             v
    VirtualMethodAnalyzer
       (detect virtual methods,
        inherited methods,
        pure virtual)
             |
             v
    VtableGenerator
  (generate vtable struct with
   function pointers in order:
   destructor first, then methods)
             |
             v
    Vtable Initialization in Constructor
  (assign vptr in ctor body)
             |
             v
    VirtualCallTranslator
  (transform obj->method(args)
   to obj->vptr->method(obj, args))
             |
             v
    Generated C Code
  (vtable structs, initialized vptrs,
   indirect calls through vtable)
```

### Vtable Structure

#### Single Inheritance Example

**C++ Source**:
```cpp
class Shape {
public:
    virtual ~Shape() {}
    virtual double area() const = 0;
    virtual void draw() = 0;
};

class Circle : public Shape {
public:
    virtual double area() const { return 3.14159 * r * r; }
    virtual void draw() { printf("Circle\n"); }
private:
    double r;
};
```

**Generated C Header**:
```c
/* Vtable struct for Shape */
struct Shape_vtable {
    const struct __class_type_info *type_info;  /* RTTI type_info pointer */
    void (*destructor)(struct Shape *this);
    double (*area)(const struct Shape *this);
    void (*draw)(struct Shape *this);
};

/* Shape struct with vptr field */
struct Shape {
    struct Shape_vtable *vptr;
    /* base class fields would go here if Shape had bases */
};

/* Vtable struct for Circle (same layout as Shape) */
struct Circle_vtable {
    const struct __class_type_info *type_info;
    void (*destructor)(struct Circle *this);
    double (*area)(const struct Circle *this);
    void (*draw)(struct Circle *this);
};

/* Circle struct embeds Shape fields + own fields */
struct Circle {
    /* Embedded Shape fields (including vptr) */
    struct Shape_vtable *vptr;
    /* Circle's own fields */
    double r;
};
```

**Generated C Implementation**:
```c
/* Circle's area implementation */
double Circle_area(const struct Circle *this) {
    return 3.14159 * this->r * this->r;
}

/* Circle's draw implementation */
void Circle_draw(struct Circle *this) {
    printf("Circle\n");
}

/* Circle's destructor */
void Circle_destructor(struct Circle *this) {
    /* Circle-specific cleanup */
    /* Note: Destructor is NOT called automatically in C,
       must be called explicitly like: c->vptr->destructor(c); */
}

/* Circle's vtable instance (global) */
struct Circle_vtable Circle_vtable_instance = {
    .type_info = &Circle_type_info,
    .destructor = (void (*)(struct Shape *))Circle_destructor,
    .area = (double (*)(const struct Shape *))Circle_area,
    .draw = (void (*)(struct Shape *))Circle_draw,
};

/* Circle constructor initializes vptr */
void Circle_constructor(struct Circle *this, double radius) {
    this->vptr = (struct Shape_vtable *)&Circle_vtable_instance;
    this->r = radius;
}
```

**Generated C Usage**:
```c
/* Virtual call through base class pointer */
struct Shape *shape = (struct Shape *)&circle;
double area = shape->vptr->area(shape);  /* Virtual dispatch */
shape->vptr->draw(shape);                 /* Virtual dispatch */
```

### Multi-Level Inheritance Example

**C++ Source**:
```cpp
class Animal {
public:
    virtual ~Animal() {}
    virtual void speak() = 0;
};

class Mammal : public Animal {
public:
    virtual void speak() { printf("Mammal sound\n"); }
    virtual void nurse() { printf("Nursing\n"); }
};

class Dog : public Mammal {
public:
    virtual void speak() { printf("Woof\n"); }
    virtual void fetch() { printf("Fetching\n"); }
};
```

**Vtable Inheritance Chain**:
```c
/* Animal's vtable - defines base slots */
struct Animal_vtable {
    const struct __class_type_info *type_info;
    void (*destructor)(struct Animal *);
    void (*speak)(struct Animal *);
};

/* Mammal's vtable - overrides speak, adds nurse */
struct Mammal_vtable {
    const struct __class_type_info *type_info;
    void (*destructor)(struct Mammal *);
    void (*speak)(struct Mammal *);      /* Override Animal::speak */
    void (*nurse)(struct Mammal *);      /* New slot */
};

/* Dog's vtable - overrides speak, inherits nurse, adds fetch */
struct Dog_vtable {
    const struct __class_type_info *type_info;
    void (*destructor)(struct Dog *);
    void (*speak)(struct Dog *);         /* Override Mammal::speak */
    void (*nurse)(struct Dog *);         /* Inherited from Mammal (same slot) */
    void (*fetch)(struct Dog *);         /* New slot */
};

/* Key insight: Overridden methods occupy SAME SLOT in derived vtable */
```

### Virtual Inheritance (Diamond Problem)

**C++ Source**:
```cpp
class Base {
public:
    virtual void foo() {}
};

class Left : virtual public Base {
public:
    virtual void left_method() {}
};

class Right : virtual public Base {
public:
    virtual void right_method() {}
};

class Diamond : public Left, public Right {
public:
    virtual void foo() {}  /* Override Base::foo */
};
```

**Generated C Handling**:
```c
/* Virtual base offset tables for diamond inheritance */
struct Diamond {
    /* Left part with Left's vptr */
    struct Left_vtable *left_vptr;
    /* Right part with Right's vptr */
    struct Right_vtable *right_vptr;
    /* Virtual base offset table for Left */
    int *left_vbptr;
    /* Virtual base offset table for Right */
    int *right_vbptr;
    /* Single copy of Base (virtual base) */
    struct Base base;
};

/* VtableGenerator::generateVtableWithVirtualBaseOffsets() handles this */
```

### Virtual Method Call Translation

#### Direct Call Translation

**C++ Source**:
```cpp
Circle circle(5.0);
double a = circle.area();  /* Direct call on object */
```

**Generated C**:
```c
struct Circle circle;
Circle_constructor(&circle, 5.0);
double a = circle.vptr->area((struct Shape *)&circle);
```

#### Through Base Pointer (Polymorphic Dispatch)

**C++ Source**:
```cpp
Shape *shape = new Circle(5.0);
double a = shape->area();  /* Virtual dispatch */
delete shape;              /* Virtual destructor */
```

**Generated C**:
```c
struct Circle *circle = (struct Circle *)malloc(sizeof(struct Circle));
Circle_constructor(circle, 5.0);

struct Shape *shape = (struct Shape *)circle;
double a = shape->vptr->area(shape);  /* Virtual dispatch through vptr */

/* Virtual destructor call - must be explicit in C */
shape->vptr->destructor(shape);
free(shape);
```

#### Reference Parameters

**C++ Source**:
```cpp
void process(Shape& shape) {
    shape.draw();  /* Virtual call through reference */
}
```

**Generated C**:
```c
void process(struct Shape *shape) {  /* Reference translated to pointer */
    shape->vptr->draw(shape);  /* Virtual call */
}
```

### Key Implementation Steps

#### Step 1: Remove Skip Condition (CppToCVisitor.cpp)

**Current Code (lines 129-131)**:
```cpp
bool CppToCVisitor::VisitCXXMethodDecl(CXXMethodDecl *MD) {
  // Edge case 1: Skip virtual methods (Phase 1 POC scope)
  if (MD->isVirtual()) {
    llvm::outs() << "Skipping virtual method: " << MD->getQualifiedNameAsString() << "\n";
    return true;
  }
```

**After Removal**:
```cpp
bool CppToCVisitor::VisitCXXMethodDecl(CXXMethodDecl *MD) {
  // Edge case 1: Skip implicit methods (compiler-generated)
  if (MD->isImplicit()) {
    return true;
  }

  // Edge case 2: Skip constructors/destructors (handled separately)
  if (isa<CXXConstructorDecl>(MD) || isa<CXXDestructorDecl>(MD)) {
    return true;
  }

  /* Process virtual methods along with non-virtual methods */

  // Translate method body
  std::string methodCode = translateMethodBody(MD);
```

#### Step 2: Vtable Struct Generation

**VtableGenerator::generateVtableStruct(Record)**:
- Input: CXXRecordDecl for polymorphic class
- Output: C struct definition with function pointers
- Uses: VirtualMethodAnalyzer to detect virtual methods
- Uses: OverrideResolver to determine method order
- Includes: Destructor first, then virtual methods in order

**Integration Point**: Call during VisitCXXRecordDecl when polymorphic

```cpp
bool CppToCVisitor::VisitCXXRecordDecl(CXXRecordDecl *D) {
  // ... existing code ...

  // Story #168: Generate vtable struct for polymorphic classes
  if (VirtualAnalyzer.isPolymorphic(D)) {
    VtableGenerator vtableGen(Context, VirtualAnalyzer, &overrideResolver);
    std::string vtableCode = vtableGen.generateVtableStruct(D);
    emitC(vtableCode);  // Output vtable struct definition

    // Also generate vtable instance (global variable)
    std::string vtableInstance = generateVtableInstance(D);
    emitC(vtableInstance);
  }
```

#### Step 3: Constructor Vtable Initialization

When polymorphic class constructor is generated, inject vptr initialization:

```cpp
void generateConstructorBody(CXXConstructorDecl *Ctor) {
  // ... existing constructor code ...

  CXXRecordDecl *Class = Ctor->getParent();
  if (VirtualAnalyzer.isPolymorphic(Class)) {
    // Inject: this->vptr = &ClassName_vtable_instance;
    std::string vptr_init =
        "  " + classNameC(Class) + "_vptr = &" +
        classNameC(Class) + "_vtable_instance;\n";
    ctorBody.insert(ctorBody.begin(), vptr_init);
  }
}
```

#### Step 4: Virtual Call Translation

**In VisitCXXMemberCallExpr**:
- Detect if call is to virtual method (CXXMethodDecl::isVirtual())
- Transform: `obj->method(args)` to `obj->vptr->method(obj, args)`
- Use VirtualCallTranslator for detection and translation

```cpp
bool CppToCVisitor::VisitCXXMemberCallExpr(CXXMemberCallExpr *CE) {
  const CXXMethodDecl *Method = CE->getMethodDecl();

  if (VirtualCallTranslator.isVirtualCall(CE)) {
    // Virtual call - use vtable dispatch
    std::string callCode = VirtualCallTranslator.translateVirtualCall(CE);
    // obj->vptr->method(obj, args)
    emitC(callCode);
  } else {
    // Non-virtual call - direct function call
    std::string callCode = translateDirectCall(CE);
    emitC(callCode);
  }

  return true;
}
```

#### Step 5: Virtual Destructor Chaining

Virtual destructors must call derived class destructors:

**C++ Source**:
```cpp
class Base {
    virtual ~Base() { /* base cleanup */ }
};

class Derived : public Base {
    ~Derived() { /* derived cleanup */ }
};
```

**Generated C**:
```c
void Derived_destructor(struct Derived *this) {
    /* Derived cleanup first */

    /* Then call base destructor through vptr
       Note: Derived's vptr points to Derived's vtable,
       which has Base's destructor slot pointing to
       Derived_destructor (virtual) */
    /* Base destructor logic is inlined, not called again */
}

/* Destructor calling is programmer's responsibility in C: */
shape->vptr->destructor(shape);
```

**Key Insight**: In C, must call destructor explicitly. Use RAII pattern or cleanup handlers to ensure destruction.

#### Step 6: Pure Virtual Function Handling

**For Abstract Classes**:
```cpp
class AbstractShape {
    virtual ~AbstractShape() {}
    virtual void draw() = 0;  /* Pure virtual */
};
```

**Generated C**:
```c
struct AbstractShape_vtable {
    const struct __class_type_info *type_info;
    void (*destructor)(struct AbstractShape *);
    void (*draw)(struct AbstractShape *);  /* Will be NULL for abstract methods in base */
};

/* Constructor should not be called directly - it's abstract
   We can't prevent this at compile time in C, but:
   1. Don't provide constructor for abstract classes
   2. Generate runtime check for abstract instantiation
   3. Document as abstract in generated code
*/

/* Optional: Runtime check in constructor */
void AbstractShape_check_abstract(void) {
    /* Generate compile error or runtime error */
    static_assert(0, "Cannot instantiate abstract class AbstractShape");
}
```

#### Step 7: Covariant Return Types

**C++ Source**:
```cpp
class Base {
    virtual Base* clone() = 0;
};

class Derived : public Base {
    virtual Derived* clone() { return new Derived(*this); }
};
```

**Generated C** (requires careful pointer casting):
```c
/* Both vtables have same slot for clone, but with different return types */
struct Base_vtable {
    struct Base* (*clone)(struct Base *);
};

struct Derived_vtable {
    /* Same slot, but function pointer accepts Derived* */
    struct Derived* (*clone)(struct Derived *);
};

/* At call site: */
struct Base *b = /* some polymorphic object */;
struct Base *cloned = b->vptr->clone(b);  /* Returns Base*, safe */

struct Derived *d = (struct Derived *)b;
struct Derived *cloned_d = d->vptr->clone(d);  /* Returns Derived*, type-safe */
```

### Test Cases (15+)

#### Tier 1: Single Inheritance (5 tests)

1. **SimpleVirtualMethod**
   - Single class with one virtual method
   - Call through object
   - Verify vtable generated and method called correctly

2. **MultipleVirtualMethods**
   - Single class with 3+ virtual methods
   - Verify all methods in vtable in correct order
   - Call each method, verify correct dispatch

3. **VirtualMethodOverride**
   - Base class with virtual method
   - Derived class overrides method
   - Call through base pointer dispatches to derived
   - Verify vtable slot reused (same position)

4. **InheritedVirtualMethod**
   - Base class with virtual method
   - Derived class does NOT override (inherits)
   - Call through derived object dispatches to base implementation
   - Verify vtable inherits slot from base

5. **MixedVirtualNonVirtual**
   - Class with mix of virtual and non-virtual methods
   - Non-virtual methods called directly (no vtable)
   - Virtual methods use vtable
   - Verify both call types work correctly

#### Tier 2: Multi-Level Inheritance (3 tests)

6. **MultiLevelInheritance**
   - A -> B -> C inheritance chain
   - Each level overrides virtual method
   - Call through base (A*) dispatches to C
   - Verify vtable chain correct

7. **MultiLevelWithNewMethod**
   - A (virtual foo)
   - B extends A (overrides foo, adds virtual bar)
   - C extends B (overrides foo, overrides bar)
   - Call through A*: foo works
   - Call through B*: bar works
   - Verify vtable slots correct

8. **MultiLevelPartialOverride**
   - A (virtual foo, virtual bar)
   - B (overrides foo, inherits bar)
   - C (inherits foo, overrides bar)
   - Verify slots preserved across levels

#### Tier 3: Virtual Destructors (2 tests)

9. **VirtualDestructor**
   - Class with virtual destructor
   - Destructor cleanup code runs
   - Verify destructor called through vptr
   - (Note: C doesn't call destructors automatically, must be explicit)

10. **VirtualDestructorInheritance**
    - Base has virtual destructor
    - Derived overrides destructor
    - Call through base pointer calls derived destructor
    - Both cleanups execute in correct order

#### Tier 4: Abstract Classes & Pure Virtual (2 tests)

11. **PureVirtualMethod**
    - Abstract base class with pure virtual method = 0
    - Derived class implements pure virtual
    - Cannot instantiate abstract base (no constructor generated)
    - Can call through pointer to derived object

12. **MultipleAbstractMethods**
    - Abstract base with 3+ pure virtual methods
    - Concrete derived implements all
    - Can instantiate derived, call all methods polymorphically

#### Tier 5: Advanced Cases (3 tests)

13. **PolymorphicThroughReference**
    - Function takes reference to base class
    - Calls virtual method through reference
    - Verify reference translated to pointer, dispatch works

14. **PolymorphicThroughPointer**
    - Function takes pointer to base class
    - Creates derived object, passes as base pointer
    - Calls virtual method, verifies polymorphic dispatch

15. **CovariantReturnType**
    - Base::clone() returns Base*
    - Derived::clone() returns Derived* (covariant)
    - Call through base pointer returns Base*
    - Call through derived pointer returns Derived*
    - Verify type safety

### Verification Criteria

- [ ] Virtual method calls dispatch correctly at runtime
- [ ] Inheritance hierarchies have correct vtable layout
- [ ] Virtual destructors call chain correctly
- [ ] Pure virtual functions prevent instantiation (at least documented)
- [ ] Covariant return types handled correctly
- [ ] Multi-level inheritance dispatch works
- [ ] Virtual inheritance (diamond) vtable offsets correct
- [ ] 15+ tests passing (100%)
- [ ] Generated C code compiles without errors
- [ ] Virtual calls match C ABI conventions
- [ ] Performance overhead minimal (<5% for virtual calls)

## Dependencies

- **Requires**: None (Phase 8 not required as dependency)
- **Infrastructure**:
  - VtableGenerator.cpp (vtable struct generation)
  - VirtualMethodAnalyzer.h (virtual method detection)
  - VirtualCallTranslator.h (call translation)
  - VirtualDestructorHandler.h (destructor support)
  - OverrideResolver.cpp (method override resolution)
  - VirtualInheritanceAnalyzer.cpp (virtual inheritance)
  - TypeInfoGenerator.cpp (RTTI type_info)

**Parallel Execution**: ✅ Can run with Phases 6, 7, 8, 11, 12, 13 (independent)

## Implementation Notes

### Naming Conventions

For a class `MyClass`:
- Vtable struct: `MyClass_vtable`
- Vtable instance: `MyClass_vtable_instance` (global)
- vptr field: `vptr` (injected by VptrInjector)
- Destructor method: `MyClass_destructor`
- Virtual method: `MyClass_methodName`

### Itanium ABI Compliance

The implementation follows Itanium ABI vtable layout:
- vtable[-1] = type_info pointer (in C, placed at offset 0)
- vtable[0] = destructor
- vtable[1..N] = virtual methods in declaration order

### C Code Generation Issues

**Challenge 1: No Implicit Destructor Calls**
- C++ calls destructors automatically
- Generated C requires explicit calls: `ptr->vptr->destructor(ptr);`
- Solution: Document this, use RAII-like patterns with cleanup functions

**Challenge 2: Abstract Classes**
- C++ prevents instantiation of abstract classes
- Generated C can't enforce this at compile-time
- Solution: Don't generate constructor for abstract classes, add static assertion

**Challenge 3: Virtual Base Offsets**
- Virtual inheritance requires offset tables
- Handled by VirtualInheritanceAnalyzer
- Must be initialized in constructors

### Performance Considerations

**Vtable Lookup Overhead**:
- Direct call: `shape.draw()` → 1 dereference (vptr load)
- Virtual call: `shape_ptr->vptr->draw(shape_ptr)` → 2 dereferences (vptr load + vtable lookup)
- Overhead: ~1-2 dereferences per virtual call
- Modern CPU branch prediction handles this well

**Memory Overhead**:
- Each polymorphic object: +8 bytes for vptr (64-bit)
- Each polymorphic class: +1 global vtable instance
- Overall overhead: <5% for typical OOP programs

## Integration with Existing Components

### CppToCVisitor Integration

```cpp
class CppToCVisitor : public RecursiveASTVisitor<CppToCVisitor> {
private:
    VirtualMethodAnalyzer VirtualAnalyzer;        // Story #167
    VtableGenerator VtableGen;                    // Story #168
    VirtualCallTranslator VirtualCallTrans;       // Story #172
    VirtualDestructorHandler VirtualDtorHandler;  // Story #175
};
```

### Constructor/Destructor Integration

- CppToCVisitor::VisitCXXConstructorDecl injects vptr initialization
- CppToCVisitor::VisitCXXDestructorDecl marks as virtual if needed
- ConstructorSplitter integrates vptr init with other ctor code

### Override Resolution Integration

- OverrideResolver::resolveVtableLayout() determines method slots
- Used by VtableGenerator::getVtableMethodOrder()
- Ensures correct slot assignment for overridden methods

## Success Criteria Summary

| Criterion | Status |
|-----------|--------|
| Remove virtual method skip | Pending |
| VtableGenerator integration | Pending |
| Vtable initialization in constructors | Pending |
| Virtual call translation | Pending |
| Virtual destructor support | Pending |
| Pure virtual function handling | Pending |
| 15+ tests passing | Pending |
| Generated C compiles | Pending |
| No linting errors | Pending |
| Documentation complete | Pending |

## Next Steps

1. **Code Review**: Review existing virtual method infrastructure
   - VirtualMethodAnalyzer.cpp implementation
   - VtableGenerator.cpp current state
   - VirtualCallTranslator.cpp availability
   - OverrideResolver.cpp integration

2. **Design Review**: Validate vtable layout matches Itanium ABI

3. **Test-Driven Development**:
   - Write failing tests first
   - Implement features to pass tests
   - Refactor for clarity

4. **Integration Testing**:
   - Verify integration with CppToCVisitor
   - Test with inheritance hierarchies
   - Benchmark virtual call overhead

5. **Documentation**:
   - Update CHANGELOG.md
   - Add examples to README.md
   - Update website features

6. **Release**:
   - Tag v2.2.0
   - Update git-flow release

---

**Created**: 2025-12-20
**Status**: DRAFT (Ready for implementation)
**Prepared for**: Phase 9 execution
