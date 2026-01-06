# ConstructorHandler Specification

## Responsibility

Translates C++ constructors into C initialization functions. This handler is responsible for:
- Converting constructor declarations to initialization functions
- Generating appropriate function names (`ClassName__ctor`)
- Handling member initializer lists
- Managing constructor overloading
- Translating constructor bodies
- Handling default constructors
- Coordinating with memory allocation patterns (stack vs heap)

## AST Nodes Processed

### Primary Nodes
- `clang::CXXConstructorDecl` - C++ constructor declarations
- `clang::CXXCtorInitializer` - Member initializer list entries

### Related Nodes (processed via traversal)
- `clang::ParmVarDecl` - Constructor parameters
- `clang::MemberExpr` - Field access in constructor body
- `clang::CXXConstructExpr` - Construction of member objects
- `clang::InitListExpr` - Brace initialization

## Translation Strategy

### Basic Translation Rules

1. **Default Constructor**
   ```cpp
   class Point {
     int x, y;
     Point() : x(0), y(0) { }
   };

   ↓

   void Point__ctor(struct Point* this) {
     this->x = 0;
     this->y = 0;
   }
   ```

2. **Parameterized Constructor**
   ```cpp
   class Point {
     int x, y;
     Point(int x, int y) : x(x), y(y) { }
   };

   ↓

   void Point__ctor(struct Point* this, int x, int y) {
     this->x = x;
     this->y = y;
   }
   ```

3. **Constructor Overloading**
   ```cpp
   class Point {
     Point() : x(0), y(0) { }
     Point(int v) : x(v), y(v) { }
     Point(int x, int y) : x(x), y(y) { }
   };

   ↓

   void Point__ctor__default(struct Point* this) {
     this->x = 0;
     this->y = 0;
   }

   void Point__ctor__int(struct Point* this, int v) {
     this->x = v;
     this->y = v;
   }

   void Point__ctor__int_int(struct Point* this, int x, int y) {
     this->x = x;
     this->y = y;
   }
   ```

4. **Member Initializer List**
   ```cpp
   class Complex {
     int a;
     double b;
     const int c;
     Complex(int a, double b, int c) : a(a), b(b), c(c) { }
   };

   ↓

   void Complex__ctor(struct Complex* this, int a, double b, int c) {
     // Initializer list → assignments
     this->a = a;
     this->b = b;
     this->c = c;  // const member must be initialized here

     // Constructor body (empty in this case)
   }
   ```

### Constructor Usage Patterns

**Stack Allocation**:
```cpp
Point p(10, 20);

↓

struct Point p;
Point__ctor(&p, 10, 20);
```

**Heap Allocation**:
```cpp
Point* p = new Point(10, 20);

↓

struct Point* p = malloc(sizeof(struct Point));
Point__ctor(p, 10, 20);
```

**Return by Value**:
```cpp
Point createPoint() {
  return Point(5, 10);
}

↓

struct Point createPoint(void) {
  struct Point __result;
  Point__ctor(&__result, 5, 10);
  return __result;
}
```

## Dependencies

### Required Handlers (must run before)
- **RecordHandler**: Need struct definitions
- **FileOriginFilter**: Determine which constructors belong to current file
- **TypeTranslator**: Translate parameter types

### Optional Handlers (may interact with)
- **MemberAccessHandler**: For member object construction in initializer list
- **ExpressionTranslator**: For constructor body expressions
- **StatementTranslator**: For constructor body statements

## Algorithm

### Phase 1: Constructor Discovery

```
For each CXXConstructorDecl in C++ AST:
  1. Check FileOriginFilter: Does this belong to current file?
     - If NO: Skip (external constructor)
     - If YES: Continue

  2. Collect constructor information:
     - Parent class (RecordDecl)
     - Parameter list
     - Member initializer list (CXXCtorInitializer nodes)
     - Constructor body
     - Is it default constructor? (no params)
     - Is it copy constructor? (param is const ClassName&)
     - Is it move constructor? (param is ClassName&&)

  3. Check for overloading:
     - Look for other constructors in same class
     - If found: Will need name mangling
```

### Phase 2: Name Generation

```
For each constructor:
  1. Generate base name:
     base = ClassName + "__ctor"
     Example: "Point__ctor"

  2. Check for overloads:
     If only one constructor:
       If it's default constructor (no params):
         finalName = base + "__default"
       Else:
         finalName = base

     If multiple constructors:
       If default constructor (no params):
         finalName = base + "__default"
       Else:
         suffix = generateOverloadSuffix(parameterTypes)
         finalName = base + suffix
         Example: "Point__ctor__int_int"

  3. Handle nested classes:
     If constructor belongs to nested class:
       base = OuterClass + "__" + InnerClass + "__ctor"
       Example: "Player__Inventory__ctor"

  4. Register name mapping:
     Map CXXConstructorDecl → C function name
     Store for expression translation
```

### Phase 3: Parameter Translation

```
For each constructor:
  1. Create 'this' parameter:
     thisParam = ParmVarDecl("this", struct ClassName*)
     // Note: Never const, because we're initializing

  2. Translate existing parameters:
     For each original parameter:
       - Translate parameter type via TypeTranslator
       - Preserve parameter name
       - Handle special cases:
         * const ClassName& → const struct ClassName*  (copy ctor)
         * ClassName&& → struct ClassName*  (move ctor)
       - Create C ParmVarDecl

  3. Build final parameter list:
     params = [thisParam] + [translated original params]
```

### Phase 4: Member Initializer List Translation

```
For each constructor:
  1. Collect all CXXCtorInitializer nodes:
     initList = constructor->getInitializers()

  2. Sort initializers by member declaration order:
     // IMPORTANT: C++ initializes members in declaration order,
     // not in the order they appear in initializer list!
     sortedInits = sortByMemberDeclOrder(initList)

  3. For each initializer:
     If initializing a field:
       fieldName = init->getMember()->getName()
       initExpr = init->getInit()

       Translate to assignment:
       this->fieldName = translatedExpr

       Add to initialization statements

     If initializing a base class:
       // Not in Phase 4 (no inheritance yet)
       Report error: "Base class initialization not supported"

     If delegating constructor:
       // Call to another constructor of same class
       otherCtorName = translateConstructor(delegatedCtor)

       Generate call:
       ClassName__ctor__variant(this, args...)

       Add to initialization statements

  4. Handle members NOT in initializer list:
     For each member field in struct:
       If NOT in initializer list:
         If member has default value:
           Add initialization: this->field = defaultValue
         Else if member is primitive:
           // Could zero-initialize or leave uninitialized
           // Decision: Document in config
         Else if member is struct:
           // Call default constructor if exists
           MemberType__ctor__default(&this->field)
```

### Phase 5: Constructor Body Translation

```
For each constructor:
  1. Get constructor body (CompoundStmt)

  2. Translate all statements in body:
     Delegate to StatementTranslator

     Special handling:
     - this->field access: Keep as-is
     - Member function calls: Delegate to MemberAccessHandler
     - Member object construction: Already handled in initializer list

  3. Build initialization sequence:
     finalBody = [
       // Member initializer list statements (Phase 4)
       ...initializerStatements,

       // Constructor body statements
       ...translatedBodyStatements
     ]

  4. Create C CompoundStmt with finalBody
```

### Phase 6: C AST Construction

```
For each constructor:
  1. Create C FunctionDecl:
     FunctionDecl::Create(
       C_Context,
       C_TU,
       SourceLocation,
       DeclarationName,         // Generated name (ClassName__ctor...)
       void,                    // Return type: always void
       translatedParams         // 'this' + original params
     )

  2. Set function body:
     Set body to CompoundStmt from Phase 5

  3. Add to C translation unit:
     C_TU->addDecl(FunctionDecl)
```

### Phase 7: Constructor Call Site Translation

```
When encountering CXXConstructExpr during expression translation:
  1. Determine which constructor is being called:
     ctorDecl = constructExpr->getConstructor()

  2. Look up translated constructor name:
     ctorName = getTranslatedName(ctorDecl)

  3. Generate appropriate initialization:

     If stack allocation:
       struct ClassName obj;
       ClassName__ctor__variant(&obj, args...);

     If temporary:
       struct ClassName __temp;
       ClassName__ctor__variant(&__temp, args...);
       // Use __temp

     If return value:
       struct ClassName __result;
       ClassName__ctor__variant(&__result, args...);
       return __result;
```

## C++ Example

```cpp
// point.h
namespace Math {
  class Point {
  private:
    int x;
    int y;

  public:
    // Default constructor
    Point() : x(0), y(0) {
      // Body can have additional logic
    }

    // Parameterized constructor
    Point(int x, int y) : x(x), y(y) { }

    // Single value constructor
    Point(int v) : x(v), y(v) { }

    // Copy constructor
    Point(const Point& other) : x(other.x), y(other.y) { }
  };

  class Line {
  private:
    Point start;
    Point end;

  public:
    // Constructor with member object initialization
    Line(int x1, int y1, int x2, int y2)
      : start(x1, y1), end(x2, y2) { }
  };
}
```

## C Example

```c
// point.h
struct Math__Point;
struct Math__Line;

// Constructor declarations
void Math__Point__ctor__default(struct Math__Point* this);
void Math__Point__ctor__int_int(struct Math__Point* this, int x, int y);
void Math__Point__ctor__int(struct Math__Point* this, int v);
void Math__Point__ctor__copy(struct Math__Point* this, const struct Math__Point* other);
void Math__Line__ctor(struct Math__Line* this, int x1, int y1, int x2, int y2);

// point.c
#include "point.h"

struct Math__Point {
  int x;
  int y;
};

struct Math__Line {
  struct Math__Point start;
  struct Math__Point end;
};

void Math__Point__ctor__default(struct Math__Point* this) {
  // Member initializer list
  this->x = 0;
  this->y = 0;

  // Constructor body (empty in original)
}

void Math__Point__ctor__int_int(struct Math__Point* this, int x, int y) {
  this->x = x;
  this->y = y;
}

void Math__Point__ctor__int(struct Math__Point* this, int v) {
  this->x = v;
  this->y = v;
}

void Math__Point__ctor__copy(struct Math__Point* this, const struct Math__Point* other) {
  this->x = other->x;
  this->y = other->y;
}

void Math__Line__ctor(struct Math__Line* this, int x1, int y1, int x2, int y2) {
  // Initialize member objects using their constructors
  Math__Point__ctor__int_int(&this->start, x1, y1);
  Math__Point__ctor__int_int(&this->end, x2, y2);
}

// Usage example
void example(void) {
  // Stack allocation
  struct Math__Point p1;
  Math__Point__ctor__default(&p1);

  struct Math__Point p2;
  Math__Point__ctor__int_int(&p2, 10, 20);

  // Heap allocation
  struct Math__Point* p3 = malloc(sizeof(struct Math__Point));
  Math__Point__ctor__int(&p3, 5);

  // Copy construction
  struct Math__Point p4;
  Math__Point__ctor__copy(&p4, &p2);

  // Member object construction
  struct Math__Line line;
  Math__Line__ctor(&line, 0, 0, 100, 100);
}
```

## Test Cases

### Unit Tests

1. **test_default_constructor**
   ```cpp
   class C { C() { } };
   // → void C__ctor__default(struct C* this) { }
   ```

2. **test_parameterized_constructor**
   ```cpp
   class C { C(int x) : val(x) { } int val; };
   // → void C__ctor(struct C* this, int x) { this->val = x; }
   ```

3. **test_multiple_params**
   ```cpp
   class C { C(int x, double y) : a(x), b(y) { } int a; double b; };
   // → void C__ctor(struct C* this, int x, double y) { this->a = x; this->b = y; }
   ```

4. **test_constructor_overloading**
   ```cpp
   class C {
     C() { }
     C(int x) { }
   };
   // → void C__ctor__default(struct C* this) { }
   // → void C__ctor__int(struct C* this, int x) { }
   ```

5. **test_initializer_list**
   ```cpp
   class C {
     int a, b;
     C(int x) : a(x), b(x * 2) { }
   };
   // → void C__ctor(struct C* this, int x) {
   //     this->a = x;
   //     this->b = x * 2;
   //   }
   ```

6. **test_initializer_list_order**
   ```cpp
   class C {
     int a, b;
     C(int x) : b(x), a(b + 1) { }  // Tricky: 'a' initialized before 'b' (decl order)
   };
   // → void C__ctor(struct C* this, int x) {
   //     this->a = this->b + 1;  // WRONG if b not set yet!
   //     this->b = x;
   //   }
   // CORRECT:
   // → void C__ctor(struct C* this, int x) {
   //     this->a = this->b + 1;  // Initialize in declaration order
   //     this->b = x;
   //   }
   ```

7. **test_member_object_construction**
   ```cpp
   class Inner { Inner(int x) : val(x) { } int val; };
   class Outer {
     Inner inner;
     Outer(int x) : inner(x) { }
   };
   // → void Outer__ctor(struct Outer* this, int x) {
   //     Inner__ctor(&this->inner, x);
   //   }
   ```

8. **test_constructor_body**
   ```cpp
   class C {
     int val;
     C(int x) : val(x) {
       val *= 2;  // Body modifies after initialization
     }
   };
   // → void C__ctor(struct C* this, int x) {
   //     this->val = x;
   //     this->val *= 2;
   //   }
   ```

9. **test_copy_constructor**
   ```cpp
   class C {
     int val;
     C(const C& other) : val(other.val) { }
   };
   // → void C__ctor__copy(struct C* this, const struct C* other) {
   //     this->val = other->val;
   //   }
   ```

10. **test_delegating_constructor**
    ```cpp
    class C {
      int x, y;
      C() : C(0, 0) { }
      C(int x, int y) : x(x), y(y) { }
    };
    // → void C__ctor__default(struct C* this) {
    //     C__ctor__int_int(this, 0, 0);
    //   }
    // → void C__ctor__int_int(struct C* this, int x, int y) {
    //     this->x = x;
    //     this->y = y;
    //   }
    ```

### Integration Tests

1. **test_with_record_handler**
   - Ensure struct definition matches constructor

2. **test_with_expression_translator**
   - Ensure constructor calls translate correctly

3. **test_stack_allocation**
   - Test CXXConstructExpr for stack objects

## Edge Cases

### 1. Const Members

```cpp
class C {
  const int id;
  C(int id) : id(id) { }
};
```

**Solution**: Initialize in initializer list (required)
```c
struct C {
  const int id;
};

void C__ctor(struct C* this, int id) {
  // In C99/C11, can't assign to const after declaration
  // Must use compound literal or memcpy trick
  *(int*)&this->id = id;  // Cast away const (ugly but works)
}
```

**Better**: Warn user that const members are tricky in C.

### 2. Reference Members

```cpp
class C {
  int& ref;
  C(int& r) : ref(r) { }
};
```

**Solution**: Convert reference to pointer
```c
struct C {
  int* ref;
};

void C__ctor(struct C* this, int* r) {
  this->ref = r;
}
```

### 3. Default Member Initializers (C++11)

```cpp
class C {
  int x = 42;  // Default member initializer
  int y;
  C(int y) : y(y) { }  // x gets 42 automatically
};
```

**Solution**: Inject default initialization
```c
void C__ctor(struct C* this, int y) {
  this->x = 42;  // From default member initializer
  this->y = y;   // From initializer list
}
```

### 4. Array Members

```cpp
class C {
  int arr[10];
  C() {
    for (int i = 0; i < 10; i++) arr[i] = i;
  }
};
```

**Solution**: Handle in constructor body
```c
void C__ctor__default(struct C* this) {
  for (int i = 0; i < 10; i++) {
    this->arr[i] = i;
  }
}
```

### 5. Explicit Constructors

```cpp
class C {
  explicit C(int x) { }
};
```

**Solution**: Drop `explicit` (no implicit conversion in C)
```c
void C__ctor(struct C* this, int x) { }
```

**Note**: Caller must explicitly construct. No issue in C.

### 6. Uniform Initialization

```cpp
C obj{10, 20};  // Brace initialization
```

**Solution**: Translate to constructor call
```c
struct C obj;
C__ctor(&obj, 10, 20);
```

### 7. Aggregate Initialization

```cpp
class C {
  int x, y;
};
C obj = {10, 20};  // No constructor defined
```

**Solution**: Keep as aggregate initialization
```c
struct C obj = {10, 20};  // No constructor call needed
```

**Note**: Only if no constructors defined at all.

### 8. Placement New

```cpp
void* mem = malloc(sizeof(C));
C* obj = new (mem) C(10);
```

**Solution**: Separate allocation and initialization
```c
void* mem = malloc(sizeof(struct C));
C__ctor((struct C*)mem, 10);
struct C* obj = (struct C*)mem;
```

### 9. Constructor with Try-Catch

```cpp
class C {
  C() try : x(compute()) {
    // Body
  } catch (...) {
    // Handle exception
  }
  int x;
};
```

**Solution**: No exceptions in C
```c
void C__ctor__default(struct C* this) {
  this->x = compute();
  // No try-catch
}
```

**Note**: Exception handling not supported.

### 10. Inherited Constructors (C++11)

```cpp
class Base {
  Base(int x) { }
};

class Derived : public Base {
  using Base::Base;  // Inherit constructors
};
```

**Solution**: Not in Phase 4 (no inheritance)
```
ERROR: Inherited constructors not supported (no inheritance in Phase 4)
```

### 11. Variadic Template Constructors

```cpp
template<typename... Args>
class C {
  C(Args... args) { }
};
```

**Solution**: Monomorphize for each usage
```c
// For C<int, double>
void C__int_double__ctor(struct C__int_double* this, int arg1, double arg2) { }
```

### 12. Constructor with Designated Initializers (C++20)

```cpp
struct C {
  int x, y;
  C() : x{.value = 10}, y{.value = 20} { }
};
```

**Solution**: Flatten designated initializers
```c
void C__ctor__default(struct C* this) {
  this->x = 10;
  this->y = 20;
}
```

## Implementation Checklist

- [ ] Create ConstructorHandler class with Chain of Responsibility interface
- [ ] Implement CXXConstructorDecl visitor
- [ ] Implement constructor name generation
- [ ] Implement overload detection and name mangling
- [ ] Implement `this` parameter creation (non-const)
- [ ] Implement parameter list translation
- [ ] Implement member initializer list collection
- [ ] Implement initializer list sorting by declaration order
- [ ] Implement field initialization translation
- [ ] Implement delegating constructor translation
- [ ] Implement default member initializer injection
- [ ] Implement constructor body translation
- [ ] Implement CXXConstructExpr translation (call sites)
- [ ] Handle stack vs heap allocation patterns
- [ ] Write unit tests for all test cases
- [ ] Write integration tests with RecordHandler and ExpressionTranslator
- [ ] Document all edge cases
- [ ] Add error handling for unsupported features

## Success Criteria

1. All constructors translated to `__ctor` functions
2. Default constructors named `__ctor__default`
3. Overloaded constructors have unique names via mangling
4. Member initializer lists translate to assignments in correct order
5. Member objects constructed via their own constructors
6. Constructor bodies execute after initialization
7. Copy constructors translate correctly
8. Delegating constructors work correctly
9. All 10 unit tests pass
10. Integration tests pass with RecordHandler and ExpressionTranslator
11. All 12 edge cases handled or documented
12. Constructor call sites (CXXConstructExpr) translate correctly
