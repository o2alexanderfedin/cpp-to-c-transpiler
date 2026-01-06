# RecordHandler Specification

## Responsibility

Translates C++ class and struct declarations into C struct declarations. This handler is responsible for:
- Converting C++ classes to C structs
- Flattening access specifiers (public/private/protected → all public)
- Handling nested class definitions
- Managing field declarations and their types
- Preserving field layout and alignment

## AST Nodes Processed

### Primary Nodes
- `clang::RecordDecl` - C struct declarations (pass-through)
- `clang::CXXRecordDecl` - C++ class/struct declarations (translate)

### Related Nodes (processed via traversal)
- `clang::FieldDecl` - Member variables
- `clang::AccessSpecDecl` - Access specifiers (stripped)
- `clang::CXXRecordDecl` (nested) - Nested classes

## Translation Strategy

### Basic Translation Rules

1. **Class → Struct Conversion**
   - `class ClassName` → `struct ClassName`
   - `struct ClassName` → `struct ClassName` (unchanged)

2. **Access Specifiers**
   - Strip all `public:`, `private:`, `protected:` specifiers
   - All fields become implicitly public in C

3. **Field Preservation**
   - Keep all fields regardless of access level
   - Preserve field order (important for layout compatibility)
   - Translate field types using TypeTranslator

4. **Nested Classes**
   - Lift nested classes to top level
   - Rename: `OuterClass::InnerClass` → `OuterClass__InnerClass`
   - Forward declare if used before definition

### Type Name Generation

```
C++ Type                     → C Type
-------------------------------------------
class GameState              → struct GameState
class Game::Player           → struct Game__Player
class Outer::Inner::Nested   → struct Outer__Inner__Nested
```

## Dependencies

### Required Handlers (must run before)
- **FileOriginFilter**: Determine which records belong to current file
- **TypeTranslator**: Translate field types (may reference other classes)

### Optional Handlers (may interact with)
- **TemplateMonomorphizer**: Generates monomorphized record instances
- **MethodHandler**: Needs struct names for method translation
- **ConstructorHandler**: Needs struct layout for initialization

## Algorithm

### Phase 1: Discovery and Collection

```
For each RecordDecl/CXXRecordDecl in C++ AST:
  1. Check FileOriginFilter: Does this belong to current file?
     - If NO: Skip (will be handled in its own file)
     - If YES: Continue

  2. Collect record information:
     - Full qualified name (with scope)
     - Is it class or struct? (both → struct in C)
     - Location (for header vs implementation decision)
     - Is it nested? (record parent if yes)

  3. Collect all FieldDecls:
     - Field name
     - Field type (QualType)
     - Field order (preserve exactly)
     - Ignore access specifiers

  4. Collect nested RecordDecls:
     - Add to processing queue with parent context
```

### Phase 2: Name Resolution

```
For each collected record:
  1. Generate C struct name:
     - If top-level: use original name
     - If nested: concatenate with "__" separator

  2. Check for name conflicts:
     - Namespace::ClassName vs ClassName
     - Resolve with namespace prefix if needed

  3. Register name mapping:
     - Map C++ RecordDecl → C struct name
     - Store for use by other handlers
```

### Phase 3: Type Translation

```
For each field in each record:
  1. Translate field type:
     - int, double, etc → same in C
     - std::string → char* (or custom String struct)
     - std::vector<T> → custom Vector__T struct
     - OtherClass → struct OtherClass*
     - OtherClass (value) → struct OtherClass

  2. Check for forward declaration needs:
     - If field is pointer to another struct: forward declare
     - If field is value of another struct: must define first

  3. Build C FieldDecl:
     - Same name as C++ field
     - Translated type
     - Preserve order
```

### Phase 4: C AST Construction

```
For each record:
  1. Create C RecordDecl node:
     - RecordDecl::Create(C_Context, ...)
     - Kind: TTK_Struct (always)
     - Name: generated C name

  2. Add all translated FieldDecls:
     - In exact same order as C++
     - With translated types

  3. Complete the definition:
     - RecordDecl->completeDefinition()

  4. Add to C translation unit:
     - C_TU->addDecl(RecordDecl)
```

### Phase 5: Output Organization

```
Determine output location:
  1. If original C++ class in header:
     → Put C struct in .h file

  2. If original C++ class in implementation:
     → Put C struct in .c file (file-local)

  3. If nested class used only in methods:
     → Consider making file-local in .c

  4. Generate forward declarations:
     → Add to header if struct is incomplete at use site
```

## C++ Example

```cpp
// game.h
namespace Game {
  class Player {
  private:
    int id;
    double health;

  public:
    int score;

    // Nested class
    class Inventory {
    private:
      int capacity;
    public:
      int itemCount;
    };

    Inventory inventory;
  };

  struct Point {  // Already a struct
    double x;
    double y;
  };
}
```

## C Example

```c
// game.h

// Forward declarations (if needed)
struct Game__Player__Inventory;

// Nested class lifted to top level
struct Game__Player__Inventory {
  int capacity;      // Was private, now public
  int itemCount;
};

// Main class converted to struct
struct Game__Player {
  int id;            // Was private, now public
  double health;     // Was private, now public
  int score;         // Was public, still public
  struct Game__Player__Inventory inventory;
};

// Struct passes through unchanged (but with namespace prefix)
struct Game__Point {
  double x;
  double y;
};
```

## Test Cases

### Unit Tests

1. **test_simple_class_to_struct**
   ```cpp
   class Simple { int x; };
   // → struct Simple { int x; };
   ```

2. **test_access_specifier_flattening**
   ```cpp
   class Mixed {
   private: int a;
   public: int b;
   protected: int c;
   };
   // → struct Mixed { int a; int b; int c; };
   ```

3. **test_nested_class_lifting**
   ```cpp
   class Outer {
     class Inner { int x; };
   };
   // → struct Outer__Inner { int x; };
   // → struct Outer { };
   ```

4. **test_field_order_preservation**
   ```cpp
   class Order { int z; int a; int m; };
   // → struct Order { int z; int a; int m; };  // Same order!
   ```

5. **test_complex_field_types**
   ```cpp
   class Complex {
     int* ptr;
     const double& ref;
     std::vector<int> vec;
   };
   // → struct Complex {
   //     int* ptr;
   //     const double* ref;  // Reference → pointer
   //     struct Vector__int vec;
   // };
   ```

6. **test_forward_declaration_needed**
   ```cpp
   class A { B* ptr; };
   class B { A* ptr; };
   // → struct B;  // Forward declaration
   // → struct A { struct B* ptr; };
   // → struct B { struct A* ptr; };
   ```

7. **test_struct_passthrough**
   ```cpp
   struct AlreadyStruct { int x; };
   // → struct AlreadyStruct { int x; };  // Unchanged
   ```

8. **test_empty_class**
   ```cpp
   class Empty { };
   // → struct Empty { };
   ```

9. **test_deeply_nested_classes**
   ```cpp
   class A {
     class B {
       class C { int x; };
     };
   };
   // → struct A__B__C { int x; };
   // → struct A__B { };
   // → struct A { };
   ```

### Integration Tests

1. **test_with_methods** (requires MethodHandler)
   ```cpp
   class Player {
     int health;
     void heal() { health = 100; }
   };
   ```

2. **test_with_constructors** (requires ConstructorHandler)
   ```cpp
   class Point {
     int x, y;
     Point(int x, int y) : x(x), y(y) { }
   };
   ```

3. **test_template_class** (requires TemplateMonomorphizer)
   ```cpp
   template<typename T>
   class Box { T value; };

   Box<int> intBox;
   ```

## Edge Cases

### 1. Anonymous Structs/Unions

```cpp
class Container {
  union {
    int asInt;
    float asFloat;
  };
};
```

**Solution**: Generate unique name for anonymous union
```c
struct Container__anonymous_union_1 {
  int asInt;
  float asFloat;
};

struct Container {
  struct Container__anonymous_union_1 __anon_1;
};
```

### 2. Bitfields

```cpp
class Flags {
  unsigned int flag1 : 1;
  unsigned int flag2 : 1;
  unsigned int value : 14;
};
```

**Solution**: Preserve bitfield syntax (C supports it)
```c
struct Flags {
  unsigned int flag1 : 1;
  unsigned int flag2 : 1;
  unsigned int value : 14;
};
```

### 3. Static Members

```cpp
class Counter {
  static int count;
  int id;
};
```

**Solution**: Move static members to file scope
```c
// In .c file
static int Counter__count;  // File-local static variable

struct Counter {
  int id;
  // Static member NOT in struct
};
```

### 4. Const Members

```cpp
class Immutable {
  const int id;
  int value;
};
```

**Solution**: Preserve const qualifier
```c
struct Immutable {
  const int id;
  int value;
};
```

**Note**: This makes struct assignment tricky in C. Document limitation.

### 5. Reference Members

```cpp
class Wrapper {
  int& ref;
};
```

**Solution**: Convert reference to pointer
```c
struct Wrapper {
  int* ref;  // Must be initialized carefully
};
```

**Note**: Constructor must take address. Document in ConstructorHandler.

### 6. Mutable Members

```cpp
class Cache {
  mutable int hitCount;
  int data;
};
```

**Solution**: Drop `mutable` keyword (no const methods in C)
```c
struct Cache {
  int hitCount;  // Just a normal field
  int data;
};
```

### 7. Nested Class Using Outer Members

```cpp
class Outer {
  int x;
  class Inner {
    void useX();  // Needs access to Outer::x
  };
};
```

**Solution**: Inner class methods need `Outer*` parameter
```c
struct Outer__Inner { };

struct Outer {
  int x;
};

// In MethodHandler:
void Outer__Inner_useX(struct Outer__Inner* this, struct Outer* outer) {
  // Can now access outer->x
}
```

### 8. Inheritance (NOT in Phase 4, but document for later)

```cpp
class Base {
  int baseField;
};

class Derived : public Base {
  int derivedField;
};
```

**Future Solution**: Composition or field flattening
```c
struct Base {
  int baseField;
};

struct Derived {
  struct Base __base;  // Composition
  int derivedField;
};
```

**Current**: Reject with error message pointing to future phase.

### 9. Name Collision with C Keywords

```cpp
class Register {  // "register" is C keyword
  int value;
};
```

**Solution**: Add prefix/suffix to avoid collision
```c
struct Register_ {  // Or _Register, or Register_t
  int value;
};
```

### 10. Templated Nested Classes

```cpp
template<typename T>
class Outer {
  class Inner {
    T value;
  };
};

Outer<int>::Inner inner;
```

**Solution**: Monomorphize both outer and inner
```c
struct Outer__int__Inner {
  int value;
};

struct Outer__int { };
```

## Implementation Checklist

- [ ] Create RecordHandler class with Chain of Responsibility interface
- [ ] Implement RecordDecl visitor (pass-through for C structs)
- [ ] Implement CXXRecordDecl visitor (translate classes)
- [ ] Implement access specifier stripping
- [ ] Implement field collection and ordering
- [ ] Implement nested class detection and lifting
- [ ] Implement C struct name generation with "__" separator
- [ ] Implement type translation for field types
- [ ] Implement forward declaration detection
- [ ] Implement C RecordDecl AST construction
- [ ] Write unit tests for all test cases
- [ ] Write integration tests with other handlers
- [ ] Document all edge cases with examples
- [ ] Add error handling for unsupported features (inheritance, etc.)

## Success Criteria

1. All C structs pass-through unchanged
2. All C++ classes convert to structs with correct fields
3. Access specifiers completely removed
4. Field order exactly preserved
5. Nested classes correctly lifted and renamed
6. Type translation integrates with TypeTranslator
7. Forward declarations generated when needed
8. All 9 unit tests pass
9. Integration tests pass with MethodHandler and ConstructorHandler
10. All 10 edge cases handled correctly or documented as limitations
