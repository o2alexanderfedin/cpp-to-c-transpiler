# MethodHandler Specification

## Responsibility

Translates C++ member functions (methods) into C free functions with explicit `this` parameter. This handler is responsible for:
- Converting method declarations to function declarations
- Adding explicit `this` parameter as first argument
- Generating appropriate function names (with class prefix)
- Handling method qualifiers (const, static)
- Managing method overloading via name mangling
- Translating method bodies with `this` pointer usage

## AST Nodes Processed

### Primary Nodes
- `clang::CXXMethodDecl` - C++ member functions (non-static)
- `clang::CXXConstructorDecl` - Handled by ConstructorHandler (not here)
- `clang::CXXDestructorDecl` - Handled by DestructorHandler (not here)

### Related Nodes (processed via traversal)
- `clang::ParmVarDecl` - Method parameters
- `clang::CXXThisExpr` - Implicit/explicit `this` usage
- `clang::MemberExpr` - Field access via `this`
- `clang::CXXMemberCallExpr` - Calls to other methods (via MemberAccessHandler)

## Translation Strategy

### Basic Translation Rules

1. **Method → Function Conversion**
   ```
   class ClassName {
     RetType methodName(Param1 p1, Param2 p2);
   };

   ↓

   RetType ClassName_methodName(struct ClassName* this, Param1 p1, Param2 p2);
   ```

2. **Const Methods**
   ```
   class ClassName {
     RetType methodName(Param p) const;
   };

   ↓

   RetType ClassName_methodName(const struct ClassName* this, Param p);
   ```

3. **Static Methods**
   ```
   class ClassName {
     static RetType staticMethod(Param p);
   };

   ↓

   RetType ClassName_staticMethod(Param p);  // No 'this' parameter
   ```

4. **Method Overloading**
   ```
   class ClassName {
     void method(int x);
     void method(double x);
     void method(int x, int y);
   };

   ↓

   void ClassName_method__int(struct ClassName* this, int x);
   void ClassName_method__double(struct ClassName* this, double x);
   void ClassName_method__int_int(struct ClassName* this, int x, int y);
   ```

### Name Generation Rules

```
C++ Method                           → C Function Name
------------------------------------------------------------------
ClassName::method                    → ClassName_method
ClassName::method (overload 1)      → ClassName_method__int
ClassName::method (overload 2)      → ClassName_method__double
OuterClass::InnerClass::method       → OuterClass__InnerClass_method
ClassName::operator+                 → ClassName_operator_plus
ClassName::~ClassName                → (handled by DestructorHandler)
```

### Name Mangling for Overloads

```
Parameter Types          → Suffix
----------------------------------
(int)                    → __int
(double)                 → __double
(int, int)               → __int_int
(const std::string&)     → __const_string_ref
(int*)                   → __int_ptr
(const int* const)       → __const_int_ptr_const
```

## Dependencies

### Required Handlers (must run before)
- **RecordHandler**: Need struct definitions to reference in `this` parameter
- **FileOriginFilter**: Determine which methods belong to current file
- **TypeTranslator**: Translate parameter and return types

### Optional Handlers (may interact with)
- **MemberAccessHandler**: Translates method calls inside method bodies
- **ExpressionTranslator**: Translates method body expressions
- **StatementTranslator**: Translates method body statements

## Algorithm

### Phase 1: Method Discovery

```
For each CXXMethodDecl in C++ AST:
  1. Check FileOriginFilter: Does this belong to current file?
     - If NO: Skip (external method)
     - If YES: Continue

  2. Skip special methods:
     - If CXXConstructorDecl: Let ConstructorHandler handle it
     - If CXXDestructorDecl: Let DestructorHandler handle it
     - If conversion operator: Document as unsupported

  3. Collect method information:
     - Method name
     - Parent class (RecordDecl)
     - Return type
     - Parameter list
     - Method qualifiers: const, static, virtual
     - Method body (if defined)

  4. Check for overloading:
     - Look for other methods with same name in same class
     - If found: Will need name mangling
```

### Phase 2: Name Generation and Mangling

```
For each method:
  1. Generate base name:
     base = ClassName + "_" + methodName
     Example: "Player_heal"

  2. Check for overloads:
     If no overloads:
       finalName = base

     If overloads exist:
       suffix = generateOverloadSuffix(parameterTypes)
       finalName = base + suffix
       Example: "Player_attack__int" vs "Player_attack__double"

  3. Handle nested classes:
     If method belongs to nested class:
       base = OuterClass + "__" + InnerClass + "_" + methodName
       Example: "Player__Inventory_addItem"

  4. Handle operators:
     If operator method:
       base = ClassName + "_operator_" + operatorName
       Example: "Vector_operator_plus"

  5. Register name mapping:
     Map CXXMethodDecl → C function name
     Store for MemberAccessHandler to use
```

### Phase 3: Parameter Translation

```
For each method:
  1. Determine 'this' parameter:
     If static method:
       thisParam = nullptr  // No 'this' parameter

     If const method:
       thisParam = ParmVarDecl("this", const struct ClassName*)

     If non-const method:
       thisParam = ParmVarDecl("this", struct ClassName*)

  2. Translate existing parameters:
     For each original parameter:
       - Translate parameter type via TypeTranslator
       - Preserve parameter name
       - Preserve default values (if C99/C11)
       - Create C ParmVarDecl

  3. Build final parameter list:
     If static:
       params = [translated original params]
     Else:
       params = [thisParam] + [translated original params]
```

### Phase 4: Return Type Translation

```
For each method:
  1. Get original return type (QualType)

  2. Translate via TypeTranslator:
     - int, double, etc → same
     - ClassName → struct ClassName
     - ClassName& → struct ClassName*
     - std::string → char* (or struct String)
     - void → void

  3. Preserve const/volatile qualifiers on return type
```

### Phase 5: Method Body Translation

```
For each method with definition:
  1. Create new function body scope

  2. Transform 'this' usage:
     For each CXXThisExpr in body:
       Replace with DeclRefExpr to 'this' parameter

     For each implicit field access:
       member → this->member

     For each implicit method call:
       otherMethod() → ClassName_otherMethod(this)

  3. Translate field access:
     For each MemberExpr where base is 'this':
       this.field → this->field  (in C)
       (Handled by ExpressionTranslator)

  4. Translate method calls:
     For each CXXMemberCallExpr:
       Delegate to MemberAccessHandler
       obj.method(args) → ClassName_method(&obj, args)

  5. Translate all other statements/expressions:
     Delegate to StatementTranslator and ExpressionTranslator

  6. Build C CompoundStmt with transformed body
```

### Phase 6: C AST Construction

```
For each method:
  1. Create C FunctionDecl:
     FunctionDecl::Create(
       C_Context,
       C_TU,                    // Parent
       SourceLocation,
       DeclarationName,         // Generated C name
       translatedReturnType,
       translatedParams
     )

  2. If method has body:
     Set function body to translated CompoundStmt

  3. Set storage class:
     If static method: No special storage
     If inline method: Mark as inline in C
     If virtual method: Just a normal function (no vtable)

  4. Add to C translation unit:
     C_TU->addDecl(FunctionDecl)
```

### Phase 7: Declaration vs Definition

```
For each method:
  1. Determine if declaration or definition:

     If method defined inline in class:
       - Put declaration in .h file
       - Put definition in .c file (or inline in .h if marked inline)

     If method declared in class, defined outside:
       - Put declaration in .h file
       - Put definition in .c file

     If method in implementation file only:
       - Put declaration and definition in .c file
       - Mark as static (file-local)

  2. Handle inline methods:
     If method marked inline:
       - Option 1: Keep inline in .h (may cause bloat)
       - Option 2: Move to .c with static linkage
       - Document choice in configuration
```

## C++ Example

```cpp
// player.h
namespace Game {
  class Player {
  private:
    int health;
    int maxHealth;

  public:
    // Simple method
    void heal() {
      health = maxHealth;
    }

    // Const method
    int getHealth() const {
      return health;
    }

    // Method with parameters
    void takeDamage(int amount) {
      health -= amount;
      if (health < 0) health = 0;
    }

    // Overloaded methods
    void attack(int damage) {
      // Physical attack
    }

    void attack(double magicPower) {
      // Magic attack
    }

    // Static method
    static int getMaxPlayers() {
      return 100;
    }

    // Method calling other method
    void reset() {
      heal();
      takeDamage(0);
    }
  };
}
```

## C Example

```c
// player.h
struct Game__Player;

// Declarations
void Game__Player_heal(struct Game__Player* this);
int Game__Player_getHealth(const struct Game__Player* this);
void Game__Player_takeDamage(struct Game__Player* this, int amount);
void Game__Player_attack__int(struct Game__Player* this, int damage);
void Game__Player_attack__double(struct Game__Player* this, double magicPower);
int Game__Player_getMaxPlayers(void);  // No 'this' - static
void Game__Player_reset(struct Game__Player* this);

// player.c
#include "player.h"

struct Game__Player {
  int health;
  int maxHealth;
};

void Game__Player_heal(struct Game__Player* this) {
  this->health = this->maxHealth;
}

int Game__Player_getHealth(const struct Game__Player* this) {
  return this->health;
}

void Game__Player_takeDamage(struct Game__Player* this, int amount) {
  this->health -= amount;
  if (this->health < 0) {
    this->health = 0;
  }
}

void Game__Player_attack__int(struct Game__Player* this, int damage) {
  // Physical attack
}

void Game__Player_attack__double(struct Game__Player* this, double magicPower) {
  // Magic attack
}

int Game__Player_getMaxPlayers(void) {
  return 100;
}

void Game__Player_reset(struct Game__Player* this) {
  Game__Player_heal(this);
  Game__Player_takeDamage(this, 0);
}
```

## Test Cases

### Unit Tests

1. **test_simple_method**
   ```cpp
   class C { void method() { } };
   // → void C_method(struct C* this) { }
   ```

2. **test_const_method**
   ```cpp
   class C { int get() const { return 42; } };
   // → int C_get(const struct C* this) { return 42; }
   ```

3. **test_static_method**
   ```cpp
   class C { static int compute(int x) { return x * 2; } };
   // → int C_compute(int x) { return x * 2; }
   ```

4. **test_method_with_params**
   ```cpp
   class C { void set(int x, double y) { } };
   // → void C_set(struct C* this, int x, double y) { }
   ```

5. **test_method_overloading**
   ```cpp
   class C {
     void method(int x) { }
     void method(double x) { }
   };
   // → void C_method__int(struct C* this, int x) { }
   // → void C_method__double(struct C* this, double x) { }
   ```

6. **test_nested_class_method**
   ```cpp
   class Outer {
     class Inner {
       void method() { }
     };
   };
   // → void Outer__Inner_method(struct Outer__Inner* this) { }
   ```

7. **test_this_usage**
   ```cpp
   class C {
     int x;
     void setX(int val) { x = val; }  // Implicit this->x
   };
   // → void C_setX(struct C* this, int val) { this->x = val; }
   ```

8. **test_explicit_this**
   ```cpp
   class C {
     int x;
     void setX(int x) { this->x = x; }
   };
   // → void C_setX(struct C* this, int x) { this->x = x; }
   ```

9. **test_method_calling_method**
   ```cpp
   class C {
     void a() { }
     void b() { a(); }
   };
   // → void C_a(struct C* this) { }
   // → void C_b(struct C* this) { C_a(this); }
   ```

10. **test_return_type_translation**
    ```cpp
    class C {
      std::string getName() { return "test"; }
    };
    // → char* C_getName(struct C* this) { return "test"; }
    ```

### Integration Tests

1. **test_with_record_handler**
   - Ensure struct definition matches method signatures

2. **test_with_member_access_handler**
   - Ensure method calls translate correctly

3. **test_with_expression_translator**
   - Ensure method bodies translate correctly

## Edge Cases

### 1. Virtual Methods

```cpp
class Base {
  virtual void method() { }
};
```

**Solution**: Treat as normal method (no vtable in C)
```c
void Base_method(struct Base* this) { }
```

**Note**: Virtual dispatch not supported. Document limitation.

### 2. Pure Virtual Methods

```cpp
class Abstract {
  virtual void method() = 0;
};
```

**Solution**: Emit declaration only, no definition
```c
void Abstract_method(struct Abstract* this);  // No body
```

**Note**: Caller must provide implementation or error.

### 3. Override Methods

```cpp
class Derived : public Base {
  void method() override { }
};
```

**Solution**: Treat as normal method, drop `override`
```c
void Derived_method(struct Derived* this) { }
```

**Note**: No inheritance, so override has no meaning.

### 4. Inline Methods in Header

```cpp
// header.h
class C {
  inline void method() { /* ... */ }
};
```

**Solution**: Either inline in header or move to .c
```c
// Option 1: Keep inline
static inline void C_method(struct C* this) { /* ... */ }

// Option 2: Move to .c
// In header: void C_method(struct C* this);
// In .c: void C_method(struct C* this) { /* ... */ }
```

### 5. Default Parameters

```cpp
class C {
  void method(int x, int y = 0) { }
};
```

**Solution**: Generate overload wrappers
```c
void C_method(struct C* this, int x, int y) { }

// Wrapper for default parameter
static inline void C_method__default_y(struct C* this, int x) {
  C_method(this, x, 0);
}
```

### 6. Template Methods

```cpp
class C {
  template<typename T>
  void method(T value) { }
};

// Usage
C c;
c.method(42);
c.method(3.14);
```

**Solution**: Monomorphize template methods
```c
void C_method__int(struct C* this, int value) { }
void C_method__double(struct C* this, double value) { }
```

### 7. Operator Overloading

```cpp
class Vector {
  Vector operator+(const Vector& other) { }
  Vector& operator+=(const Vector& other) { }
  Vector operator-() const { }
};
```

**Solution**: Translate to named functions
```c
struct Vector Vector_operator_plus(struct Vector* this, const struct Vector* other) { }
void Vector_operator_plus_assign(struct Vector* this, const struct Vector* other) { }
struct Vector Vector_operator_negate(const struct Vector* this) { }
```

**Operator Name Mapping**:
```
+   → operator_plus
-   → operator_minus
*   → operator_multiply
/   → operator_divide
+=  → operator_plus_assign
==  → operator_equal
<   → operator_less
[]  → operator_subscript
()  → operator_call
```

### 8. Conversion Operators

```cpp
class Number {
  operator int() const { return value; }
  operator double() const { return value; }
private:
  int value;
};
```

**Solution**: Translate to named conversion functions
```c
int Number_to_int(const struct Number* this) { return this->value; }
double Number_to_double(const struct Number* this) { return this->value; }
```

### 9. Friend Functions (Non-Member)

```cpp
class C {
  friend void helper(C& c);
private:
  int x;
};
```

**Solution**: Just emit as free function
```c
void helper(struct C* c);  // Has access to all fields (no private in C)
```

### 10. Trailing Return Type

```cpp
class C {
  auto method() -> int { return 42; }
};
```

**Solution**: Extract return type, emit normally
```c
int C_method(struct C* this) { return 42; }
```

### 11. Noexcept Specification

```cpp
class C {
  void method() noexcept { }
};
```

**Solution**: Drop noexcept (no exceptions in C)
```c
void C_method(struct C* this) { }
```

### 12. Rvalue Reference Parameters

```cpp
class C {
  void method(std::string&& str) { }
};
```

**Solution**: Treat as regular reference (pointer)
```c
void C_method(struct C* this, char* str) { }
```

**Note**: Move semantics not preserved.

## Implementation Checklist

- [ ] Create MethodHandler class with Chain of Responsibility interface
- [ ] Implement CXXMethodDecl visitor
- [ ] Skip constructors/destructors (handled elsewhere)
- [ ] Implement method name generation
- [ ] Implement overload detection and name mangling
- [ ] Implement `this` parameter insertion (const vs non-const)
- [ ] Implement static method detection (no `this`)
- [ ] Implement parameter list translation
- [ ] Implement return type translation
- [ ] Implement method body translation
- [ ] Implement `this` usage transformation
- [ ] Implement method call delegation to MemberAccessHandler
- [ ] Implement declaration vs definition logic
- [ ] Write unit tests for all test cases
- [ ] Write integration tests with other handlers
- [ ] Document all edge cases
- [ ] Add error handling for unsupported features (pure virtual, etc.)

## Success Criteria

1. All non-static methods get explicit `this` parameter
2. All static methods have no `this` parameter
3. Const methods get `const struct*` this parameter
4. Method overloading resolved via name mangling
5. Method bodies correctly transform `this` usage
6. Method calls delegate to MemberAccessHandler
7. Nested class methods use correct naming
8. All 10 unit tests pass
9. Integration tests pass with RecordHandler and MemberAccessHandler
10. All 12 edge cases handled or documented
