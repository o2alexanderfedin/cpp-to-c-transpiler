# MemberAccessHandler Specification

## Responsibility

Translates C++ member access expressions (field access and method calls) into C equivalents. This handler is responsible for:
- Converting field access (`.` and `->` operators)
- Translating method calls to function calls with explicit `this`
- Handling nested member access
- Managing implicit `this` in member functions
- Translating member function pointers
- Handling chained method calls

## AST Nodes Processed

### Primary Nodes
- `clang::MemberExpr` - Field access: `obj.field`, `ptr->field`
- `clang::CXXMemberCallExpr` - Method calls: `obj.method()`, `ptr->method()`
- `clang::CXXThisExpr` - Explicit or implicit `this` pointer

### Related Nodes (processed via traversal)
- `clang::DeclRefExpr` - Variable references (for `this` replacement)
- `clang::UnaryOperator` - Address-of for method calls: `&obj`
- `clang::CallExpr` - Base class for call expressions

## Translation Strategy

### Basic Translation Rules

1. **Field Access (Dot Operator)**
   ```cpp
   obj.field

   ↓

   obj.field  // Unchanged (C has dot operator)
   ```

2. **Field Access (Arrow Operator)**
   ```cpp
   ptr->field

   ↓

   ptr->field  // Unchanged (C has arrow operator)
   ```

3. **Method Call (Dot Operator)**
   ```cpp
   obj.method(arg1, arg2)

   ↓

   ClassName_method(&obj, arg1, arg2)
   ```

4. **Method Call (Arrow Operator)**
   ```cpp
   ptr->method(arg1, arg2)

   ↓

   ClassName_method(ptr, arg1, arg2)  // No & needed, already pointer
   ```

5. **Implicit This**
   ```cpp
   class C {
     int field;
     void method() {
       field = 42;  // Implicit this->field
     }
   };

   ↓

   void C_method(struct C* this) {
     this->field = 42;
   }
   ```

6. **Chained Method Calls**
   ```cpp
   obj.method1().method2().method3()

   ↓

   // If methods return by value:
   struct C temp1 = C_method1(&obj);
   struct C temp2 = C_method2(&temp1);
   struct C result = C_method3(&temp2);

   // If methods return by reference:
   struct C* temp1 = C_method1(&obj);
   struct C* temp2 = C_method2(temp1);
   struct C* result = C_method3(temp2);
   ```

### Operator Translation

```
C++ Operator    Context              → C Translation
----------------------------------------------------------
.               obj.field            → obj.field
->              ptr->field           → ptr->field
.               obj.method()         → ClassName_method(&obj, ...)
->              ptr->method()        → ClassName_method(ptr, ...)
this            this->field          → this->field
this            this->method()       → ClassName_method(this, ...)
```

## Dependencies

### Required Handlers (must run before)
- **RecordHandler**: Need struct definitions
- **MethodHandler**: Need method name mappings
- **FileOriginFilter**: Determine context

### Optional Handlers (may interact with)
- **ExpressionTranslator**: For arguments in method calls
- **TypeTranslator**: For return type handling

## Algorithm

### Phase 1: Expression Analysis

```
For each MemberExpr or CXXMemberCallExpr:
  1. Identify the base expression:
     base = expr->getBase()

     Examples:
     - obj.field → base is DeclRefExpr("obj")
     - ptr->field → base is DeclRefExpr("ptr")
     - this->field → base is CXXThisExpr
     - obj.method1().field → base is CXXMemberCallExpr

  2. Determine base type:
     baseType = base->getType()

     Is it:
     - Value type (struct C)
     - Pointer type (struct C*)
     - Reference type (struct C&)

  3. Identify the member being accessed:
     member = expr->getMemberDecl()

     Is it:
     - FieldDecl (field access)
     - CXXMethodDecl (method call)
     - EnumConstantDecl (should not happen via member access)
```

### Phase 2: Field Access Translation

```
If MemberExpr accessing a field:
  1. Translate base expression:
     translatedBase = translateExpr(base)

  2. Determine operator:
     If baseType is pointer or reference:
       operator = "->"
     Else:
       operator = "."

  3. Build C MemberExpr:
     result = MemberExpr::Create(
       C_Context,
       translatedBase,
       baseType->isPointerType(),  // isArrow
       member,
       fieldType
     )

  4. Return C AST node
```

### Phase 3: Method Call Translation

```
If CXXMemberCallExpr:
  1. Get method being called:
     method = expr->getMethodDecl()

  2. Look up translated method name:
     methodName = MethodHandler->getTranslatedName(method)
     Example: "Player_attack__int"

  3. Translate base expression:
     translatedBase = translateExpr(base)

  4. Prepare 'this' argument:
     If baseType is pointer:
       thisArg = translatedBase  // Already a pointer

     If baseType is value or reference:
       thisArg = UnaryOperator(&, translatedBase)  // Take address

  5. Translate method arguments:
     translatedArgs = []
     for each arg in expr->getArgs():
       translatedArgs.append(translateExpr(arg))

  6. Build argument list:
     finalArgs = [thisArg] + translatedArgs

  7. Create C CallExpr:
     result = CallExpr::Create(
       C_Context,
       DeclRefExpr(methodName),  // Function to call
       finalArgs,
       returnType
     )

  8. Return C AST node
```

### Phase 4: Implicit This Handling

```
When inside a method body:
  1. Track current method context:
     currentMethod = getCurrentMethod()
     currentClass = currentMethod->getParent()

  2. For each MemberExpr where base is CXXThisExpr:
     Replace CXXThisExpr with DeclRefExpr("this")

     Example:
     this->field → this->field  (in C AST)

  3. For each MemberExpr where base is implicit:
     Example in C++:
       void C::method() {
         field = 42;  // Implicit this->field
       }

     Translate to:
       void C_method(struct C* this) {
         this->field = 42;
       }

     Steps:
     a. Detect implicit member access (Clang provides this info)
     b. Create explicit DeclRefExpr("this")
     c. Create MemberExpr with this as base

  4. For each method call with implicit this:
     Example in C++:
       void C::method1() {
         method2();  // Implicit this->method2()
       }

     Translate to:
       void C_method1(struct C* this) {
         C_method2(this);
       }
```

### Phase 5: Chained Calls Translation

```
For chained method calls: obj.m1().m2().m3()

  1. Identify the chain:
     Parse AST to find nested CXXMemberCallExpr

     Structure:
     CXXMemberCallExpr(m3)
       └─ CXXMemberCallExpr(m2)
            └─ CXXMemberCallExpr(m1)
                 └─ DeclRefExpr(obj)

  2. Flatten the chain (process innermost first):
     calls = [m1, m2, m3]
     currentBase = obj

  3. For each call in chain:
     a. Translate call:
        result = translateMethodCall(currentBase, call)

     b. Determine if we need temporary:
        If call returns by value AND not last in chain:
          Generate temporary variable:

          struct RetType __temp_N;
          __temp_N = ClassName_method(&currentBase, args...);
          currentBase = &__temp_N;

        If call returns by reference/pointer:
          currentBase = ClassName_method(currentBase, args...);

  4. Return final result
```

### Phase 6: Nested Member Access

```
For nested field access: obj.inner.field

  1. Parse structure:
     MemberExpr(field)
       └─ MemberExpr(inner)
            └─ DeclRefExpr(obj)

  2. Translate innermost first:
     temp1 = obj.inner  (or obj->inner if obj is pointer)
     temp2 = temp1.field  (or temp1->field)

  3. In C AST:
     Just compose: obj.inner.field

     C handles this naturally!
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
    int getHealth() const {
      return health;  // Implicit this->health
    }

    void heal() {
      health = maxHealth;  // Implicit this
    }

    void takeDamage(int amount) {
      health -= amount;
    }

    Player& setHealth(int h) {
      health = h;
      return *this;  // Return self for chaining
    }
  };

  class Game {
  private:
    Player player;

  public:
    void playTurn() {
      // Field access
      int currentHealth = player.getHealth();

      // Method call
      player.takeDamage(10);

      // Chained calls
      player.setHealth(100).takeDamage(5);
    }
  };
}

void externalFunction() {
  Game::Player p;

  // Dot operator
  p.heal();
  int h = p.getHealth();

  // Arrow operator
  Game::Player* ptr = &p;
  ptr->heal();
  int h2 = ptr->getHealth();
}
```

## C Example

```c
// player.h
struct Game__Player;
struct Game__Game;

// Method declarations
int Game__Player_getHealth(const struct Game__Player* this);
void Game__Player_heal(struct Game__Player* this);
void Game__Player_takeDamage(struct Game__Player* this, int amount);
struct Game__Player* Game__Player_setHealth(struct Game__Player* this, int h);
void Game__Game_playTurn(struct Game__Game* this);

// player.c
#include "player.h"

struct Game__Player {
  int health;
  int maxHealth;
};

struct Game__Game {
  struct Game__Player player;
};

int Game__Player_getHealth(const struct Game__Player* this) {
  return this->health;  // Explicit this
}

void Game__Player_heal(struct Game__Player* this) {
  this->health = this->maxHealth;  // Explicit this
}

void Game__Player_takeDamage(struct Game__Player* this, int amount) {
  this->health -= amount;
}

struct Game__Player* Game__Player_setHealth(struct Game__Player* this, int h) {
  this->health = h;
  return this;
}

void Game__Game_playTurn(struct Game__Game* this) {
  // Field access: this->player is a value
  int currentHealth = Game__Player_getHealth(&this->player);

  // Method call
  Game__Player_takeDamage(&this->player, 10);

  // Chained calls
  struct Game__Player* temp = Game__Player_setHealth(&this->player, 100);
  Game__Player_takeDamage(temp, 5);
}

void externalFunction(void) {
  struct Game__Player p;
  Game__Player__ctor__default(&p);  // Constructor

  // Dot operator → take address for 'this'
  Game__Player_heal(&p);
  int h = Game__Player_getHealth(&p);

  // Arrow operator → already pointer
  struct Game__Player* ptr = &p;
  Game__Player_heal(ptr);
  int h2 = Game__Player_getHealth(ptr);
}
```

## Test Cases

### Unit Tests

1. **test_field_access_dot**
   ```cpp
   struct C { int x; };
   C obj;
   int val = obj.x;
   // → int val = obj.x;  // Unchanged
   ```

2. **test_field_access_arrow**
   ```cpp
   struct C { int x; };
   C* ptr;
   int val = ptr->x;
   // → int val = ptr->x;  // Unchanged
   ```

3. **test_method_call_dot**
   ```cpp
   class C { void method() { } };
   C obj;
   obj.method();
   // → C_method(&obj);
   ```

4. **test_method_call_arrow**
   ```cpp
   class C { void method() { } };
   C* ptr;
   ptr->method();
   // → C_method(ptr);
   ```

5. **test_method_with_args**
   ```cpp
   class C { void method(int x, int y) { } };
   C obj;
   obj.method(10, 20);
   // → C_method(&obj, 10, 20);
   ```

6. **test_implicit_this_field**
   ```cpp
   class C {
     int x;
     void method() { x = 42; }
   };
   // → void C_method(struct C* this) { this->x = 42; }
   ```

7. **test_implicit_this_method**
   ```cpp
   class C {
     void a() { }
     void b() { a(); }
   };
   // → void C_b(struct C* this) { C_a(this); }
   ```

8. **test_explicit_this**
   ```cpp
   class C {
     int x;
     void method() { this->x = 42; }
   };
   // → void C_method(struct C* this) { this->x = 42; }
   ```

9. **test_nested_field_access**
   ```cpp
   struct Inner { int x; };
   struct Outer { Inner inner; };
   Outer obj;
   int val = obj.inner.x;
   // → int val = obj.inner.x;  // C handles naturally
   ```

10. **test_chained_method_calls**
    ```cpp
    class C {
      C& method() { return *this; }
    };
    C obj;
    obj.method().method();
    // → struct C* temp = C_method(&obj);
    //   C_method(temp);
    ```

### Integration Tests

1. **test_with_method_handler**
   - Ensure method names match

2. **test_with_record_handler**
   - Ensure field types match

3. **test_complex_scenario**
   - Multiple levels of member access

## Edge Cases

### 1. Method Returning Reference

```cpp
class C {
  C& method() { return *this; }
};

C obj;
obj.method().method();
```

**Solution**: Track return type, no temp needed
```c
struct C* C_method(struct C* this) { return this; }

// Call site:
C_method(C_method(&obj));
```

### 2. Method Returning Value (Chained)

```cpp
class C {
  C method() { return *this; }
};

C obj;
obj.method().method();
```

**Solution**: Need temporary for copy
```c
struct C C_method(struct C* this) {
  struct C result;
  // Copy *this to result
  return result;
}

// Call site:
struct C __temp1 = C_method(&obj);
C_method(&__temp1);
```

### 3. Static Member Access

```cpp
class C {
  static int count;
  static int getCount() { return count; }
};

C obj;
obj.getCount();  // Can call static via instance (weird but legal)
C::getCount();   // Normal way
```

**Solution**: Static members are not in struct
```c
// File scope
static int C__count;

int C_getCount(void) {  // No 'this'
  return C__count;
}

// Call site (both ways):
C_getCount();  // obj.getCount() and C::getCount() both → this
```

### 4. Const Method on Non-Const Object

```cpp
class C {
  int get() const { return x; }
  int x;
};

C obj;
obj.get();
```

**Solution**: Can pass non-const to const
```c
int C_get(const struct C* this) { return this->x; }

// Call site:
C_get(&obj);  // OK: struct C* converts to const struct C*
```

### 5. Member Function Pointer

```cpp
class C {
  void method() { }
};

void (C::*ptr)() = &C::method;
C obj;
(obj.*ptr)();
```

**Solution**: Function pointer without 'this'
```c
void (*ptr)(struct C*) = &C_method;

// Call site:
(*ptr)(&obj);
```

**Note**: More complex with overloading. Document limitation.

### 6. Overloaded Method Call

```cpp
class C {
  void method(int x) { }
  void method(double x) { }
};

C obj;
obj.method(42);
obj.method(3.14);
```

**Solution**: Resolve overload at call site
```c
C_method__int(&obj, 42);
C_method__double(&obj, 3.14);
```

### 7. Template Method Call

```cpp
class C {
  template<typename T>
  void method(T value) { }
};

C obj;
obj.method(42);
obj.method(3.14);
```

**Solution**: Monomorphize
```c
C_method__int(&obj, 42);
C_method__double(&obj, 3.14);
```

### 8. Virtual Method Call

```cpp
class Base {
  virtual void method() { }
};

class Derived : public Base {
  void method() override { }
};

Base* ptr = new Derived();
ptr->method();  // Should call Derived::method
```

**Solution**: No inheritance in Phase 4
```
ERROR: Virtual method calls not supported (no inheritance)
```

### 9. Method Call on Temporary

```cpp
class C {
  C create() { return C(); }
  void method() { }
};

create().method();
```

**Solution**: Generate temporary
```c
struct C __temp = C_create();
C_method(&__temp);
```

### 10. Arrow Operator Overload

```cpp
class SmartPtr {
  C* operator->() { return ptr; }
  C* ptr;
};

SmartPtr sp;
sp->method();  // Calls operator->, then method
```

**Solution**: Chain operator call
```c
struct C* SmartPtr_operator_arrow(struct SmartPtr* this) {
  return this->ptr;
}

// Call site:
struct C* __temp = SmartPtr_operator_arrow(&sp);
C_method(__temp);
```

### 11. Nested Class Method Call

```cpp
class Outer {
  class Inner {
    void method() { }
  };
};

Outer::Inner obj;
obj.method();
```

**Solution**: Use full qualified name
```c
Outer__Inner_method(&obj);
```

### 12. Anonymous Struct Member Access

```cpp
class C {
  union {
    int asInt;
    float asFloat;
  };

  void method() {
    asInt = 42;  // Which member?
  }
};
```

**Solution**: Named anonymous union member
```c
struct C {
  union {
    int asInt;
    float asFloat;
  } __anon_1;
};

void C_method(struct C* this) {
  this->__anon_1.asInt = 42;
}
```

## Implementation Checklist

- [ ] Create MemberAccessHandler class with Chain of Responsibility interface
- [ ] Implement MemberExpr visitor (field access)
- [ ] Implement CXXMemberCallExpr visitor (method calls)
- [ ] Implement CXXThisExpr detection and replacement
- [ ] Implement implicit member access detection
- [ ] Implement dot operator handling (take address for method calls)
- [ ] Implement arrow operator handling (use as-is)
- [ ] Implement method name lookup from MethodHandler
- [ ] Implement argument translation and reordering
- [ ] Implement chained call detection and flattening
- [ ] Implement temporary generation for value returns
- [ ] Implement nested member access
- [ ] Write unit tests for all test cases
- [ ] Write integration tests with MethodHandler and RecordHandler
- [ ] Document all edge cases
- [ ] Add error handling for unsupported features (virtual calls, etc.)

## Success Criteria

1. Field access (dot and arrow) works correctly
2. Method calls translate with correct `this` parameter
3. Dot operator on value types takes address
4. Arrow operator on pointer types passes pointer
5. Implicit `this` converted to explicit
6. Chained method calls work with temporaries
7. Nested member access translates correctly
8. Method overloads resolve to correct names
9. All 10 unit tests pass
10. Integration tests pass with MethodHandler and RecordHandler
11. All 12 edge cases handled or documented
12. Return type handling correct (value vs reference)
