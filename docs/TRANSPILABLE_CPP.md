# Transpilable C++ Subset

**Version**: 3.0.0-draft
**Date**: 2025-12-24
**Status**: DRAFT - Subject to refinement based on real-world validation

---

## Overview

This document defines the "Transpilable C++" subset - the subset of C++ language features that the hupyy-cpp-to-c transpiler currently supports. Understanding these boundaries helps you write C++ code that transpiles successfully to C.

**Philosophy**: Transpilable C++ focuses on core object-oriented and generic programming features that can be mechanically translated to C, while avoiding features that require complex runtime support (STL, exceptions with full unwinding, etc.).

---

## Supported C++ Features

### Core Language Features (C++98/03 Base)

#### ✅ Classes and Structs
```cpp
// SUPPORTED
class Point {
private:
    double x_, y_;
public:
    Point(double x, double y) : x_(x), y_(y) {}
    double distance() const {
        return sqrt(x_ * x_ + y_ * y_);
    }
};

// Transpiles to:
struct Point {
    double x_;
    double y_;
};
void Point_init(struct Point* self, double x, double y);
double Point_distance(const struct Point* self);
```

#### ✅ Single Inheritance
```cpp
// SUPPORTED
class Shape {
public:
    virtual double area() const = 0;
    virtual ~Shape() {}
};

class Circle : public Shape {
    double radius_;
public:
    Circle(double r) : radius_(r) {}
    double area() const override {
        return 3.14159 * radius_ * radius_;
    }
};

// Transpiles to: Structs with composition + vtable pointers
```

#### ✅ Multiple Inheritance (Non-Virtual)
```cpp
// SUPPORTED
class Printable {
public:
    virtual void print() const = 0;
};

class Serializable {
public:
    virtual void serialize() const = 0;
};

class Document : public Printable, public Serializable {
    // ...
};

// Transpiles to: Struct with multiple vtable pointers
```

#### ✅ Virtual Functions and Polymorphism
```cpp
// SUPPORTED
class Base {
public:
    virtual void foo() { /* default */ }
    virtual void bar() = 0;  // Pure virtual
    virtual ~Base() {}
};

class Derived : public Base {
public:
    void foo() override { /* override */ }
    void bar() override { /* implement */ }
};

// Transpiles to: Function pointers in vtable structs
```

#### ✅ Constructors and Destructors (RAII)
```cpp
// SUPPORTED
class Resource {
    int* data_;
public:
    Resource(int size) : data_(new int[size]) {}
    ~Resource() { delete[] data_; }
};

// Transpiles to: Init/destroy functions with manual calls
```

#### ✅ Operator Overloading
```cpp
// SUPPORTED
class Complex {
    double real_, imag_;
public:
    Complex operator+(const Complex& other) const {
        return Complex(real_ + other.real_, imag_ + other.imag_);
    }

    bool operator==(const Complex& other) const {
        return real_ == other.real_ && imag_ == other.imag_;
    }
};

// Transpiles to: Named functions (Complex_add, Complex_eq)
```

#### ✅ Member Functions (Methods)
```cpp
// SUPPORTED
class Calculator {
public:
    int add(int a, int b) const { return a + b; }
    static int multiply(int a, int b) { return a * b; }
};

// Transpiles to:
// int Calculator_add(const struct Calculator* self, int a, int b);
// int Calculator_multiply(int a, int b);  // static -> no self param
```

#### ✅ Namespaces
```cpp
// SUPPORTED - Single namespaces
namespace math {
    class Vector3D { /* ... */ };
    void rotate(Vector3D& v);
}

// Transpiles to: Name mangling
// struct math_Vector3D { /* ... */ };
// void math_rotate(struct math_Vector3D* v);

// SUPPORTED - Nested namespaces
namespace graphics::rendering {
    class Renderer { /* ... */ };
}

// Transpiles to:
// struct graphics_rendering_Renderer { /* ... */ };

// SUPPORTED - Anonymous namespaces (file-local scope)
namespace {
    void internalHelper() { /* ... */ }
}

// Transpiles to:
// static void _anon_file_cpp_42_internalHelper(void) { /* ... */ }

// SUPPORTED - Scoped enums in namespaces
namespace game {
    enum class State { Menu, Playing, Paused };
}

// Transpiles to:
// enum { game_State__Menu, game_State__Playing, game_State__Paused };

// NOT SUPPORTED - using directives
// using namespace std;  // NOT SUPPORTED - use explicit qualification

// NOT SUPPORTED - Namespace aliases
// namespace short_name = very::long::namespace;  // NOT SUPPORTED

// Pattern: namespace1_namespace2_identifier
// See: docs/features/NAMESPACE_GUIDE.md for complete documentation
```

---

### Templates and Generic Programming

#### ✅ Class Templates (Monomorphization)
```cpp
// SUPPORTED
template<typename T>
class Stack {
    T* data_;
    size_t size_;
public:
    void push(const T& value) { /* ... */ }
    T pop() { /* ... */ }
};

// Usage:
Stack<int> intStack;
Stack<double> doubleStack;

// Transpiles to:
// struct Stack_int { int* data_; size_t size_; };
// struct Stack_double { double* data_; size_t size_; };
// (Separate types for each instantiation)
```

#### ✅ Function Templates
```cpp
// SUPPORTED
template<typename T>
T max(T a, T b) {
    return a > b ? a : b;
}

// Usage:
int result = max(10, 20);
double result2 = max(3.14, 2.71);

// Transpiles to:
// int max_int(int a, int b);
// double max_double(double a, double b);
```

#### ✅ Template Specialization (Explicit)
```cpp
// SUPPORTED (with limitations)
template<typename T>
class Container {
    T value_;
};

template<>
class Container<bool> {
    // Special implementation for bool
    unsigned char value_;
};

// Transpiles to: Separate struct definitions
```

---

### C++11/14/17/20/23 Features

#### ✅ auto Type Deduction
```cpp
// SUPPORTED
auto x = 42;              // Deduced as int
auto y = 3.14;            // Deduced as double
auto& ref = someVariable; // Reference

// Transpiles to: Explicit types after deduction
```

#### ✅ nullptr
```cpp
// SUPPORTED
int* ptr = nullptr;

// Transpiles to:
// int* ptr = NULL;  (or ((void*)0))
```

#### ✅ constexpr (Compile-Time Evaluation)
```cpp
// SUPPORTED (with limitations)
constexpr int factorial(int n) {
    return n <= 1 ? 1 : n * factorial(n - 1);
}

constexpr int value = factorial(5);  // Evaluated at compile time

// Transpiles to: Constant value (120) if evaluable
```

#### ✅ C++23: Multidimensional Subscript Operator
```cpp
// SUPPORTED
class Matrix {
public:
    double operator[](int row, int col) const {
        return data_[row * cols_ + col];
    }
};

// Transpiles to: Named function (Matrix_subscript_2d)
```

#### ✅ C++23: Static Operator Functions
```cpp
// SUPPORTED
class Compare {
public:
    static bool operator==(const T& a, const T& b) {
        return a.id == b.id;
    }
};

// Transpiles to: Static function (Compare_eq_static)
```

#### ✅ C++23: [[assume]] Attribute
```cpp
// SUPPORTED
void process(int* ptr) {
    [[assume(ptr != nullptr)]];
    // Compiler can optimize based on assumption
}

// Transpiles to: __builtin_assume() or similar
```

#### ✅ C++23: if consteval
```cpp
// SUPPORTED (with runtime fallback)
int compute(int x) {
    if consteval {
        return x * 2;  // Compile-time
    } else {
        return x + x;  // Runtime
    }
}

// Transpiles to: Runtime branch (compile-time branch omitted)
```

#### ✅ C++20: Deducing this (PARTIAL - Clang 18+ only)
```cpp
// SUPPORTED (requires Clang 18+)
class Builder {
    auto&& with_name(this auto&& self, std::string name) {
        self.name_ = std::move(name);
        return std::forward<decltype(self)>(self);
    }
};

// Note: Currently blocked by Clang 17 API limitations
```

---

### Type System

#### ✅ Fundamental Types
```cpp
// SUPPORTED
bool, char, short, int, long, long long
float, double, long double
unsigned variants
void, void*
```

#### ✅ Enums
```cpp
// SUPPORTED
enum Color { RED, GREEN, BLUE };
enum class Status { OK, ERROR };  // scoped enums

// Transpiles to: C enums with name mangling for scoped enums
```

#### ✅ Pointers and References
```cpp
// SUPPORTED
int* ptr = &variable;
int& ref = variable;
const int* const_ptr = &value;

// Transpiles to: Pointers (references become pointers)
```

#### ✅ Arrays (Stack-Allocated)
```cpp
// SUPPORTED
int arr[10];
int matrix[3][3];

// Transpiles to: Same C arrays
```

---

## Current Limitations (NOT SUPPORTED)

### STL Containers and Utilities

#### ❌ std::string
```cpp
// NOT SUPPORTED
std::string name = "Alice";
name += " Smith";

// WORKAROUND: Use char* with manual memory management
char* name = strdup("Alice");
char* fullName = malloc(strlen(name) + strlen(" Smith") + 1);
strcpy(fullName, name);
strcat(fullName, " Smith");
free(name);
free(fullName);
```

#### ❌ std::vector<T>
```cpp
// NOT SUPPORTED
std::vector<int> numbers;
numbers.push_back(42);

// WORKAROUND: Use C arrays or custom dynamic array
int* numbers = NULL;
size_t size = 0, capacity = 0;
// Manual resize logic...
```

#### ❌ std::map<K,V>, std::unordered_map<K,V>
```cpp
// NOT SUPPORTED
std::map<std::string, int> ages;
ages["Alice"] = 30;

// WORKAROUND: Implement custom hash table or use linear search
```

#### ❌ std::unique_ptr<T>, std::shared_ptr<T>
```cpp
// NOT SUPPORTED
auto ptr = std::make_unique<Resource>();

// WORKAROUND: Manual new/delete with RAII discipline
Resource* res = new Resource();
// ... use res ...
delete res;  // Don't forget!
```

#### ❌ std::function<R(Args...)>
```cpp
// NOT SUPPORTED
std::function<int(int, int)> op = [](int a, int b) { return a + b; };

// WORKAROUND: Function pointers + void* context
int (*op)(void*, int, int);
void* context;
```

#### ❌ std::optional<T>, std::variant<T...>, std::any
```cpp
// NOT SUPPORTED
std::optional<int> maybeValue = std::nullopt;
std::variant<int, double> value = 42;

// WORKAROUND: Manual tagged unions
struct optional_int { bool has_value; int value; };
struct variant_int_double { int tag; union { int i; double d; } value; };
```

---

### Modern C++ Features

#### ❌ Lambda Expressions
```cpp
// NOT SUPPORTED
auto lambda = [](int x) { return x * 2; };
std::for_each(vec.begin(), vec.end(), [](int& x) { x *= 2; });

// WORKAROUND: Named functions or function pointers
int double_value(int x) { return x * 2; }
```

#### ❌ Range-Based For Loops
```cpp
// NOT SUPPORTED
for (const auto& item : collection) {
    process(item);
}

// WORKAROUND: Traditional for loops
for (size_t i = 0; i < collection_size; ++i) {
    process(collection[i]);
}
```

#### ❌ Move Semantics (std::move, rvalue references)
```cpp
// NOT SUPPORTED
std::string str = std::move(otherStr);  // Move, not copy

// WORKAROUND: Manual transfer + clear
char* str = other_str;
other_str = NULL;
```

#### ❌ Perfect Forwarding (std::forward)
```cpp
// NOT SUPPORTED (in user code)
template<typename T>
void wrapper(T&& arg) {
    target(std::forward<T>(arg));
}

// WORKAROUND: Pass by value or const reference
```

#### ❌ Variadic Templates
```cpp
// NOT SUPPORTED
template<typename... Args>
void print(Args... args) {
    ((std::cout << args << " "), ...);
}

// WORKAROUND: Fixed-arity overloads or C varargs (unsafe)
```

---

### Exception Handling

#### ⚠️ Exceptions (PARTIAL SUPPORT)
```cpp
// BASIC SUPPORT ONLY
try {
    if (error) throw std::runtime_error("Error");
} catch (const std::exception& e) {
    handle(e);
}

// Limitations:
// - RAII cleanup during unwinding is INCOMPLETE
// - Stack unwinding across complex control flow MAY FAIL
// - std::exception hierarchy NOT SUPPORTED (no STL)

// WORKAROUND: Error codes or manual setjmp/longjmp
int error = do_operation();
if (error != 0) {
    handle_error(error);
}
```

---

### Advanced C++ Features

#### ❌ Virtual Inheritance
```cpp
// NOT SUPPORTED
class A { };
class B : virtual public A { };
class C : virtual public A { };
class D : public B, public C { };

// WORKAROUND: Redesign to avoid virtual inheritance
```

#### ❌ RTTI (dynamic_cast with polymorphic classes)
```cpp
// NOT SUPPORTED (yet - planned)
Base* ptr = getDerived();
Derived* derived = dynamic_cast<Derived*>(ptr);

// Current: type_info tables exist but dynamic_cast not fully working
```

#### ❌ Co_routines (C++20)
```cpp
// NOT SUPPORTED
generator<int> fibonacci() {
    int a = 0, b = 1;
    while (true) {
        co_yield a;
        auto next = a + b;
        a = b;
        b = next;
    }
}

// WORKAROUND: State machine pattern
```

#### ❌ Concepts (C++20)
```cpp
// NOT SUPPORTED
template<typename T>
concept Addable = requires(T a, T b) {
    { a + b } -> std::same_as<T>;
};

// WORKAROUND: SFINAE or runtime checks
```

---

## Example: Transpilable C++ Projects

### Example 1: Math Library (Pure Transpilable C++)

```cpp
// vector3d.h
class Vector3D {
private:
    double x_, y_, z_;

public:
    Vector3D(double x = 0, double y = 0, double z = 0)
        : x_(x), y_(y), z_(z) {}

    double dot(const Vector3D& other) const {
        return x_ * other.x_ + y_ * other.y_ + z_ * other.z_;
    }

    Vector3D cross(const Vector3D& other) const {
        return Vector3D(
            y_ * other.z_ - z_ * other.y_,
            z_ * other.x_ - x_ * other.z_,
            x_ * other.y_ - y_ * other.x_
        );
    }

    double magnitude() const {
        return sqrt(x_ * x_ + y_ * y_ + z_ * z_);
    }

    Vector3D operator+(const Vector3D& other) const {
        return Vector3D(x_ + other.x_, y_ + other.y_, z_ + other.z_);
    }

    Vector3D operator*(double scalar) const {
        return Vector3D(x_ * scalar, y_ * scalar, z_ * scalar);
    }
};
```

**Transpilability**: ✅ 100% - No STL, no complex features, pure computation

---

### Example 2: Custom Container (Transpilable)

```cpp
// fixed_array.h
template<typename T, size_t N>
class FixedArray {
private:
    T data_[N];
    size_t size_;

public:
    FixedArray() : size_(0) {}

    void push(const T& value) {
        if (size_ < N) {
            data_[size_++] = value;
        }
    }

    T& operator[](size_t index) {
        return data_[index];
    }

    const T& operator[](size_t index) const {
        return data_[index];
    }

    size_t size() const { return size_; }
    size_t capacity() const { return N; }
};

// Usage:
FixedArray<int, 100> numbers;
numbers.push(42);
```

**Transpilability**: ✅ 100% - Stack-allocated array, template monomorphization works

---

### Example 3: State Machine (Transpilable)

```cpp
// state_machine.h
class State {
public:
    virtual ~State() {}
    virtual void enter() = 0;
    virtual void update() = 0;
    virtual void exit() = 0;
};

class IdleState : public State {
public:
    void enter() override { /* ... */ }
    void update() override { /* ... */ }
    void exit() override { /* ... */ }
};

class StateMachine {
private:
    State* currentState_;

public:
    StateMachine() : currentState_(nullptr) {}

    void changeState(State* newState) {
        if (currentState_) {
            currentState_->exit();
        }
        currentState_ = newState;
        if (currentState_) {
            currentState_->enter();
        }
    }

    void update() {
        if (currentState_) {
            currentState_->update();
        }
    }
};
```

**Transpilability**: ✅ 100% - Virtual functions, RAII, polymorphism all supported

---

### Example 4: Game Entity System (Transpilable)

```cpp
// entity.h
class Entity {
protected:
    double x_, y_;
    double health_;

public:
    Entity(double x, double y, double health)
        : x_(x), y_(y), health_(health) {}

    virtual ~Entity() {}

    virtual void update(double dt) = 0;
    virtual void render() = 0;

    bool isAlive() const { return health_ > 0; }
    void takeDamage(double amount) { health_ -= amount; }
};

class Player : public Entity {
private:
    double speed_;

public:
    Player(double x, double y)
        : Entity(x, y, 100.0), speed_(5.0) {}

    void update(double dt) override {
        // Update position based on input
    }

    void render() override {
        // Render player sprite
    }

    void moveLeft(double dt) { x_ -= speed_ * dt; }
    void moveRight(double dt) { x_ += speed_ * dt; }
};

class Enemy : public Entity {
public:
    Enemy(double x, double y)
        : Entity(x, y, 50.0) {}

    void update(double dt) override {
        // AI logic
    }

    void render() override {
        // Render enemy sprite
    }
};
```

**Transpilability**: ✅ 100% - Inheritance, virtual functions, polymorphism

---

### Example 5: Simple Parser (Transpilable with Workarounds)

```cpp
// tokenizer.h
enum TokenType { T_NUMBER, T_OPERATOR, T_EOF };

struct Token {
    TokenType type;
    char value[32];  // Fixed-size buffer instead of std::string
};

class Tokenizer {
private:
    const char* input_;
    const char* current_;

public:
    Tokenizer(const char* input) : input_(input), current_(input) {}

    Token nextToken() {
        skipWhitespace();

        Token token;
        if (isdigit(*current_)) {
            token.type = T_NUMBER;
            size_t i = 0;
            while (isdigit(*current_) && i < 31) {
                token.value[i++] = *current_++;
            }
            token.value[i] = '\0';
        } else if (*current_ == '+' || *current_ == '-') {
            token.type = T_OPERATOR;
            token.value[0] = *current_++;
            token.value[1] = '\0';
        } else {
            token.type = T_EOF;
            token.value[0] = '\0';
        }

        return token;
    }

private:
    void skipWhitespace() {
        while (*current_ == ' ' || *current_ == '\t') {
            ++current_;
        }
    }
};
```

**Transpilability**: ✅ 90% - Uses char* instead of std::string, fixed buffers

---

## Workarounds and Best Practices

### Avoiding STL Containers

**Pattern**: Custom Fixed-Size Containers
```cpp
template<typename T, size_t N>
class Array {
    T data_[N];
public:
    T& operator[](size_t i) { return data_[i]; }
    size_t size() const { return N; }
};
```

**Pattern**: C-Style Dynamic Arrays with RAII
```cpp
class DynamicArray {
    int* data_;
    size_t size_;
    size_t capacity_;

public:
    DynamicArray() : data_(nullptr), size_(0), capacity_(0) {}

    ~DynamicArray() {
        delete[] data_;
    }

    void push(int value) {
        if (size_ >= capacity_) {
            resize(capacity_ == 0 ? 8 : capacity_ * 2);
        }
        data_[size_++] = value;
    }

private:
    void resize(size_t newCap) {
        int* newData = new int[newCap];
        for (size_t i = 0; i < size_; ++i) {
            newData[i] = data_[i];
        }
        delete[] data_;
        data_ = newData;
        capacity_ = newCap;
    }
};
```

---

### String Handling

**Pattern**: Use char* with RAII wrappers
```cpp
class String {
    char* data_;

public:
    String(const char* str) {
        size_t len = strlen(str);
        data_ = new char[len + 1];
        strcpy(data_, str);
    }

    ~String() {
        delete[] data_;
    }

    const char* c_str() const { return data_; }
};
```

---

### Error Handling Without Exceptions

**Pattern**: Error codes with result structs
```cpp
enum ErrorCode { SUCCESS = 0, INVALID_INPUT = 1, OUT_OF_MEMORY = 2 };

struct Result {
    ErrorCode error;
    int value;
};

Result divide(int a, int b) {
    if (b == 0) {
        return {INVALID_INPUT, 0};
    }
    return {SUCCESS, a / b};
}

// Usage:
Result r = divide(10, 2);
if (r.error != SUCCESS) {
    // Handle error
}
```

---

## Domain-Specific Applicability

### High Transpilability Domains (80-100%)

✅ **Embedded Systems**
- Typically avoid STL for determinism
- Custom containers and allocators
- Heavy use of templates for zero-cost abstractions

✅ **Game Engines (Core)**
- Custom allocators and containers
- Entity-component systems
- Physics engines (pure math)

✅ **Math Libraries**
- Template-heavy, STL-free
- Vector, matrix, quaternion operations
- Signal processing, numerical methods

✅ **Device Drivers / Kernel Modules**
- No STL allowed (kernel space)
- Strict RAII discipline
- Template metaprogramming for compile-time optimization

---

### Medium Transpilability Domains (40-70%)

⚠️ **Systems Programming**
- Some STL usage (std::vector, std::string)
- Can often refactor to avoid STL
- Performance-critical paths may already be STL-free

⚠️ **Game Logic / Gameplay Code**
- May use std::vector, std::map for convenience
- Can refactor to custom containers
- Event systems may use std::function (can use function pointers)

---

### Low Transpilability Domains (10-30%)

❌ **Web Services / APIs**
- Heavy std::string, std::vector, std::map usage
- JSON parsing (requires std::map)
- HTTP clients (requires std::string)

❌ **Desktop Applications**
- GUI frameworks (Qt, wxWidgets) use STL extensively
- File I/O with std::ifstream, std::ofstream
- std::thread for concurrency

❌ **Data Processing**
- std::vector for datasets
- std::map for lookups
- STL algorithms for transformations

---

## Migration Guide

### Assessing Transpilability of Existing Code

**Step 1**: Grep for STL usage
```bash
grep -r "std::" --include="*.cpp" --include="*.h" | wc -l
```

**Step 2**: Count critical STL types
```bash
grep -r "std::string\|std::vector\|std::map\|std::unique_ptr" \
    --include="*.cpp" --include="*.h" | wc -l
```

**Step 3**: Estimate refactoring effort
- If < 10 STL uses: 1-2 days to refactor
- If 10-50 STL uses: 1-2 weeks to refactor
- If 50-200 STL uses: 1-2 months to refactor
- If > 200 STL uses: Wait for STL support or don't transpile

---

### Refactoring Strategy

**For std::string**:
1. Replace with `const char*` for read-only strings
2. Use `char*` with malloc/free for mutable strings
3. Wrap in RAII class for automatic cleanup

**For std::vector<T>**:
1. Use stack arrays if size is known: `T arr[N]`
2. Use custom dynamic array class (see examples)
3. Use C-style realloc for simple cases

**For std::map<K,V>**:
1. Use linear search for small datasets
2. Implement custom hash table
3. Sort array + binary search

---

## Roadmap for Future Support

### v3.0.0 (Current - STL-Free)
- ✅ Classes, inheritance, virtual functions
- ✅ Templates (class and function)
- ✅ C++23 features (multidim subscript, static operators, [[assume]], if consteval, auto(x))
- ✅ Multi-file projects
- ❌ STL containers
- ❌ Smart pointers
- ❌ Lambdas

### v4.0.0 (Planned - Critical STL Subset)
- ✅ std::string
- ✅ std::vector<T>
- ✅ std::unique_ptr<T>
- ✅ std::map<K,V> (as std::unordered_map)
- ⚠️ Exceptions (improved RAII cleanup)
- ❌ std::shared_ptr, std::function, lambdas

### v5.0.0 (Future - Extended STL)
- ✅ std::shared_ptr<T>
- ✅ std::function<R(Args...)>
- ✅ Lambdas
- ✅ std::optional<T>, std::variant<Ts...>
- ✅ Range-based for loops
- ✅ Move semantics (std::move)

### v6.0.0 (Long-Term - Full Modern C++)
- ✅ Variadic templates
- ✅ Coroutines
- ✅ Concepts
- ✅ Full STL algorithm support

---

## Conclusion

**Transpilable C++ is a practical subset** for:
- Embedded systems developers
- Game engine core developers
- Math library authors
- Legacy C++ → C migration projects
- Security-critical code requiring auditability

**Current transpiler covers**: ~30% of real-world C++ codebases

**With v4.0.0 (Critical STL Subset)**: ~70% coverage

**Full coverage**: v6.0.0+ (2-3 years out)

**Recommendation**: If your project heavily uses STL, wait for v4.0.0. If your project is STL-light or can be refactored, the transpiler is ready for use today.

---

## Resources

- [FEATURE-MATRIX.md](FEATURE-MATRIX.md) - Detailed feature support status
- [STL_USAGE_ANALYSIS.md](../.planning/phases/35-post-phase34-foundation/STL_USAGE_ANALYSIS.md) - Real-world STL usage patterns
- [STL_IMPLEMENTATION_ESTIMATES.md](../.planning/phases/35-post-phase34-foundation/STL_IMPLEMENTATION_ESTIMATES.md) - Timeline for STL support
- [TESTING.md](TESTING.md) - How to test your transpilable C++ code

---

**Generated**: 2025-12-24
**Version**: v3.0.0-draft
**Status**: Subject to refinement
