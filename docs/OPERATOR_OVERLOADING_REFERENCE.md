# Operator Overloading Reference

## Overview

This document provides a quick reference for all supported C++ operator overloads and their translations to C. Operators are organized by phase and category.

**Current Support**: Phase 50-51 complete, Phase 52 planned

| Phase | Category | Operators | Status |
|-------|----------|-----------|--------|
| **Phase 50** | Arithmetic | `+`, `-`, `*`, `/`, `%`, unary `-`, `++`, `--`, `+=`, `-=`, `*=`, `/=` | Complete (v2.10.0) |
| **Phase 51** | Comparison & Logical | `<`, `>`, `<=`, `>=`, `==`, `!=`, `!`, `&&`, `\|\|` | Complete (v2.11.0) |
| **Phase 52** | Special Operators | `[]`, `()`, `->`, `*`, `<<`, `>>`, conversion ops, `=` | Planned (v2.12.0) |

---

## Phase 50: Arithmetic Operators (v2.10.0)

See [ARITHMETIC_OPERATORS.md](ARITHMETIC_OPERATORS.md) for detailed guide.

### Binary Operators

| C++ Operator | Function Name | Example | Returns | Notes |
|--------------|---------------|---------|---------|-------|
| `+` | `_operator_plus` | `a + b` | Same type | Addition |
| `-` | `_operator_minus` | `a - b` | Same type | Subtraction |
| `*` | `_operator_multiply` | `a * b` | Same type | Multiplication |
| `/` | `_operator_divide` | `a / b` | Same type | Division |
| `%` | `_operator_modulo` | `a % b` | Same type | Modulo |

**Example**:
```cpp
// C++
Vector c = a + b;

// C
Vector c = Vector_operator_plus_const_Vector_ref(&a, &b);
```

### Unary Operators

| C++ Operator | Function Name | Example | Returns | Notes |
|--------------|---------------|---------|---------|-------|
| Unary `-` | `_operator_minus` | `-a` | Same type | Negation |

**Example**:
```cpp
// C++
Vector negated = -v;

// C
Vector negated = Vector_operator_minus_const(&v);
```

### Increment/Decrement

| C++ Operator | Function Name | Example | Returns | Notes |
|--------------|---------------|---------|---------|-------|
| Prefix `++` | `_operator_pre_increment` | `++x` | Reference | Increment, return new value |
| Postfix `++` | `_operator_post_increment` | `x++` | Value | Increment, return old value |
| Prefix `--` | `_operator_pre_decrement` | `--x` | Reference | Decrement, return new value |
| Postfix `--` | `_operator_post_decrement` | `x--` | Value | Decrement, return old value |

**Example**:
```cpp
// C++
int i = 0;
printf("%d\n", ++i);  // Prints 1
printf("%d\n", i++);  // Prints 1 (returns old value)

// C
int i = 0;
printf("%d\n", Integer_operator_pre_increment(&i));   // &i modified in place
printf("%d\n", Integer_operator_post_increment(&i));  // Returns copy of old value
```

### Compound Assignment

| C++ Operator | Function Name | Example | Notes |
|--------------|---------------|---------|-------|
| `+=` | `_operator_plus_equal` | `a += b` | Usually `a = a + b` |
| `-=` | `_operator_minus_equal` | `a -= b` | Usually `a = a - b` |
| `*=` | `_operator_multiply_equal` | `a *= b` | Usually `a = a * b` |
| `/=` | `_operator_divide_equal` | `a /= b` | Usually `a = a / b` |

**Example**:
```cpp
// C++
Vector v{1, 2};
v += Vector{3, 4};  // v becomes {4, 6}

// C
Vector v = {1, 2};
Vector_operator_plus_equal_Vector_ref(&v, &Vector_ref_3_4);
```

---

## Phase 51: Comparison & Logical Operators (v2.11.0)

See [COMPARISON_OPERATORS.md](COMPARISON_OPERATORS.md) for detailed guide.

### Relational Operators

| C++ Operator | Function Name | Example | Returns | Notes |
|--------------|---------------|---------|---------|-------|
| `<` | `_operator_less` | `a < b` | `bool` | Less than |
| `>` | `_operator_greater` | `a > b` | `bool` | Greater than |
| `<=` | `_operator_less_equal` | `a <= b` | `bool` | Less or equal |
| `>=` | `_operator_greater_equal` | `a >= b` | `bool` | Greater or equal |

**Example**:
```cpp
// C++
Date d1{2024, 12, 25}, d2{2025, 1, 1};
if (d1 < d2) { /* ... */ }

// C
Date d1 = {2024, 12, 25}, d2 = {2025, 1, 1};
if (Date_operator_less_const_Date_ref(&d1, &d2)) { /* ... */ }
```

### Equality Operators

| C++ Operator | Function Name | Example | Returns | Notes |
|--------------|---------------|---------|---------|-------|
| `==` | `_operator_equal` | `a == b` | `bool` | Equality |
| `!=` | `_operator_not_equal` | `a != b` | `bool` | Inequality |

**Example**:
```cpp
// C++
if (r1 == r2) { /* ... */ }

// C
if (Rational_operator_equal_const_Rational_ref(&r1, &r2)) { /* ... */ }
```

### Logical Operators

| C++ Operator | Function Name | Example | Returns | Notes |
|--------------|---------------|---------|---------|-------|
| `!` | `_operator_not` | `!a` | `bool` | Logical NOT (unary) |
| `&&` | `_operator_and` | `a && b` | `bool` | Logical AND **⚠️ Loses short-circuit** |
| `\|\|` | `_operator_or` | `a \|\| b` | `bool` | Logical OR **⚠️ Loses short-circuit** |

**Example - Logical NOT**:
```cpp
// C++
class Optional { bool has_value; };
Optional opt = getSome();
if (!opt) { /* ... */ }

// C
bool Optional_operator_not_const(const Optional* this);
if (Optional_operator_not_const(&opt)) { /* ... */ }
```

**Example - Logical AND (⚠️ WARNING)**:
```cpp
// C++ - short-circuits, doesn't evaluate condition2 if condition1 is false
if (condition1 && condition2) { /* ... */ }

// C - ALWAYS evaluates both conditions
if (Condition_operator_and_const_Condition_ref(&condition1, &condition2)) { /* ... */ }
```

**⚠️ Critical Warning**: `&&` and `||` are **STRONGLY DISCOURAGED** for overloading because:
- C++ `&&` and `||` short-circuit (don't evaluate 2nd operand if result is known)
- Transpiled C evaluates both operands
- Changes program behavior and can cause errors
- **Solution**: Use `operator bool()` (Phase 52) instead

---

## Phase 52: Special Operators (v2.12.0)

*Planned for future implementation*

### Subscript and Call

| C++ Operator | Purpose | Example |
|--------------|---------|---------|
| `[]` | Element access | `arr[i]` |
| `()` | Function call | `obj()` |

### Smart Pointer/Dereference

| C++ Operator | Purpose | Example |
|--------------|---------|---------|
| `->` | Member access through pointer | `ptr->method()` |
| `*` | Dereference | `*ptr` |

### Stream I/O

| C++ Operator | Purpose | Example |
|--------------|---------|---------|
| `<<` | Output stream | `std::cout << obj` |
| `>>` | Input stream | `std::cin >> obj` |

### Conversion and Assignment

| C++ Operator | Purpose | Example |
|--------------|---------|---------|
| `T()` | Conversion to type T | `int(obj)` |
| `operator bool` | Boolean conversion | `if (obj) { }` |
| `=` | Assignment/copy | `a = b` |

### Rare Operators

| C++ Operator | Purpose | Notes |
|--------------|---------|-------|
| `&` | Address-of (rarely overloaded) | Unusual semantics |
| `,` | Comma (rarely overloaded) | Unusual semantics |

---

## Function Naming Convention

The transpiler uses systematic naming for all operators:

### Pattern

```
ClassName_operator_OPERATOR_QUALIFIERS
```

Where:
- **ClassName**: The class containing the operator
- **OPERATOR**: The operator name (less, plus, etc.)
- **QUALIFIERS**: Const and parameter information

### Examples

| C++ Code | C Function Name |
|----------|-----------------|
| `Vector::operator+` | `Vector_operator_plus_const_Vector_ref` |
| `Date::operator<` | `Date_operator_less_const_Date_ref` |
| `Point::operator==` | `Point_operator_equal_const_Point_ref` |
| `Optional::operator!` | `Optional_operator_not_const` |
| `Score::operator<` (non-const) | `Score_operator_less_Score_ref` |

### Const Member Functions

Const member functions add `_const` before the parameter type:

```cpp
// C++ - const member function
bool operator<(const Score& other) const;

// C - const this pointer
bool Score_operator_less_const_Score_ref(
    const Score* this,        // Note: const qualifier
    const Score* other
);
```

### Friend (Non-Member) Operators

Friend operators omit the implicit `this` parameter:

```cpp
// C++ - friend function
friend bool operator==(const Vector& lhs, const Vector& rhs);

// C - explicit two parameters
bool Vector_operator_equal_friend(
    const Vector* lhs,
    const Vector* rhs
);
```

---

## Translation Mechanics

### Member vs Friend

**Member operator** (implicit `this`):
```cpp
class Vector {
    double x, y;
public:
    bool operator==(const Vector& other) const;
};

// C function has explicit this parameter
bool Vector_operator_equal_const_Vector_ref(
    const Vector* this,
    const Vector* other
);
```

**Friend operator** (explicit parameters):
```cpp
class Vector {
    double x, y;
    friend bool operator==(const Vector& lhs, const Vector& rhs);
};

// C function has two explicit parameters
bool Vector_operator_equal_friend(
    const Vector* lhs,
    const Vector* rhs
);
```

### Call Site Transformation

**Member operator call**:
```cpp
// C++
Vector v1{1, 2}, v2{3, 4};
if (v1 == v2) { /* ... */ }

// C - address-of for both operands
Vector v1 = {1, 2}, v2 = {3, 4};
if (Vector_operator_equal_const_Vector_ref(&v1, &v2)) { /* ... */ }
```

**Friend operator call**:
```cpp
// C++ - symmetric
if (v1 == v2) { /* ... */ }

// C - still symmetric (friend has two parameters)
if (Vector_operator_equal_friend(&v1, &v2)) { /* ... */ }
```

### Overloading Resolution

When multiple versions exist (e.g., different parameter types), the transpiler uses the same approach as C++ name mangling:

```cpp
// Multiple overloads
class Number {
    int value;
public:
    bool operator<(int other) const;
    bool operator<(double other) const;
    bool operator<(const Number& other) const;
};

// Become distinct C functions
bool Number_operator_less_int(const Number* this, int other);
bool Number_operator_less_double(const Number* this, double other);
bool Number_operator_less_const_Number_ref(const Number* this, const Number* other);
```

---

## Type Requirements

### Return Types

Most operators return specific types:

| Operator | Return Type | Notes |
|----------|-------------|-------|
| Arithmetic (`+`, `-`, `*`, `/`, `%`) | Same as operand type | Usually |
| Comparison (`<`, `>`, `<=`, `>=`, `==`, `!=`) | `bool` | Always |
| Logical (`!`, `&&`, `\|\|`) | `bool` | Always |
| Increment/Decrement (prefix) | Reference | Pointer in C |
| Increment/Decrement (postfix) | Value | Copy |

### Parameter Types

Parameters must follow certain patterns:

| Category | Typical Pattern | Notes |
|----------|-----------------|-------|
| Binary operators | `const ClassName&` | Value comparison |
| Comparison | `const ClassName&` | const correct |
| Unary operators | None (besides `this`) | Operate on self |

---

## Best Practices

### 1. Implement Systematically

For relational operators, implement `<` canonically:
```cpp
bool operator<(const Date& other) const {
    // Full implementation
    if (year != other.year) return year < other.year;
    if (month != other.month) return month < other.month;
    return day < other.day;
}

// Others derived from <
bool operator>(const Date& other) const {
    return other < *this;
}
```

### 2. Const Correctness

Always mark comparison operators as `const`:
```cpp
// GOOD
bool operator<(const Score& other) const;

// WRONG
bool operator<(const Score& other);  // Non-const!
```

### 3. Use References, Not Pointers

Always use const references for parameters:
```cpp
// GOOD
bool operator==(const Point& other) const;

// INEFFICIENT
bool operator==(const Point other) const;  // Copies parameter

// INCOMPATIBLE
bool operator==(const Point* other) const;  // Use pointers
```

### 4. Avoid && and || Overloading

Use `operator bool()` instead:
```cpp
// GOOD - operator bool() preserves short-circuit
class Optional {
    explicit operator bool() const { return has_value; }
};
if (opt1 && opt2) { /* ... */ }  // Short-circuits correctly!

// BAD - operator&& loses short-circuit
class Optional {
    bool operator&&(const Optional& other) const {
        return has_value && other.has_value;  // Both always evaluated
    }
};
if (opt1 && opt2) { /* ... */ }  // Both operands always evaluated!
```

### 5. Maintain Consistency

Ensure all comparison operators agree:
```cpp
// GOOD - all consistent
if (a < b) { /* ... */ }      // Uses <
if (!(a < b) && !(b < a)) { /* ... */ }  // Equivalent to ==
if (b < a || (!(a < b) && !(b < a))) { /* ... */ }  // Equivalent to >=

// BAD - inconsistent
bool operator<(const Score& other) const { return points < other.points; }
bool operator==(const Score& other) const { return name == other.name; }  // Different field!
```

---

## Common Patterns

### Vector/Matrix Math (Phase 50)

```cpp
class Vector {
    double x, y, z;
public:
    Vector operator+(const Vector& other) const;
    Vector operator-(const Vector& other) const;
    Vector operator*(double scalar) const;
    double operator*(const Vector& other) const;  // Dot product
};

Vector v1{1, 2, 3}, v2{4, 5, 6};
Vector sum = v1 + v2;           // Addition
Vector diff = v1 - v2;          // Subtraction
Vector scaled = v1 * 2.0;       // Scalar multiplication
double dot = v1 * v2;           // Dot product
```

### Sorting and Searching (Phase 51)

```cpp
class Person {
    std::string name;
    int age;
public:
    bool operator<(const Person& other) const {
        if (age != other.age) return age < other.age;
        return name < other.name;
    }
};

std::vector<Person> people = { /* ... */ };
std::sort(people.begin(), people.end());  // Uses operator<
```

### Custom Containers (Phase 52)

```cpp
class Vector {
public:
    int& operator[](int index);
    const int& operator[](int index) const;
};

Vector v = { /* ... */ };
int first = v[0];    // Uses operator[]
v[0] = 42;           // Uses operator[]
```

---

## Limitations and Workarounds

### Short-Circuit Evaluation Loss

**Problem**: `&&` and `||` lose short-circuit in transpilation.

**Workaround**: Use `operator bool()` (Phase 52):
```cpp
class Optional {
    explicit operator bool() const { return has_value; }
};

if (opt1 && opt2) { /* Short-circuit preserved! */ }
```

### Pointer Parameter Syntax

**Problem**: Some code uses pointer parameters instead of references.

**Workaround**: Use references in operator declarations:
```cpp
// GOOD - use references
bool operator<(const Date& other) const;

// LESS IDEAL - use pointers (transpilation less clean)
bool operator<(const Date* other) const;  // Avoid if possible
```

---

## See Also

- [ARITHMETIC_OPERATORS.md](ARITHMETIC_OPERATORS.md) - Phase 50 detailed guide
- [COMPARISON_OPERATORS.md](COMPARISON_OPERATORS.md) - Phase 51 detailed guide
- [Operator Overloading Roadmap](.planning/OPERATOR_OVERLOADING_ROADMAP.md) - Implementation plan
- [Namespace Support Guide](features/NAMESPACE_GUIDE.md) - Using operators with namespaces
- [Method Generation](METHOD_GENERATION.md) - How operators become functions

