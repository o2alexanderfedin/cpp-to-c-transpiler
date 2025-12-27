# Comparison Operators Guide

## Overview

This guide explains how the C++ to C transpiler handles comparison operators, including relational operators (`<`, `>`, `<=`, `>=`), equality operators (`==`, `!=`), and logical operators (`!`, `&&`, `||`). The transpiler translates these operator overloads to explicit C function calls, enabling custom types to work with standard C algorithms and control flow.

## Why Comparison Operators Matter

Comparison operators are **critical** for:

- **Sorting**: Custom types need `<` to work with `std::sort`, `std::set`, `std::map`
- **Searching**: Binary search requires comparison operators (`<`, `==`)
- **Conditional Logic**: Natural comparisons in `if` statements and loops
- **Standard Algorithms**: Generic algorithms like `std::find`, `std::lower_bound`, `std::unique`
- **Custom Types**: Defining natural ordering for user-defined types (Date, Rational, Point, etc.)

## Translation Patterns

### Pattern Overview

All comparison operators follow a consistent translation pattern:

```cpp
// C++ Member Operator
bool ClassName::operator@(const ClassName& other) const { ... }

// C Function
bool ClassName_operator_@_const_ClassName_ref(const ClassName* this, const ClassName* other) { ... }

// Call Site
if (a @ b) { ... }                           // C++
if (ClassName_operator_@(&a, &b)) { ... }   // C
```

Where `@` is replaced with the operator symbol (`<`, `>`, `==`, `!=`, etc.).

### Const Correctness

Comparison operators typically declare both:
- **Const method** (the `this` pointer is const)
- **Const parameter** (the compared object is const)

This translates to `const` pointers in C:

```c
bool Date_operator_less_const_Date_ref(
    const Date* this,        // Const this pointer
    const Date* other        // Const parameter pointer
);
```

---

## Relational Operators (< > <= >=)

Relational operators establish a natural ordering of values. They form the foundation for sorting and searching.

### Less-Than Operator (<)

**Purpose**: Determines if the left operand is strictly less than the right operand.

**C++ Code**:
```cpp
class Date {
    int year, month, day;
public:
    bool operator<(const Date& other) const {
        if (year != other.year) return year < other.year;
        if (month != other.month) return month < other.month;
        return day < other.day;
    }
};

int main() {
    Date d1{2024, 12, 25}, d2{2025, 1, 1};
    if (d1 < d2) {
        printf("d1 comes before d2\n");
    }
}
```

**Transpiled C Code**:
```c
#include <stdbool.h>

typedef struct {
    int year, month, day;
} Date;

// Function declaration
bool Date_operator_less_const_Date_ref(
    const Date* this,
    const Date* other
);

// Function implementation
bool Date_operator_less_const_Date_ref(
    const Date* this,
    const Date* other
) {
    if (this->year != other->year) return this->year < other->year;
    if (this->month != other->month) return this->month < other->month;
    return this->day < other->day;
}

int main(void) {
    Date d1 = {2024, 12, 25}, d2 = {2025, 1, 1};
    if (Date_operator_less_const_Date_ref(&d1, &d2)) {
        printf("d1 comes before d2\n");
    }
}
```

**Key Characteristics**:
- Returns `bool` (true if left < right, false otherwise)
- Typically `const` member function
- Establishes strict weak ordering (irreflexive, transitive, asymmetric)
- Canonical operator - others (`>`, `<=`, `>=`) often implemented in terms of `<`

**Use Cases**:
- Sorting arrays and containers
- Binary search (requires `<` to work correctly)
- Tree-based containers (std::map, std::set)
- Generic algorithms (std::lower_bound, std::upper_bound)

### Greater-Than Operator (>)

**Purpose**: Determines if the left operand is strictly greater than the right operand.

**C++ Code**:
```cpp
class Score {
    int points;
public:
    bool operator>(const Score& other) const {
        return other < *this;  // Implemented in terms of <
    }
};

int main() {
    Score s1{100}, s2{85};
    if (s1 > s2) {
        printf("s1 has higher score\n");
    }
}
```

**Transpiled C Code**:
```c
#include <stdbool.h>

typedef struct {
    int points;
} Score;

bool Score_operator_less_const_Score_ref(
    const Score* this, const Score* other
);

bool Score_operator_greater_const_Score_ref(
    const Score* this, const Score* other
) {
    // Call < with arguments reversed
    return Score_operator_less_const_Score_ref(other, this);
}

int main(void) {
    Score s1 = {100}, s2 = {85};
    if (Score_operator_greater_const_Score_ref(&s1, &s2)) {
        printf("s1 has higher score\n");
    }
}
```

**Key Characteristics**:
- Returns `bool` (true if left > right)
- Opposite of `<`
- Often implemented as `other < *this`

### Less-Than-or-Equal Operator (<=)

**Purpose**: Determines if the left operand is less than or equal to the right operand.

**C++ Code**:
```cpp
class Price {
    double amount;
public:
    bool operator<(const Price& other) const {
        return amount < other.amount;
    }

    bool operator<=(const Price& other) const {
        return !(other < *this);  // Implemented as NOT(other < this)
    }
};

int main() {
    Price p1{9.99}, p2{10.00};
    if (p1 <= p2) {
        printf("p1 is affordable\n");
    }
}
```

**Transpiled C Code**:
```c
#include <stdbool.h>

typedef struct {
    double amount;
} Price;

bool Price_operator_less_const_Price_ref(
    const Price* this, const Price* other
);

bool Price_operator_less_equal_const_Price_ref(
    const Price* this, const Price* other
) {
    return !Price_operator_less_const_Price_ref(other, this);
}

int main(void) {
    Price p1 = {9.99}, p2 = {10.00};
    if (Price_operator_less_equal_const_Price_ref(&p1, &p2)) {
        printf("p1 is affordable\n");
    }
}
```

**Key Characteristics**:
- Returns `bool` (true if left <= right)
- Commonly implemented as `!(other < *this)`
- Allows equal comparison

### Greater-Than-or-Equal Operator (>=)

**Purpose**: Determines if the left operand is greater than or equal to the right operand.

**C++ Code**:
```cpp
class Temperature {
    double celsius;
public:
    bool operator<(const Temperature& other) const {
        return celsius < other.celsius;
    }

    bool operator>=(const Temperature& other) const {
        return !(*this < other);  // Implemented as NOT(this < other)
    }
};

int main() {
    Temperature t1{37.0}, t2{36.5};
    if (t1 >= t2) {
        printf("t1 is at least as hot as t2\n");
    }
}
```

**Transpiled C Code**:
```c
#include <stdbool.h>

typedef struct {
    double celsius;
} Temperature;

bool Temperature_operator_less_const_Temperature_ref(
    const Temperature* this, const Temperature* other
);

bool Temperature_operator_greater_equal_const_Temperature_ref(
    const Temperature* this, const Temperature* other
) {
    return !Temperature_operator_less_const_Temperature_ref(this, other);
}

int main(void) {
    Temperature t1 = {37.0}, t2 = {36.5};
    if (Temperature_operator_greater_equal_const_Temperature_ref(&t1, &t2)) {
        printf("t1 is at least as hot as t2\n");
    }
}
```

**Key Characteristics**:
- Returns `bool` (true if left >= right)
- Often implemented as `!(*this < other)`
- Allows equal comparison

---

## Equality Operators (== !=)

Equality operators test for exact value equivalence. They have different semantics than relational operators and form an equivalence relation (reflexive, symmetric, transitive).

### Equality Operator (==)

**Purpose**: Determines if two values are exactly equal.

**C++ Code**:
```cpp
class Rational {
    int numerator, denominator;
public:
    bool operator==(const Rational& other) const {
        // Cross-multiply: a/b == c/d ⟺ a*d == b*c
        return numerator * other.denominator ==
               denominator * other.numerator;
    }
};

int main() {
    Rational r1{1, 2}, r2{2, 4};  // 1/2 and 2/4 are equal
    if (r1 == r2) {
        printf("Rationals are equivalent\n");
    }
}
```

**Transpiled C Code**:
```c
#include <stdbool.h>

typedef struct {
    int numerator, denominator;
} Rational;

bool Rational_operator_equal_const_Rational_ref(
    const Rational* this, const Rational* other
);

bool Rational_operator_equal_const_Rational_ref(
    const Rational* this, const Rational* other
) {
    return this->numerator * other->denominator ==
           this->denominator * other->numerator;
}

int main(void) {
    Rational r1 = {1, 2}, r2 = {2, 4};
    if (Rational_operator_equal_const_Rational_ref(&r1, &r2)) {
        printf("Rationals are equivalent\n");
    }
}
```

**Key Characteristics**:
- Returns `bool` (true if values are equal)
- Typically `const` member function
- Canonical equality operator - `!=` usually implemented as `!(==)`
- Forms equivalence relation (reflexive: a==a, symmetric: if a==b then b==a, transitive: if a==b and b==c then a==c)

**Implementation Patterns**:
1. **Value Comparison**: Compare all fields
   ```cpp
   bool operator==(const Point& other) const {
       return x == other.x && y == other.y;
   }
   ```

2. **Smart Comparison**: Cross-products, normalized forms
   ```cpp
   bool operator==(const Rational& other) const {
       return numerator * other.denominator == denominator * other.numerator;
   }
   ```

3. **Pointer/Reference Equality**: Compare addresses (identity)
   ```cpp
   bool operator==(const SmartPtr& other) const {
       return ptr == other.ptr;
   }
   ```

### Inequality Operator (!=)

**Purpose**: Determines if two values are not equal (opposite of `==`).

**C++ Code**:
```cpp
class Vector {
    double x, y;
public:
    bool operator==(const Vector& other) const {
        return x == other.x && y == other.y;
    }

    bool operator!=(const Vector& other) const {
        return !(*this == other);  // Implemented in terms of ==
    }
};

int main() {
    Vector v1{1.0, 2.0}, v2{1.0, 3.0};
    if (v1 != v2) {
        printf("Vectors are different\n");
    }
}
```

**Transpiled C Code**:
```c
#include <stdbool.h>

typedef struct {
    double x, y;
} Vector;

bool Vector_operator_equal_const_Vector_ref(
    const Vector* this, const Vector* other
);

bool Vector_operator_not_equal_const_Vector_ref(
    const Vector* this, const Vector* other
) {
    return !Vector_operator_equal_const_Vector_ref(this, other);
}

int main(void) {
    Vector v1 = {1.0, 2.0}, v2 = {1.0, 3.0};
    if (Vector_operator_not_equal_const_Vector_ref(&v1, &v2)) {
        printf("Vectors are different\n");
    }
}
```

**Key Characteristics**:
- Returns `bool` (true if values are not equal)
- Usually implemented as `!(*this == other)`
- Supports conditional logic where inequality is natural

---

## Logical Operators (! && ||)

Logical operators handle boolean operations and negation. While `&&` and `||` can theoretically be overloaded, this is **strongly discouraged** because the transpiler cannot preserve short-circuit evaluation.

### Logical NOT Operator (!)

**Purpose**: Returns the logical negation (inverts a boolean condition).

**C++ Code**:
```cpp
class Optional {
    void* value;
    bool has_value;
public:
    bool operator!() const {
        return !has_value;
    }
};

int main() {
    Optional opt = getSomeValue();
    if (!opt) {
        printf("Optional is empty\n");
    }
}
```

**Transpiled C Code**:
```c
#include <stdbool.h>

typedef struct {
    void* value;
    bool has_value;
} Optional;

bool Optional_operator_not_const(const Optional* this);

bool Optional_operator_not_const(const Optional* this) {
    return !this->has_value;
}

int main(void) {
    Optional opt = getSomeValue();
    if (Optional_operator_not_const(&opt)) {
        printf("Optional is empty\n");
    }
}
```

**Key Characteristics**:
- Returns `bool` (negation of internal state)
- Unary operator (no parameters besides `this`)
- Common for checking emptiness, validity, or presence
- No parameters means simpler C translation

**Use Cases**:
- Optional/Maybe types
- Smart pointers (null checks)
- Validation/state checking

### Logical AND Operator (&&)

**Purpose**: Binary logical AND (true only if both operands are true).

**IMPORTANT WARNING**: Overloading `&&` is **STRONGLY DISCOURAGED** because:
1. The transpiler cannot preserve **short-circuit evaluation**
2. In C++, `a && b` doesn't evaluate `b` if `a` is false
3. In transpiled C, both operands are always evaluated: `ClassName_operator_and(&a, &b)`
4. This changes program behavior and may cause errors

**C++ Code** (NOT RECOMMENDED):
```cpp
class Condition {
    bool value;
public:
    bool operator&&(const Condition& other) const {
        return value && other.value;  // Lost short-circuit!
    }
};

int main() {
    Condition c1{true}, c2{false};
    if (c1 && c2) {  // Both evaluated - not short-circuiting!
        printf("Both conditions true\n");
    }
}
```

**Transpiled C Code** (Shows Lost Short-Circuit):
```c
#include <stdbool.h>

typedef struct {
    bool value;
} Condition;

bool Condition_operator_and_const_Condition_ref(
    const Condition* this, const Condition* other
);

bool Condition_operator_and_const_Condition_ref(
    const Condition* this, const Condition* other
) {
    return this->value && other->value;
}

int main(void) {
    Condition c1 = {true}, c2 = {false};
    // Both operands ALWAYS evaluated - no short-circuit!
    if (Condition_operator_and_const_Condition_ref(&c1, &c2)) {
        printf("Both conditions true\n");
    }
}
```

**Workaround**: Use `operator bool()` conversion (Phase 52) instead:
```cpp
class Condition {
    bool value;
public:
    explicit operator bool() const {
        return value;
    }
};

int main() {
    Condition c1{true}, c2{false};
    if (c1 && c2) {  // Short-circuit preserved with operator bool()!
        printf("Both conditions true\n");
    }
}
```

### Logical OR Operator (||)

**Purpose**: Binary logical OR (true if either operand is true).

**IMPORTANT WARNING**: Like `&&`, overloading `||` is **STRONGLY DISCOURAGED** because:
1. Short-circuit evaluation is lost in transpilation
2. In C++, `a || b` doesn't evaluate `b` if `a` is true
3. In transpiled C, both operands always evaluate
4. This changes behavior for side effects and expensive operations

**C++ Code** (NOT RECOMMENDED):
```cpp
class Result {
    bool success;
public:
    bool operator||(const Result& other) const {
        return success || other.success;  // Lost short-circuit!
    }
};

int main() {
    Result r1 = getResult1();
    Result r2 = getResult2();
    if (r1 || r2) {  // Both evaluated - expensive if r2 requires computation!
        printf("At least one succeeded\n");
    }
}
```

**Transpiled C Code** (Shows Lost Short-Circuit):
```c
#include <stdbool.h>

typedef struct {
    bool success;
} Result;

bool Result_operator_or_const_Result_ref(
    const Result* this, const Result* other
);

bool Result_operator_or_const_Result_ref(
    const Result* this, const Result* other
) {
    return this->success || other->success;
}

int main(void) {
    Result r1 = getResult1();
    Result r2 = getResult2();
    // Both getResult() calls executed - getResult2() wasn't skipped!
    if (Result_operator_or_const_Result_ref(&r1, &r2)) {
        printf("At least one succeeded\n");
    }
}
```

**Workaround**: Use `operator bool()` (Phase 52) or avoid overloading `||`.

---

## Friend (Non-Member) Operators

Comparison operators can be defined as friend (non-member) functions, which is common for symmetrical operations and enables comparison in both directions.

### Member vs Friend Operators

**Member Operator** (typical):
```cpp
class Point {
    double x, y;
public:
    bool operator==(const Point& other) const {
        return x == other.x && y == other.y;
    }
};
```

**Friend Operator** (symmetrical):
```cpp
class Point {
    double x, y;
    friend bool operator==(const Point& lhs, const Point& rhs);
};

bool operator==(const Point& lhs, const Point& rhs) {
    return lhs.x == rhs.x && lhs.y == rhs.y;
}
```

### Translation Differences

**Member operator** → function with `this` parameter:
```c
bool Point_operator_equal_const_Point_ref(
    const Point* this,     // Implicit this
    const Point* other
);
```

**Friend operator** → free function with 2 parameters:
```c
bool Point_operator_equal_friend(
    const Point* lhs,      // First argument
    const Point* rhs       // Second argument
);
```

### When to Use Friend Operators

Use friend operators when:

1. **Symmetrical operations** - Both operands are equally important:
   ```cpp
   // Can write: v1 == v2 or v2 == v1 (same function)
   friend bool operator==(const Vector& lhs, const Vector& rhs);
   ```

2. **Mixed-type comparisons** - Comparing different types:
   ```cpp
   class Meter {
       double value;
       friend bool operator==(const Meter& lhs, const Centimeter& rhs);
   };
   // Allows: meter == centimeter
   ```

3. **Convenience** - Avoid asymmetry:
   ```cpp
   // Member operator requires left operand to be the class
   class Integer { /* ... */ };
   Integer a = 5;
   if (a == 5) { /* ... */ }  // OK
   if (5 == a) { /* ... */ }  // ERROR (5 is int, not Integer)

   // Friend operator allows both directions
   friend bool operator==(const Integer& lhs, const Integer& rhs);
   if (a == 5) { /* ... */ }  // OK (5 converted to Integer)
   if (5 == a) { /* ... */ }  // OK (5 converted to Integer)
   ```

---

## Function Naming Convention

The transpiler uses a consistent naming convention for comparison operators:

| Operator | C Function Name | Example |
|----------|-----------------|---------|
| `<` | `_operator_less` | `Date_operator_less_const_Date_ref` |
| `>` | `_operator_greater` | `Date_operator_greater_const_Date_ref` |
| `<=` | `_operator_less_equal` | `Date_operator_less_equal_const_Date_ref` |
| `>=` | `_operator_greater_equal` | `Date_operator_greater_equal_const_Date_ref` |
| `==` | `_operator_equal` | `Point_operator_equal_const_Point_ref` |
| `!=` | `_operator_not_equal` | `Point_operator_not_equal_const_Point_ref` |
| `!` | `_operator_not` | `Optional_operator_not_const` |
| `&&` | `_operator_and` | `Condition_operator_and_const_Condition_ref` |
| `\|\|` | `_operator_or` | `Result_operator_or_const_Result_ref` |

**Const Function Suffix**:
- For const member functions: `_const_*` suffix (e.g., `_const_Date_ref`)
- For non-const: no suffix (rare for comparison operators)

---

## Best Practices

### 1. Implement All Comparison Operators Consistently

Define a canonical operator and implement others in terms of it:

```cpp
class Date {
public:
    bool operator<(const Date& other) const {
        // Canonical - full implementation
        if (year != other.year) return year < other.year;
        if (month != other.month) return month < other.month;
        return day < other.day;
    }

    bool operator>(const Date& other) const {
        return other < *this;  // In terms of <
    }

    bool operator<=(const Date& other) const {
        return !(other < *this);  // In terms of <
    }

    bool operator>=(const Date& other) const {
        return !(*this < other);  // In terms of <
    }

    bool operator==(const Date& other) const {
        return !(*this < other) && !(other < *this);  // In terms of <
    }

    bool operator!=(const Date& other) const {
        return !(*this == other);  // In terms of ==
    }
};
```

**Why**: Easier to test (test 1-2 operators, others follow), better performance (less code).

### 2. Preserve Const Correctness

Always mark comparison operators as `const`:

```cpp
// GOOD - const member function
bool operator<(const Score& other) const {
    return points < other.points;
}

// BAD - non-const (won't work with const objects)
bool operator<(const Score& other) {  // ERROR!
    return points < other.points;
}
```

### 3. Use References for Parameters

Always pass comparison arguments by const reference:

```cpp
// GOOD - const reference
bool operator==(const Point& other) const {
    return x == other.x && y == other.y;
}

// INEFFICIENT - copies argument
bool operator==(const Point other) const {
    return x == other.x && y == other.y;
}

// WRONG - pointer syntax
bool operator==(const Point* other) const {  // Makes transpilation harder
    return x == other->x && y == other->y;
}
```

### 4. Return Bool, Not Int

Always return `bool`, never `int`:

```cpp
// GOOD - explicit bool
bool operator<(const Integer& other) const {
    return value < other.value;
}

// BAD - implicit conversion from int
int operator<(const Integer& other) const {  // Don't do this!
    return value < other.value;
}
```

### 5. Avoid Overloading && and ||

Use `operator bool()` instead (Phase 52):

```cpp
// GOOD - operator bool allows natural use
class Optional {
    bool has_value;
public:
    explicit operator bool() const {
        return has_value;
    }
};

// Usage preserves short-circuit evaluation
if (opt1 && opt2) { /* ... */ }  // Works correctly!

// BAD - overloading && loses short-circuit
class Optional {
public:
    bool operator&&(const Optional& other) const {
        return has_value && other.has_value;  // ALWAYS evaluates both!
    }
};

// Both operands evaluated, defeating short-circuit
if (opt1 && opt2) { /* ... */ }  // Both operands evaluated
```

### 6. Implement Equivalence or Ordering Relations Properly

**Equivalence Relation** (for `==`):
- Reflexive: `a == a` is always true
- Symmetric: if `a == b` then `b == a`
- Transitive: if `a == b` and `b == c` then `a == c`

```cpp
bool operator==(const Rational& other) const {
    return numerator * other.denominator == denominator * other.numerator;
}
```

**Strict Weak Ordering** (for `<`):
- Irreflexive: `a < a` is always false
- Transitive: if `a < b` and `b < c` then `a < c`
- Asymmetric: if `a < b` then `!(b < a)`
- Incomparability is transitive: if `!(a < b)` and `!(b < a)` and `!(b < c)` and `!(c < b)` then `!(a < c)` and `!(c < a)`

```cpp
bool operator<(const Date& other) const {
    if (year != other.year) return year < other.year;
    if (month != other.month) return month < other.month;
    return day < other.day;
}
```

---

## Common Pitfalls

### Pitfall 1: Short-Circuit Loss with && and ||

**Problem**: C++ `&&` and `||` short-circuit (don't evaluate second operand if result is known). Transpilation loses this:

```cpp
// C++ - doesn't call mayHaveExpensiveSideEffects() if x is false
if (x && mayHaveExpensiveSideEffects()) { /* ... */ }

// Transpiled C - ALWAYS calls the function!
if (Condition_operator_and(&x, &getSomeValue())) { /* ... */ }
```

**Solution**: Use `operator bool()` instead (Phase 52), or avoid overloading `&&`/`||`.

### Pitfall 2: Inconsistent Comparison Operators

**Problem**: Implementing operators independently can cause contradictions:

```cpp
bool operator<(const Score& other) const {
    return points < other.points;
}

bool operator>(const Score& other) const {
    return points > other.points;  // OK, but redundant
}

bool operator==(const Score& other) const {
    return points == other.points;  // What if points are equal but other fields differ?
}
```

**Solution**: Implement canonical operator, derive others:

```cpp
bool operator<(const Score& other) const {
    if (points != other.points) return points < other.points;
    if (name != other.name) return name < other.name;
    return false;
}

bool operator==(const Score& other) const {
    return !(*this < other) && !(other < *this);  // Automatic consistency!
}
```

### Pitfall 3: Non-Const Comparison Operators

**Problem**: Non-const comparisons can't be used with const objects:

```cpp
class Vector {
    double x, y;
public:
    // BAD - non-const
    bool operator<(const Vector& other) {
        x = 0;  // Oops, modified this!
        return length() < other.length();
    }
};

const Vector v1{1, 2}, v2{3, 4};
if (v1 < v2) { /* ... */ }  // ERROR - v1 is const!
```

**Solution**: Always mark comparison operators as `const`:

```cpp
bool operator<(const Vector& other) const {  // const member function
    return length() < other.length();
}

const Vector v1{1, 2}, v2{3, 4};
if (v1 < v2) { /* ... */ }  // OK!
```

### Pitfall 4: Confusing Value and Identity Equality

**Problem**: Using `==` for identity when value equality is needed (or vice versa):

```cpp
class SmartPtr {
    void* ptr;
public:
    bool operator==(const SmartPtr& other) const {
        return ptr == other.ptr;  // Identity equality
    }
};

SmartPtr p1(new int(42));
SmartPtr p2(new int(42));
// These have equal values but different identities
if (p1 == p2) { /* ... */ }  // false - not what users expect!
```

**Solution**: Document whether `==` is identity or value equality, and implement correctly:

```cpp
// Value equality
bool operator==(const SmartPtr& other) const {
    return *ptr == *other.ptr;  // Compare values
}

// Or identity equality with clearer semantics
bool isSamePtr(const SmartPtr& other) const {
    return ptr == other.ptr;
}
```

---

## Sorting and Searching

Comparison operators enable your custom types to work with standard algorithms:

### Sorting Arrays

```cpp
class Person {
    std::string name;
    int age;
public:
    bool operator<(const Person& other) const {
        if (age != other.age) return age < other.age;
        return name < other.name;  // Sort by age, then by name
    }
};

int main() {
    Person people[] = {
        {"Alice", 30}, {"Bob", 25}, {"Charlie", 30}
    };

    // Sort by age, then name (std::sort uses operator<)
    std::sort(people, people + 3);

    for (const auto& p : people) {
        printf("%s, %d\n", p.name.c_str(), p.age);
    }
    // Output:
    // Bob, 25
    // Alice, 30
    // Charlie, 30
}
```

### Binary Search

```cpp
int main() {
    Person people[] = {
        {"Alice", 30}, {"Bob", 25}, {"Charlie", 35}
    };
    std::sort(people, people + 3);  // Must be sorted

    Person target{"David", 30};

    // Returns iterator to element if found, otherwise end()
    auto it = std::lower_bound(people, people + 3, target);

    if (it != people + 3 && it->age == target.age) {
        printf("Found person with age %d\n", it->age);
    }
}
```

### Removing Duplicates

```cpp
int main() {
    std::vector<int> nums{1, 2, 2, 3, 3, 3, 4};

    // std::unique uses operator==
    auto last = std::unique(nums.begin(), nums.end());
    nums.erase(last, nums.end());

    // Result: {1, 2, 3, 4}
}
```

---

## Integration with Phase 50 (Arithmetic Operators)

Comparison operators work together with arithmetic operators for complete type support:

```cpp
class Rational {
    int numerator, denominator;
public:
    // Arithmetic (Phase 50)
    Rational operator+(const Rational& other) const { /* ... */ }
    Rational operator-(const Rational& other) const { /* ... */ }
    Rational operator*(const Rational& other) const { /* ... */ }
    Rational operator/(const Rational& other) const { /* ... */ }

    // Comparison (Phase 51)
    bool operator<(const Rational& other) const {
        return numerator * other.denominator < denominator * other.numerator;
    }
    bool operator==(const Rational& other) const {
        return numerator * other.denominator == denominator * other.numerator;
    }
};

int main() {
    Rational r1{1, 2}, r2{1, 3};
    Rational r3 = r1 + r2;  // Phase 50
    if (r1 < r2) { /* ... */ }  // Phase 51
    if (r1 == r2) { /* ... */ }  // Phase 51
}
```

---

## Integration with Phase 52 (Conversion Operators)

Conversion operators (Phase 52) enable natural boolean conversions:

```cpp
class Optional {
    void* value;
    bool has_value;
public:
    // Logical NOT (Phase 51)
    bool operator!() const {
        return !has_value;
    }

    // Conversion to bool (Phase 52)
    explicit operator bool() const {
        return has_value;
    }
};

int main() {
    Optional opt = getSomeValue();

    if (!opt) { /* ... */ }  // Phase 51 - operator!
    if (opt) { /* ... */ }   // Phase 52 - operator bool

    if (opt1 && opt2) { /* ... */ }  // Phase 52 - preserves short-circuit!
}
```

---

## FAQs

**Q: Why is the transpiler output so verbose?**
A: Function names include parameter types for clarity and to avoid collisions. This is essential for overloading support. The verbose names are generated automatically and don't appear in your C++ source.

**Q: Can I mix member and friend operators?**
A: Yes, it's common. Member operators for internal logic, friend operators for symmetrical operations. The transpiler handles both.

**Q: What about three-way comparison (C++20 spaceship operator)?**
A: Phase 51 supports `<`, `>`, `<=`, `>=`, `==`, `!=` (the six classic operators). The spaceship operator (`<=>`) is planned for Phase 52+.

**Q: How does const correctness translate to C?**
A: C++ const methods become `const ClassName*` parameters in C:
```cpp
bool operator<(const Score& other) const;  // C++ const method

// Becomes:
bool Score_operator_less_const_Score_ref(const Score* this, const Score* other);  // C
```

**Q: Do I need to implement all 6 comparison operators?**
A: No, but it's good practice. Implement `<` and `==` canonically, derive others. STL containers and algorithms use `<` for ordering, so that's the most important.

**Q: What about `<=>, ==, !=` C++20 changes?**
A: The transpiler supports the classic 6 operators. C++20's changes to `==` and `<=>` are handled in Phase 52+.

---

## See Also

- [Phase 50: Arithmetic Operators](ARITHMETIC_OPERATORS.md)
- [Phase 52: Conversion Operators](CONVERSION_OPERATORS.md) (Future)
- [OPERATOR_OVERLOADING_REFERENCE.md](OPERATOR_OVERLOADING_REFERENCE.md) - Complete operator reference
- [Namespace Support Guide](features/NAMESPACE_GUIDE.md) - Using comparison operators with namespaces

