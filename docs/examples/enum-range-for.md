# Enum and Range-For Loop Translation Examples

**Phase 16 (v2.9.0)**

This document demonstrates how the C++ to C transpiler translates enums and range-for loops from C++ to C.

## Table of Contents
- [Enum Translation](#enum-translation)
  - [Unscoped Enums](#unscoped-enums)
  - [Scoped Enums (enum class)](#scoped-enums-enum-class)
  - [Enums with Underlying Types](#enums-with-underlying-types)
- [Range-For Loop Translation](#range-for-loop-translation)
  - [Arrays](#arrays)
  - [Containers (Future)](#containers-future)
- [Combined Examples](#combined-examples)

---

## Enum Translation

### Unscoped Enums

Unscoped enums translate directly to C enums with no modifications.

#### C++ Input
```cpp
enum Color {
    RED = 0,
    GREEN = 1,
    BLUE = 2
};

void setColor() {
    Color c = RED;
    int value = GREEN;
}
```

#### Generated C Output
```c
// Unscoped enum Color
enum Color {
  RED = 0,
  GREEN = 1,
  BLUE = 2
};

void setColor() {
    enum Color c = RED;
    int value = GREEN;
}
```

**Key Points**:
- No name prefix needed
- Direct enum value access
- Implicit conversion to underlying type (int)

---

### Scoped Enums (enum class)

Scoped enums require name prefixing because C doesn't have enum class scoping.

#### C++ Input
```cpp
enum class Status {
    IDLE = 0,
    RUNNING = 1,
    STOPPED = 2
};

void checkStatus() {
    Status s = Status::IDLE;
    if (s == Status::RUNNING) {
        // ...
    }
}
```

#### Generated C Output
```c
// Scoped enum (enum class) Status
enum Status_enum {
  Status_IDLE = 0,
  Status_RUNNING = 1,
  Status_STOPPED = 2
};
typedef int Status;

void checkStatus() {
    enum Status_enum s = Status_IDLE;
    if (s == Status_RUNNING) {
        // ...
    }
}
```

**Key Points**:
- Enum values prefixed with `Status_`
- Typedef created for the enum name
- `Status::IDLE` → `Status_IDLE`
- Prevents namespace pollution

---

### Enums with Underlying Types

C++11 allows specifying the underlying type for enums.

#### C++ Input
```cpp
#include <cstdint>

enum class Priority : int8_t {
    LOW = -1,
    NORMAL = 0,
    HIGH = 1
};

void setPriority() {
    Priority p = Priority::HIGH;
    int8_t value = static_cast<int8_t>(p);
}
```

#### Generated C Output
```c
#include <stdint.h>

// Scoped enum (enum class) Priority
enum Priority_enum {
  Priority_LOW = -1,
  Priority_NORMAL = 0,
  Priority_HIGH = 1
};
typedef int8_t Priority;

void setPriority() {
    enum Priority_enum p = Priority_HIGH;
    int8_t value = (int8_t)p;
}
```

**Key Points**:
- Typedef uses specified underlying type (`int8_t`)
- Includes necessary headers (`<stdint.h>`)
- Maintains type safety
- Explicit casts translated to C-style casts

---

## Range-For Loop Translation

**Note**: Full code generation for range-for loops is planned for a future phase. Current implementation provides detection and infrastructure.

### Arrays

Range-for on arrays will be expanded to traditional for loops with direct indexing.

#### C++ Input
```cpp
void processArray() {
    int arr[5] = {1, 2, 3, 4, 5};

    for (int x : arr) {
        printf("%d\n", x);
    }
}
```

#### Planned C Output (Future)
```c
void processArray() {
    int arr[5] = {1, 2, 3, 4, 5};

    // Traditional for loop with direct indexing
    for (int __i_0 = 0; __i_0 < 5; __i_0++) {
        int x = arr[__i_0];
        printf("%d\n", x);
    }
}
```

**Translation Strategy**:
- Detect array size at compile time
- Generate index variable (`__i_0`)
- Direct array access with `arr[index]`
- Preserve loop body exactly

---

### Containers (Future)

Range-for on STL containers will use iterator protocol expansion.

#### C++ Input
```cpp
#include <vector>

void processVector() {
    std::vector<int> vec = {1, 2, 3};

    for (int x : vec) {
        printf("%d\n", x);
    }
}
```

#### Planned C Output (Future)
```c
void processVector() {
    struct std_vector__int vec;
    std_vector__int__ctor(&vec);
    // ... push items 1, 2, 3 ...

    // Iterator-based loop
    struct std_vector__int__iterator __iter = std_vector__int__begin(&vec);
    struct std_vector__int__iterator __iter_end = std_vector__int__end(&vec);

    for (; !std_vector__int__iterator__eq(&__iter, &__iter_end);
         std_vector__int__iterator__inc(&__iter)) {
        int x = *std_vector__int__iterator__deref(&__iter);
        printf("%d\n", x);
    }

    std_vector__int__dtor(&vec);
}
```

**Translation Strategy**:
- Generate begin() and end() iterator calls
- Expand operator++ to function call
- Expand operator* to dereference function
- Expand operator== to equality function

---

## Combined Examples

### Enum + Range-For Integration

Combining enums with range-for loops.

#### C++ Input
```cpp
enum class LogLevel {
    DEBUG = 0,
    INFO = 1,
    WARNING = 2,
    ERROR = 3
};

void processLogs() {
    LogLevel levels[4] = {
        LogLevel::DEBUG,
        LogLevel::INFO,
        LogLevel::WARNING,
        LogLevel::ERROR
    };

    for (auto level : levels) {
        switch(level) {
            case LogLevel::DEBUG:
                printf("DEBUG\n");
                break;
            case LogLevel::INFO:
                printf("INFO\n");
                break;
            default:
                printf("OTHER\n");
        }
    }
}
```

#### Generated C Output (Current)
```c
// Scoped enum (enum class) LogLevel
enum LogLevel_enum {
  LogLevel_DEBUG = 0,
  LogLevel_INFO = 1,
  LogLevel_WARNING = 2,
  LogLevel_ERROR = 3
};
typedef int LogLevel;

void processLogs() {
    enum LogLevel_enum levels[4] = {
        LogLevel_DEBUG,
        LogLevel_INFO,
        LogLevel_WARNING,
        LogLevel_ERROR
    };

    // Range-for detection: Array type detected
    // Full code generation pending future phase
}
```

---

## CLI Usage

Enable or disable enum and range-for translation:

```bash
# Enable enum translation (default: on)
cpptoc --enable-enum input.cpp

# Disable enum translation
cpptoc --enable-enum=false input.cpp

# Enable range-for expansion (default: on)
cpptoc --enable-range-for input.cpp

# Disable range-for expansion
cpptoc --enable-range-for=false input.cpp

# Use both flags
cpptoc --enable-enum --enable-range-for input.cpp
```

---

## Current Status

### ✅ Fully Implemented
- Unscoped enum translation
- Scoped enum translation with name prefixing
- Enum underlying type handling
- Enum code generation
- CLI flags for control

### 🚧 In Progress (Infrastructure Complete)
- Range-for array detection
- Range-for container detection
- Loop variable type deduction

### ⏳ Future Work
- Range-for code generation for arrays
- Range-for iterator protocol expansion
- Container begin/end generation
- Operator overload expansion (++, *, ==)

---

## Best Practices

### For Enums
1. **Prefer Scoped Enums**: Use `enum class` in C++ for better type safety
2. **Explicit Underlying Types**: Specify underlying types for memory-sensitive code
3. **Meaningful Names**: Use clear enum and value names to improve generated C code

### For Range-For Loops
1. **Simple Ranges**: Start with simple array or container ranges
2. **Type Deduction**: Use `auto` for cleaner code (transpiler deduces type)
3. **Const References**: Use `const auto&` for large objects to avoid copies

---

## Troubleshooting

### Enum Issues

**Issue**: Scoped enum values not accessible
```cpp
enum class Color { RED };
Color c = RED;  // ERROR: RED not in scope
```

**Solution**: Use qualified access
```cpp
Color c = Color::RED;  // Transpiles to: Color_RED
```

### Range-For Issues

**Issue**: Range-for on unsupported type
```cpp
for (int x : myCustomContainer) { ... }
```

**Solution**: Current implementation supports arrays and standard containers. Custom containers require begin/end methods and operator overloads.

---

## See Also

- [Phase 16 Plan](../../.planning/phases/16-enums-rangefor/PLAN.md)
- [Phase 16 Summary](../../.planning/phases/16-enums-rangefor/SUMMARY.md)
- [CHANGELOG.md](../CHANGELOG.md) for v2.9.0 release notes

---

**Last Updated**: 2025-12-21 (v2.9.0)
