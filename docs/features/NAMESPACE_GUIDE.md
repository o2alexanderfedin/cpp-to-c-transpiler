# Namespace Support Guide

## Overview

The C++ to C transpiler provides comprehensive support for C++ namespaces, translating them into C-compatible naming conventions using name mangling. This guide explains what's supported, how it works, and how to use namespaces effectively in your C++ code.

## What Are Namespaces?

Namespaces are a C++ feature for organizing code and preventing name collisions. They allow you to group related classes, functions, and variables under a common scope.

```cpp
namespace graphics {
    class Point { /* ... */ };
    void draw();
}
```

Since C doesn't have namespaces, the transpiler converts namespace-qualified names into prefixed identifiers that preserve the namespace hierarchy.

## Translation Pattern

The transpiler uses underscore-separated prefixes to encode namespace information:

**Pattern**: `namespace1_namespace2_identifier`

### Examples

```cpp
// C++ Input
namespace math {
    int add(int a, int b);
}

// C Output
int math_add(int a, int b);
```

```cpp
// C++ Input
namespace graphics::math {
    class Vector {
        void normalize();
    };
}

// C Output
struct graphics_math_Vector { /* ... */ };
void graphics_math_Vector_normalize(struct graphics_math_Vector* this);
```

## Supported Features

### 1. Simple Namespaces

Single-level namespaces work as expected:

```cpp
// C++ Input
namespace utils {
    void helper() {
        // Implementation
    }
}

int main() {
    utils::helper();
}

// C Output
void utils_helper(void) {
    // Implementation
}

int main(void) {
    utils_helper();
}
```

### 2. Nested Namespaces

Multi-level namespace hierarchies are fully supported:

```cpp
// C++ Input
namespace company::project::module {
    void process();
}

// C Output
void company_project_module_process(void);
```

C++17 nested namespace syntax is also supported:

```cpp
namespace a::b::c {
    void func();
}
// Same as:
namespace a {
    namespace b {
        namespace c {
            void func();
        }
    }
}
```

### 3. Classes in Namespaces

Classes defined within namespaces include the namespace prefix:

```cpp
// C++ Input
namespace game {
    class Player {
        int score;
    public:
        void addScore(int points);
        int getScore();
    };
}

// C Output
struct game_Player {
    int score;
};

void game_Player_addScore(struct game_Player* this, int points);
int game_Player_getScore(struct game_Player* this);
```

### 4. Methods in Namespaced Classes

Methods combine namespace, class, and method names:

```cpp
// C++ Input
namespace graphics {
    class Renderer {
    public:
        void render();
    };
}

// C Output
struct graphics_Renderer { /* ... */ };
void graphics_Renderer_render(struct graphics_Renderer* this);
```

### 5. Scoped Enums in Namespaces

Scoped enums (enum class) in namespaces use double-underscore for enum values:

```cpp
// C++ Input
namespace game {
    enum class State {
        Menu,
        Playing,
        Paused
    };
}

// C Output
enum {
    game_State__Menu = 0,
    game_State__Playing = 1,
    game_State__Paused = 2
};
```

**Pattern**: `namespace_EnumName__value`

### 6. Overloaded Functions in Namespaces

Function overloading is supported by appending parameter types:

```cpp
// C++ Input
namespace math {
    int max(int a, int b) {
        return a > b ? a : b;
    }
    double max(double a, double b) {
        return a > b ? a : b;
    }
}

// C Output
int math_max_int_int(int a, int b) {
    return a > b ? a : b;
}
double math_max_double_double(double a, double b) {
    return a > b ? a : b;
}
```

### 7. Static Methods in Namespaced Classes

Static methods don't receive a `this` parameter:

```cpp
// C++ Input
namespace utils {
    class Math {
    public:
        static int square(int x) {
            return x * x;
        }
    };
}

// C Output
int utils_Math_square(int x) {
    return x * x;
}
```

### 8. Anonymous Namespaces

Anonymous namespaces are translated with unique identifiers for internal linkage:

```cpp
// C++ Input (in file: utils.cpp)
namespace {
    void internalHelper() {
        // Internal implementation
    }
}

void publicFunction() {
    internalHelper();
}

// C Output
static void _anon_utils_cpp_10_internalHelper(void) {
    // Internal implementation
}

void publicFunction(void) {
    _anon_utils_cpp_10_internalHelper();
}
```

**Anonymous Namespace Pattern**: `_anon_<filename>_<line>_name`

The transpiler generates unique identifiers based on source location to ensure:
- File-local scope (functions are `static` in C)
- No name collisions across translation units
- Human-readable generated code

## Special Cases

### extern "C" Functions

Functions with C linkage are **never mangled**, even in namespaces:

```cpp
// C++ Input
namespace wrapper {
    extern "C" void c_api_function();
}

// C Output
void c_api_function(void);  // NOT wrapper_c_api_function
```

This preserves C ABI compatibility for interfacing with C libraries.

### main() Function

The `main()` function is **never mangled**:

```cpp
// C++ Input
int main() {
    return 0;
}

// C Output
int main(void) {
    return 0;
}
```

### Constructors and Destructors

Constructors and destructors in namespaced classes include namespace prefix:

```cpp
// C++ Input
namespace data {
    class Buffer {
    public:
        Buffer();
        Buffer(int size);
        ~Buffer();
    };
}

// C Output
void data_Buffer__ctor(struct data_Buffer* this);
void data_Buffer__ctor_1(struct data_Buffer* this, int size);
void data_Buffer__dtor(struct data_Buffer* this);
```

## Not Supported

### Using Directives

`using namespace` directives are **not supported**:

```cpp
// NOT SUPPORTED
using namespace std;
cout << "Hello";
```

**Workaround**: Use explicit namespace qualification:

```cpp
// SUPPORTED
std::cout << "Hello";
```

**Rationale**: Supporting `using` directives would require complex name resolution and scope tracking. Since Clang's AST already resolves names, implementing this would require reverse-engineering, adding significant complexity with minimal benefit.

### Namespace Aliases (Limited)

Namespace aliases may work if Clang resolves them internally, but are not officially supported:

```cpp
// May or may not work
namespace alias = very::long::namespace::name;
alias::func();
```

**Workaround**: Use full namespace qualification:

```cpp
very::long::namespace::name::func();
```

### Inline Namespaces (Limited)

Inline namespaces are treated as regular namespaces:

```cpp
// C++ Input
namespace lib {
    inline namespace v2 {
        void func();
    }
}

// C Output (inline keyword ignored)
void lib_v2_func(void);
```

## Common Patterns and Use Cases

### Organizing Related Functionality

```cpp
// C++ Input
namespace geometry {
    class Point {
        float x, y;
    public:
        Point(float x, float y);
        float distance(const Point& other);
    };

    class Line {
        Point start, end;
    public:
        Line(Point a, Point b);
        float length();
    };
}

// C Output
struct geometry_Point {
    float x;
    float y;
};

void geometry_Point__ctor(struct geometry_Point* this, float x, float y);
float geometry_Point_distance(struct geometry_Point* this, struct geometry_Point* other);

struct geometry_Line {
    struct geometry_Point start;
    struct geometry_Point end;
};

void geometry_Line__ctor(struct geometry_Line* this, struct geometry_Point a, struct geometry_Point b);
float geometry_Line_length(struct geometry_Line* this);
```

### Library Versioning

Use nested namespaces for version management:

```cpp
// C++ Input
namespace mylib::v1 {
    void process();
}

namespace mylib::v2 {
    void process();
}

// C Output
void mylib_v1_process(void);
void mylib_v2_process(void);
```

### Utility Functions

Group utility functions under a common namespace:

```cpp
// C++ Input
namespace string_utils {
    int length(const char* str);
    void copy(char* dest, const char* src);
    bool equals(const char* a, const char* b);
}

// C Output
int string_utils_length(const char* str);
void string_utils_copy(char* dest, const char* src);
bool string_utils_equals(const char* a, const char* b);
```

### Internal Implementation Details

Use anonymous namespaces for file-local helpers:

```cpp
// C++ Input (module.cpp)
namespace {
    const int BUFFER_SIZE = 1024;
    void validateInput(int x) {
        // Validation logic
    }
}

void publicAPI(int value) {
    validateInput(value);
    // Process with BUFFER_SIZE
}

// C Output
static const int _anon_module_cpp_2_BUFFER_SIZE = 1024;
static void _anon_module_cpp_3_validateInput(int x) {
    // Validation logic
}

void publicAPI(int value) {
    _anon_module_cpp_3_validateInput(value);
    // Process with _anon_module_cpp_2_BUFFER_SIZE
}
```

## Migration Guide

### From Non-Namespaced Code

If you have existing code without namespaces that you want to organize:

**Before**:
```cpp
class GameState { /* ... */ };
void initGame();
void updateGame();
```

**After**:
```cpp
namespace game {
    class State { /* ... */ };
    void init();
    void update();
}
```

The transpiler will generate:
```c
struct game_State { /* ... */ };
void game_init(void);
void game_update(void);
```

### Avoiding Name Collisions

If you have name collisions in generated C code, namespaces help:

**Problem**:
```cpp
// lib1.cpp
class Buffer { /* ... */ };

// lib2.cpp
class Buffer { /* ... */ };  // Collision!
```

**Solution**:
```cpp
// lib1.cpp
namespace lib1 {
    class Buffer { /* ... */ };
}

// lib2.cpp
namespace lib2 {
    class Buffer { /* ... */ };
}
```

Generated C code:
```c
struct lib1_Buffer { /* ... */ };
struct lib2_Buffer { /* ... */ };  // No collision
```

## Integration with Other Features

### Templates

Templates in namespaces work correctly after monomorphization:

```cpp
// C++ Input
namespace containers {
    template<typename T>
    class Vector {
        T* data;
    public:
        void push(T value);
    };
}

// Instantiation
containers::Vector<int> vec;

// C Output (after monomorphization)
struct containers_Vector_int {
    int* data;
};

void containers_Vector_int_push(struct containers_Vector_int* this, int value);
```

### Inheritance

Classes in namespaces support inheritance:

```cpp
// C++ Input
namespace shapes {
    class Shape {
    public:
        virtual void draw() = 0;
    };

    class Circle : public Shape {
    public:
        void draw() override;
    };
}

// C Output
struct shapes_Shape { /* vtable */ };
struct shapes_Circle {
    struct shapes_Shape base;
    /* additional fields */
};

void shapes_Circle_draw(struct shapes_Circle* this);
```

### Virtual Methods

Virtual methods in namespaced classes work as expected:

```cpp
// C++ Input
namespace ui {
    class Widget {
    public:
        virtual void render();
    };
}

// C Output
struct ui_Widget {
    void** lpVtbl;
};

void ui_Widget_render(struct ui_Widget* this);
```

## Best Practices

### 1. Use Descriptive Namespace Names

Choose short but meaningful namespace names:

```cpp
// Good
namespace math { /* ... */ }
namespace graphics { /* ... */ }
namespace audio { /* ... */ }

// Avoid overly long names (creates verbose C code)
namespace extremely_long_descriptive_namespace_name { /* ... */ }
```

### 2. Nest Logically

Use nesting to create clear hierarchies:

```cpp
namespace company {
    namespace product {
        namespace module {
            // ...
        }
    }
}
```

Or use C++17 syntax:
```cpp
namespace company::product::module {
    // ...
}
```

### 3. Prefer Explicit Qualification

Always use full qualification instead of `using` directives:

```cpp
// Good
std::vector<int> vec;
math::sqrt(x);

// Not supported
using namespace std;
using namespace math;
```

### 4. Use Anonymous Namespaces for Internal Code

Mark implementation details as file-local:

```cpp
// header.h
namespace mylib {
    void publicAPI();
}

// implementation.cpp
namespace {
    void internalHelper() { /* ... */ }
}

void mylib::publicAPI() {
    internalHelper();  // Only visible in this file
}
```

### 5. Organize by Feature, Not Type

```cpp
// Good - feature-based organization
namespace rendering {
    class Renderer { /* ... */ };
    class Shader { /* ... */ };
    void render();
}

// Less ideal - type-based organization
namespace classes {
    class Renderer { /* ... */ };
    class Shader { /* ... */ };
}
namespace functions {
    void render();
}
```

## Debugging

### Inspecting Generated Names

To see how namespaces are translated, run the transpiler with verbose output:

```bash
./cpptoc mycode.cpp --output mycode.c --verbose
```

### Understanding Mangled Names

The pattern is always: `namespace1_namespace2_..._identifier`

Examples:
- `graphics_math_Vector` = `graphics::math::Vector`
- `ui_Widget_render` = `ui::Widget::render()`
- `game_State__Menu` = `game::State::Menu` (scoped enum value)

### Name Collision Debugging

If you see unexpected names, check for:
1. Function overloading (adds parameter types)
2. Multiple namespaces with same name in different files
3. Anonymous namespace collisions (check file/line numbers in names)

## Performance Considerations

Namespace mangling has **negligible performance impact**:
- Name mangling happens at transpilation time (compile-time), not runtime
- Generated C code runs at same speed as hand-written C
- No indirection or lookup overhead
- Names are resolved statically

## Examples

See the `examples/namespaces/` directory for complete working examples:

- `simple_namespace.cpp` - Basic namespace usage
- `nested_namespaces.cpp` - Multi-level hierarchies
- `namespace_classes.cpp` - Classes in namespaces
- `namespace_enums.cpp` - Scoped enums in namespaces
- `namespace_overloading.cpp` - Function overloading
- `anonymous_namespace.cpp` - File-local declarations

## Summary

| Feature | Supported | Notes |
|---------|-----------|-------|
| Simple namespaces | ✅ Yes | Pattern: `ns_name` |
| Nested namespaces | ✅ Yes | Pattern: `ns1_ns2_name` |
| Classes in namespaces | ✅ Yes | Pattern: `ns_ClassName` |
| Methods in namespaced classes | ✅ Yes | Pattern: `ns_Class_method` |
| Scoped enums in namespaces | ✅ Yes | Pattern: `ns_Enum__value` |
| Anonymous namespaces | ✅ Yes | Pattern: `_anon_file_line_name` |
| Overloaded functions | ✅ Yes | Adds parameter types |
| Static methods | ✅ Yes | No `this` parameter |
| extern "C" functions | ✅ Yes | Never mangled |
| main() function | ✅ Yes | Never mangled |
| Using directives | ❌ No | Use explicit qualification |
| Namespace aliases | ⚠️ Limited | May work if Clang resolves |
| Inline namespaces | ⚠️ Limited | Treated as regular namespaces |

## Further Reading

- [C++ Namespaces Reference](https://en.cppreference.com/w/cpp/language/namespace)
- [Architecture Documentation](../ARCHITECTURE.md) - Transpiler pipeline
- [Scoped Enums Guide](../features/scoped-enums.md) - Integration with namespaces
- [Name Mangling Reference](../../NAMESPACE_MANGLING_REFERENCE.md) - Technical details

## Getting Help

If you encounter issues with namespace transpilation:

1. Check this guide's "Not Supported" section
2. Review the FAQ: [NAMESPACE_FAQ.md](NAMESPACE_FAQ.md)
3. Examine the generated C code to understand the translation
4. File an issue on GitHub with a minimal reproducible example

---

**Version**: 1.0.0 (Phase 48)
**Last Updated**: 2025-12-27
