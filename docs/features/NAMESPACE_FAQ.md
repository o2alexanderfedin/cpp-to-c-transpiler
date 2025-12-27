# Namespace Support - Frequently Asked Questions

## General Questions

### Q1: What are namespaces and why should I use them?

**A**: Namespaces are a C++ feature for organizing code and preventing name collisions. They're especially useful when:
- Building libraries that might be used alongside other code
- Organizing large codebases into logical modules
- Avoiding global namespace pollution
- Creating clear boundaries between different components

Example:
```cpp
namespace mylib {
    class Buffer { /* ... */ };  // Won't conflict with other Buffer classes
}
```

### Q2: How does the transpiler handle namespaces?

**A**: Since C doesn't have namespaces, the transpiler uses **name mangling** - encoding the namespace hierarchy into C identifier names using underscores:

```cpp
// C++
namespace graphics::math {
    void rotate();
}

// Transpiled C
void graphics_math_rotate(void);
```

This preserves namespace semantics while generating valid C code.

### Q3: Will using namespaces make my code slower?

**A**: No. Namespace mangling happens at transpilation time (compile-time), not runtime. The generated C code runs at exactly the same speed as if you had written the C code with prefixed names manually. There's zero runtime overhead.

### Q4: Can I use namespaces from the C++ standard library?

**A**: If you're transpiling standard library usage, yes - but the standard library itself must be separately implemented or provided. The transpiler translates your code that uses `std::vector`, `std::string`, etc., but you'll need C implementations of those classes. This is an advanced use case.

For simple programs, it's better to avoid the standard library and use plain C++ classes that the transpiler can handle.

### Q5: Are namespaces required?

**A**: No, namespaces are optional. You can write C++ code without namespaces, and the transpiler will work fine:

```cpp
// Without namespaces
class Point { /* ... */ };

// With namespaces
namespace geometry {
    class Point { /* ... */ };
}

// Both transpile correctly
```

## Supported Features

### Q6: Do nested namespaces work?

**A**: Yes, fully supported. Both traditional and C++17 syntax work:

```cpp
// Traditional syntax
namespace a {
    namespace b {
        namespace c {
            void func();
        }
    }
}

// C++17 syntax (equivalent)
namespace a::b::c {
    void func();
}

// Both transpile to:
void a_b_c_func(void);
```

### Q7: Can I put classes inside namespaces?

**A**: Yes, classes in namespaces work perfectly:

```cpp
namespace game {
    class Player {
        int health;
    public:
        void takeDamage(int amount);
    };
}

// Transpiles to:
struct game_Player {
    int health;
};
void game_Player_takeDamage(struct game_Player* this, int amount);
```

### Q8: What about enum classes in namespaces?

**A**: Scoped enums (enum class) in namespaces are fully supported with double-underscore notation:

```cpp
namespace ui {
    enum class Color {
        Red,
        Green,
        Blue
    };
}

// Transpiles to:
enum {
    ui_Color__Red = 0,
    ui_Color__Green = 1,
    ui_Color__Blue = 2
};
```

**Pattern**: `namespace_EnumName__value`

### Q9: Can I overload functions in namespaces?

**A**: Yes, function overloading works. The transpiler appends parameter types to distinguish overloads:

```cpp
namespace math {
    int add(int a, int b);
    double add(double a, double b);
}

// Transpiles to:
int math_add_int_int(int a, int b);
double math_add_double_double(double a, double b);
```

### Q10: Do anonymous namespaces work?

**A**: Yes, anonymous namespaces are supported and generate unique internal names:

```cpp
// file: utils.cpp
namespace {
    void helper() { /* ... */ }
}

// Transpiles to:
static void _anon_utils_cpp_15_helper(void) { /* ... */ }
```

The generated name includes the filename and line number to ensure uniqueness. The `static` keyword ensures file-local scope (like anonymous namespaces in C++).

## Special Cases

### Q11: What happens to `main()` in a namespace?

**A**: The `main()` function should never be in a namespace (it's invalid C++). However, if you somehow have it in a namespace, the transpiler always keeps `main` unmangled since C requires the entry point to be named exactly `main`.

```cpp
int main() {  // Always stays as main()
    return 0;
}
```

### Q12: How are `extern "C"` functions in namespaces handled?

**A**: Functions with C linkage are **never mangled**, even if declared in a namespace:

```cpp
namespace wrapper {
    extern "C" void c_api_function();
}

// Transpiles to:
void c_api_function(void);  // NOT wrapper_c_api_function
```

This preserves C ABI compatibility for interfacing with C libraries.

### Q13: Can I use constructors and destructors in namespaced classes?

**A**: Yes, they work normally and include the namespace prefix:

```cpp
namespace data {
    class Buffer {
    public:
        Buffer();
        ~Buffer();
    };
}

// Transpiles to:
void data_Buffer__ctor(struct data_Buffer* this);
void data_Buffer__dtor(struct data_Buffer* this);
```

### Q14: What about static methods in namespaced classes?

**A**: Static methods work correctly and don't receive a `this` parameter:

```cpp
namespace utils {
    class Math {
    public:
        static int square(int x) { return x * x; }
    };
}

// Transpiles to:
int utils_Math_square(int x) {
    return x * x;
}
```

### Q15: Can I use templates in namespaces?

**A**: Yes, after template monomorphization:

```cpp
namespace containers {
    template<typename T>
    class Vector {
        T* data;
    };
}

// Instantiation
containers::Vector<int> v;

// Transpiles to (after monomorphization):
struct containers_Vector_int {
    int* data;
};
```

## Not Supported Features

### Q16: Can I use `using namespace` directives?

**A**: No, `using namespace` is **not supported**:

```cpp
// NOT SUPPORTED
using namespace std;
cout << "Hello";
```

**Reason**: Supporting `using` directives requires complex name resolution and scope tracking. Since Clang's AST already resolves names, implementing this would add significant complexity with minimal benefit.

**Workaround**: Use explicit qualification:

```cpp
// SUPPORTED
std::cout << "Hello";
```

### Q17: Are namespace aliases supported?

**A**: Officially no, but they may work in some cases if Clang resolves them internally:

```cpp
// May or may not work
namespace short_name = very::long::namespace::name;
short_name::func();
```

**Workaround**: Use the full namespace name:

```cpp
very::long::namespace::name::func();
```

### Q18: What about inline namespaces?

**A**: Inline namespaces are treated as regular namespaces (the `inline` keyword is ignored):

```cpp
namespace lib {
    inline namespace v2 {
        void func();
    }
}

// Transpiles to (inline ignored):
void lib_v2_func(void);
```

The versioning semantics of inline namespaces (where `lib::func` is equivalent to `lib::v2::func`) are not preserved. Always use explicit qualification.

### Q19: Can I use argument-dependent lookup (ADL)?

**A**: ADL is a C++ feature where function lookup considers the namespaces of arguments. Since the transpiler generates explicit C function calls, ADL semantics are not preserved. Always use explicit qualification:

```cpp
// C++ with ADL
namespace ns {
    class MyClass { };
    void func(MyClass obj);
}

int main() {
    ns::MyClass obj;
    func(obj);  // ADL finds ns::func - NOT SUPPORTED
}

// Instead, write:
int main() {
    ns::MyClass obj;
    ns::func(obj);  // Explicit qualification - SUPPORTED
}
```

### Q20: Are using declarations supported?

**A**: No, `using` declarations (different from `using` directives) are not supported:

```cpp
// NOT SUPPORTED
using std::vector;
vector<int> v;
```

**Workaround**: Use full qualification:

```cpp
std::vector<int> v;
```

## Migration and Best Practices

### Q21: Should I add namespaces to existing code?

**A**: Only if you need to avoid name collisions or organize code into modules. Namespaces are optional. If your code works without them, there's no need to add them.

However, namespaces can help if:
- You're building a library
- You have naming conflicts with other code
- You want clearer code organization

### Q22: How do I avoid really long generated names?

**A**: Keep namespace hierarchies shallow (2-3 levels max) and use short, meaningful names:

```cpp
// Avoid deep nesting
namespace company::division::department::team::project::module {
    void func();  // Generates: company_division_department_team_project_module_func
}

// Better
namespace mylib::core {
    void func();  // Generates: mylib_core_func
}
```

### Q23: Can I mix namespaced and non-namespaced code?

**A**: Yes, you can freely mix code with and without namespaces:

```cpp
// Global scope
class GlobalClass { };

// Namespaced
namespace mylib {
    class LibClass { };
}

// Transpiles to:
struct GlobalClass { };
struct mylib_LibClass { };
```

### Q24: How do I organize a large project with namespaces?

**A**: Follow these best practices:

1. **One namespace per library/module**:
   ```cpp
   namespace math { /* math utilities */ }
   namespace graphics { /* rendering code */ }
   namespace audio { /* sound system */ }
   ```

2. **Use nested namespaces for sub-modules**:
   ```cpp
   namespace engine::physics { /* physics engine */ }
   namespace engine::ai { /* AI system */ }
   ```

3. **Use anonymous namespaces for implementation details**:
   ```cpp
   // header.h
   namespace mylib {
       void publicAPI();
   }

   // impl.cpp
   namespace {
       void internalHelper() { }  // File-local
   }
   void mylib::publicAPI() {
       internalHelper();
   }
   ```

### Q25: What if I have name collisions even with namespaces?

**A**: If two symbols have the same fully-qualified name (including namespace), you have a real collision that namespaces can't fix:

```cpp
// Collision: both are ns::func()
namespace ns {
    void func();  // First declaration
}

namespace ns {
    void func();  // Redeclaration - ERROR
}
```

**Solution**: Use function overloading with different parameter types, or rename one of them.

## Debugging and Troubleshooting

### Q26: How can I see what names the transpiler generates?

**A**: Run the transpiler and inspect the generated C code:

```bash
./cpptoc mycode.cpp --output mycode.c
cat mycode.c  # Inspect generated names
```

Or use verbose mode:
```bash
./cpptoc mycode.cpp --output mycode.c --verbose
```

### Q27: My generated C code has unexpected names. Why?

**A**: Common reasons:

1. **Function overloading** - Parameter types are appended:
   ```cpp
   void func(int x);     // func_int
   void func(double x);  // func_double
   ```

2. **Nested namespaces** - All levels are included:
   ```cpp
   namespace a::b::c { void f(); }  // a_b_c_f
   ```

3. **Anonymous namespaces** - File and line numbers are added:
   ```cpp
   namespace { void helper(); }  // _anon_file_cpp_42_helper
   ```

### Q28: I get linker errors with namespaced functions. What's wrong?

**A**: Make sure you're:

1. **Including the transpiled header**: The C header should declare the mangled names
2. **Linking the transpiled object file**: The mangled function definitions must be linked
3. **Using consistent transpilation**: Re-transpile all related files together

Example:
```bash
# Transpile
./cpptoc module1.cpp --output module1.c
./cpptoc module2.cpp --output module2.c

# Compile and link
gcc -c module1.c -o module1.o
gcc -c module2.c -o module2.o
gcc module1.o module2.o -o program
```

### Q29: Can I call namespaced C++ functions from plain C code?

**A**: Yes, after transpilation. Use the mangled names:

```c
// C code calling transpiled C++ function
#include "mylib.h"  // Contains: void mylib_func(void);

int main(void) {
    mylib_func();  // Call using mangled name
    return 0;
}
```

### Q30: How do I debug namespace-related transpilation issues?

**A**: Follow this process:

1. **Simplify**: Create a minimal example with just the problematic namespace code
2. **Transpile**: Run the transpiler on the minimal example
3. **Inspect**: Look at the generated C code to see how names were mangled
4. **Compare**: Check against expected pattern (`ns_name`)
5. **Report**: If it doesn't match expected behavior, file an issue with the minimal example

Example minimal test:
```cpp
// test.cpp
namespace myns {
    void func() { }
}

int main() {
    myns::func();
}
```

Transpile and check:
```bash
./cpptoc test.cpp --output test.c
cat test.c  # Should see: void myns_func(void)
```

## Advanced Topics

### Q31: How are virtual methods in namespaced classes handled?

**A**: Virtual methods work normally with vtables:

```cpp
namespace ui {
    class Widget {
    public:
        virtual void render();
    };
}

// Transpiles to:
struct ui_Widget {
    void** lpVtbl;  // Virtual table pointer
};
void ui_Widget_render(struct ui_Widget* this);
```

The vtable setup and virtual dispatch work the same as for non-namespaced classes.

### Q32: What about inheritance with namespaced classes?

**A**: Inheritance works correctly:

```cpp
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

// Transpiles with proper base class embedding:
struct shapes_Shape { /* ... */ };
struct shapes_Circle {
    struct shapes_Shape base;
    /* ... */
};
```

### Q33: Can I have multiple translation units with the same namespace?

**A**: Yes, namespaces can span multiple files:

```cpp
// file1.cpp
namespace mylib {
    void func1() { }
}

// file2.cpp
namespace mylib {
    void func2() { }
}

// Transpiles to:
// file1.c
void mylib_func1(void) { }

// file2.c
void mylib_func2(void) { }
```

Just ensure both files are transpiled and linked together.

### Q34: How do anonymous namespaces interact with multiple files?

**A**: Each file's anonymous namespace is separate and generates unique IDs:

```cpp
// file1.cpp
namespace { void helper() { } }  // _anon_file1_cpp_10_helper

// file2.cpp
namespace { void helper() { } }  // _anon_file2_cpp_15_helper
```

No collision - they're different functions with different names.

### Q35: Can I use namespaces with templates?

**A**: Yes, templates in namespaces work after monomorphization:

```cpp
namespace containers {
    template<typename T>
    struct Vector {
        T* data;
        void push(T val);
    };
}

// Usage
containers::Vector<int> v1;
containers::Vector<float> v2;

// Transpiles to:
struct containers_Vector_int { int* data; };
void containers_Vector_int_push(struct containers_Vector_int* this, int val);

struct containers_Vector_float { float* data; };
void containers_Vector_float_push(struct containers_Vector_float* this, float val);
```

## Performance and Code Size

### Q36: Do longer namespace names make my code slower?

**A**: No. At runtime, the names don't matter. The C compiler turns them into addresses. Whether a function is called `f` or `very_long_namespace_name_f`, it runs at the same speed.

### Q37: Do longer namespace names increase binary size?

**A**: Symbol names can slightly increase debug binary size, but in release builds with stripped symbols, there's no difference. If you're concerned, keep namespace names short.

### Q38: Is there any performance overhead from namespace mangling?

**A**: Zero runtime overhead. Mangling happens at transpilation time. The generated C code is as fast as hand-written C with the same naming pattern.

## Comparison with Other Approaches

### Q39: Why not use C's file-based scoping instead of namespaces?

**A**: C's `static` provides file-local scope, but doesn't help with:
- Organizing related functions across multiple files
- Preventing collisions in header files (public APIs)
- Creating logical groupings within a single file

Namespaces provide better organization and work across files.

### Q40: Why not use prefixes manually instead of namespaces?

**A**: You can! But namespaces offer:
- Compile-time enforcement (C++ compiler checks namespace membership)
- Cleaner source code (shorter qualified names in C++)
- Automatic, consistent mangling
- Better refactoring support

If you're writing C++, namespaces are more idiomatic. If you're writing C, manual prefixes work fine.

---

## Still Have Questions?

- **User Guide**: See [NAMESPACE_GUIDE.md](NAMESPACE_GUIDE.md) for detailed documentation
- **Technical Reference**: See [../../NAMESPACE_MANGLING_REFERENCE.md](../../NAMESPACE_MANGLING_REFERENCE.md)
- **Examples**: Check `examples/namespaces/` for working code
- **Report Issues**: File a bug report on GitHub with a minimal reproducible example

---

**Version**: 1.0.0 (Phase 48)
**Last Updated**: 2025-12-27
