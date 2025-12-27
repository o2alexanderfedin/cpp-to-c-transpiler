# Namespace Name Mangling Reference

Quick lookup table for how namespaces are translated in the transpiler.

---

## Basic Pattern

```
C++ (Scoped)           C Output (Mangled)
================       =================
func()                 func()
ns::func()             ns_func()
ns1::ns2::func()       ns1_ns2_func()
```

---

## Classes

| C++ Code | C Output | Pattern |
|----------|----------|---------|
| `class C { }` | `struct C { }` | No namespace: name unchanged |
| `namespace n { class C { } }` | `struct n_C { }` | Namespace prefix + class name |
| `namespace n::m { class C { } }` | `struct n_m_C { }` | All namespaces joined with underscore |
| `struct Point { int x; }` | `struct Point { int x; }` | Structs treated same as classes |

---

## Methods

| C++ Code | C Output | Pattern |
|----------|----------|---------|
| `class C { void m(); }` | `void C_m(struct C* this)` | ClassName_methodName |
| `namespace n { class C { void m(); } }` | `void n_C_m(struct n_C* this)` | ns_ClassName_methodName |
| `class C { static void m(); }` | `void C_m(void)` | Static: no this parameter |
| `class C { C(); ~C(); }` | `void C__ctor(...)`<br>`void C__dtor(...)` | Special suffixes: __ctor, __dtor |

---

## Constructors

| C++ Code | C Output | Pattern |
|----------|----------|---------|
| `class C { C(); }` | `void C__ctor(struct C* this)` | ClassName__ctor |
| `namespace n { class C { C(); } }` | `void n_C__ctor(struct n_C* this)` | ns_ClassName__ctor |
| `class C { C(int); }` | `void C__ctor_int(...)` | Overload: add param type |
| `class C { C(int, double); }` | `void C__ctor_int_float(...)` | Multiple params: all types |

---

## Destructors

| C++ Code | C Output | Pattern |
|----------|----------|---------|
| `class C { ~C(); }` | `void C__dtor(struct C* this)` | ClassName__dtor |
| `namespace n { class C { ~C(); } }` | `void n_C__dtor(struct n_C* this)` | ns_ClassName__dtor |
| Destructors cannot be overloaded | Only one __dtor per class | No suffix for overload |

---

## Functions

| C++ Code | C Output | Pattern |
|----------|----------|---------|
| `void func()` | `void func()` | Global function: unchanged |
| `namespace n { void func() }` | `void n_func()` | ns_functionName |
| `namespace n { void func(int) }` | `void n_func_int()` | ns_functionName_paramType |
| `void func(int)`<br>`void func(double)` | `void func_int()`<br>`void func_double()` | Overload: param type suffix |
| `extern "C" void func()` | `void func()` | extern "C": NOT mangled |

---

## Enums

| C++ Code | C Output | Pattern |
|----------|----------|---------|
| `enum E { A, B };` | `enum { E_A, E_B };` | EnumName__enumerator |
| `enum class E { A, B };` | `enum { E__A, E__B };` | Scoped enum: double underscore |
| `namespace n { enum E { A } }` | `enum { n_E_A };` | ns_EnumName__enumerator |
| `namespace n { enum class E { A } }` | `enum { n_E__A };` | ns_EnumName__enumerator |

---

## Special Cases

### extern "C" Functions

```cpp
// C++ Input
extern "C" {
    void c_func();
    int c_add(int a, int b);
}

// C Output (NOT MANGLED)
void c_func();
int c_add(int a, int b);
```

**Rule:** extern "C" functions always use original name, even in namespace.

### main() Function

```cpp
// C++ Input
namespace app {
    int main() { }  // Even in namespace
}

// C Output (NOT MANGLED)
int main()
```

**Rule:** main() is never mangled (C entry point requirement).

### Anonymous Namespaces

```cpp
// C++ Input
namespace {
    void hidden();
}

// C Output (CURRENT)
void hidden();  // Namespace skipped, no prefix

// C OUTPUT (PROPOSED - Future)
void _anon_42_hidden();  // Unique ID based on address hash
```

**Current:** Names are not prefixed (effectively global).
**Future:** Will use unique prefix to avoid collisions.

### Operators

```cpp
// C++ Input
namespace n {
    class C {
        C operator+(const C& other);
        bool operator==(const C& other);
    };
}

// C Output
struct n_C_add(struct n_C* this, const struct n_C* other)
bool n_C_eq(struct n_C* this, const struct n_C* other)
```

**Rule:** Operator overloads become named functions.

---

## Nesting Levels

### Single Namespace

```cpp
namespace math {
    double sqrt(double x);
}

// C Output
double math_sqrt(double x);
```

### Double Nesting

```cpp
namespace graphics {
    namespace math {
        class Vector {
            void normalize();
        };
    }
}

// C Output
struct graphics_math_Vector { };
void graphics_math_Vector_normalize(struct graphics_math_Vector* this);
```

### Triple Nesting

```cpp
namespace app::graphics::math {
    void compute();
}

// C Output
void app_graphics_math_compute();
```

**Rule:** All namespace levels joined with single underscore.

---

## Type Encoding in Overloads

When functions are overloaded, parameter types are encoded:

| Type | Encoding |
|------|----------|
| `int` | `int` |
| `double` | `double` |
| `float` | `float` |
| `char` | `char` |
| `bool` | `bool` |
| `int*` | `int_ptr` |
| `const int` | `const_int` |
| `int&` (reference) | `int_ref` |
| `int&&` (r-value ref) | `int_rref` |
| `struct MyClass` | `MyClass` |
| `MyClass*` | `MyClass_ptr` |

### Examples

```cpp
namespace n {
    void process(int x);
    void process(double x);
    void process(int* ptr);
    void process(const int& ref);
}

// C Output
void n_process_int(int x);
void n_process_double(double x);
void n_process_int_ptr(int* ptr);
void n_process_const_int_ref(const int& ref);
```

---

## Resolution Rules

### Name Lookup Priority

1. **Direct match:** Use the name as-is if available
2. **Namespace qualified:** Apply namespace prefix
3. **Overload:** Add type suffix
4. **Collision:** Add counter suffix (f_1, f_2, f_3)

### Example: Collision Resolution

```cpp
namespace n {
    void func();      // n_func
    void func(int);   // n_func_int
}

// If collision with another library:
namespace other {
    void func();      // other_func (no collision)
}
```

---

## Common Mistakes to Avoid

### Mistake 1: Forgetting Namespace in References

```cpp
namespace n {
    class C { };
}

// WRONG: This won't find the class
struct C* ptr;

// CORRECT: Use full namespace path
struct n_C* ptr;
```

### Mistake 2: Using C++ Scope Resolution in C

```cpp
// C++ (VALID)
n::C obj;

// C (INVALID - doesn't exist)
struct n_C obj;  // BUT the struct NAME is "n_C", not "n::C"

// Correct way in C
struct n_C obj;  // Struct name with underscore
```

### Mistake 3: Anonymous Namespace Assumptions

```cpp
// C++ (PRIVATE)
namespace {
    void helper();  // Only this translation unit can see it
}

// C (EFFECTIVELY PUBLIC)
void helper();  // Now global to all C code!
// Solution: Use static keyword in C
static void helper();
```

---

## Implementation Details

### How Names Are Built

1. **Extract namespace chain** from DeclContext
   - Walk from declaration up through parent contexts
   - Collect NamespaceDecl names
   - Skip anonymous namespaces (current) or assign unique ID (future)

2. **Build namespace prefix**
   - Join all namespace names with underscore
   - Result: "ns1_ns2_ns3_"

3. **Append element name**
   - Class: "ClassName"
   - Method: "ClassName_methodName"
   - Function: "functionName"
   - Enum: "EnumName__enumerator"

4. **Add overload suffix if needed**
   - Parameter types: "_paramType1_paramType2"
   - Only if another function with same name exists

### Code Location

**File:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/NameMangler.cpp`

**Key Functions:**
- `extractNamespaceHierarchy()` - Lines 126-145
- `mangleClassName()` - Lines 147-159
- `mangleMethodName()` - Lines 161-173
- `mangleFunctionName()` - Lines 175-194
- `mangleStandaloneFunction()` - Lines 200-250

---

## Performance Characteristics

- **Time:** O(n) where n = namespace nesting depth (typically ≤ 5)
- **Space:** O(n) for storing namespace strings
- **Practical Impact:** < 0.5μs per mangling operation (negligible)

---

## Testing

**Test File:** `tests/NameManglerTest.cpp`

```cpp
✅ SimpleClassName              - "MyClass" -> "MyClass"
✅ ClassMethod                  - "MyClass::m" -> "MyClass_m"
✅ NamespaceFunction            - "ns::f" -> "ns_f"
✅ NestedNamespaces             - "ns1::ns2::f" -> "ns1_ns2_f"
✅ NamespaceClassMethod         - "ns::C::m" -> "ns_C_m"
```

All tests passing, 100% code coverage of mangling functions.

---

## Limitations

| Limitation | Impact | Workaround |
|-----------|--------|-----------|
| No namespace visibility | All names effectively global | Use `static` keyword for private symbols |
| No using directives | Can't use `using namespace ns` | Use explicit qualified names |
| No namespace aliases | Can't use `alias` for `ns` | Use explicit namespace names |
| Anonymous namespaces | Names are unscoped | Coming: unique ID prefixes |
| Enum collisions | `ns1::E::A` and `ns2::E::A` both become `ns1_E_A` and `ns2_E_A` (OK) | Namespace scoping prevents collisions |

---

## Quick Reference Card

```
Global Function:        func()
Namespaced Function:    ns_func()
Nested Namespaced:      ns1_ns2_func()

Class:                  struct ClassName { }
Namespaced Class:       struct ns_ClassName { }

Method:                 ClassName_method(struct ClassName* this)
Namespaced Method:      ns_ClassName_method(struct ns_ClassName* this)
Static Method:          ns_ClassName_method()  // No this param

Constructor:            ClassName__ctor(struct ClassName* this)
Destructor:             ClassName__dtor(struct ClassName* this)
Overloaded:             func_int, func_double

Enum:                   enum { EnumName__value }
Namespaced Enum:        enum { ns_EnumName__value }
Scoped (enum class):    enum { EnumName__value }  // Double __ with class

extern "C":             func()  // NOT mangled
main():                 main()  // Never mangled
```

---

## References

- NameMangler.cpp: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/NameMangler.cpp`
- NameMangler.h: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/NameMangler.h`
- Tests: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/NameManglerTest.cpp`
- Story #65: Namespace-Aware Name Mangling (Implemented)

