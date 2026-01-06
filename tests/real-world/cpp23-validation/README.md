# C++23 to C99 Transpilation Validation

This project validates the C++ to C transpiler's ability to handle C++23 language features.

## Project Structure

```
cpp23-validation/
├── cpp/                          # Original C++23 code
│   ├── CMakeLists.txt           # C++23 build system
│   ├── src/                     # C++23 source files
│   └── include/                 # C++23 headers
├── transpiled/                   # Generated C99 code
│   ├── src/                     # Transpiled .c files
│   └── include/                 # Transpiled .h files
├── ab-test/                      # AB-testing framework
│   └── results/                 # Test results
├── transpile.sh                  # Transpilation automation script
└── README.md                     # This file
```

## C++23 Features Tested

### Core Language Features

| Feature | Status | Notes |
|---------|--------|-------|
| Deducing this (P0847) | ❌ Not transpiled | C++ code passed through unchanged |
| if consteval (P1938) | ❌ Not transpiled | consteval/constexpr not converted |
| Multidimensional subscript (P2128) | ❌ Not transpiled | operator[] with multiple args not converted |
| Static operator() and operator[] (P1169) | ❌ Not transpiled | Static operators not supported |
| [[assume]] attribute (P1774) | ⚠️ Unknown | Attributes may be stripped |
| Labels at end of compound statements (P2324) | ⚠️ Unknown | May work as-is |
| size_t literals (uz/UZ) (P0330) | ⚠️ Unknown | May work with casting |
| Named universal character escapes (P2071) | ❌ Not transpiled | Unicode names not converted |

### Templates (Previously tested)
| Feature | Status | Notes |
|---------|--------|-------|
| Class templates | ✅ Partial | Monomorphization works for some cases |
| Function templates | ⚠️ Partial | Limited support |
| Template metaprogramming | ❌ Not supported | SFINAE, concepts not handled |

## Build Instructions

### Build C++23 Version

```bash
cd cpp/build
cmake ..
make
./cpp23_validation
```

### Transpile to C99

```bash
./transpile.sh
```

### Build C99 Version (NOT WORKING YET)

```bash
cd transpiled
make
./cpp23_validation_c
```

## Current Status

**TRANSPILATION INCOMPLETE** - The transpiler currently outputs C++ code with modern C++23 features still present. It does NOT produce valid C99 code.

### Issues Found

1. **Namespaces not converted** - `namespace cpp23 { }` appears in .c files
2. **Classes not converted** - `class TextBuffer { }` appears as-is
3. **Templates not converted** - Template syntax remains in output
4. **constexpr/consteval not handled** - These keywords remain in output
5. **Explicit object parameters (deducing this)** - `this` parameter syntax not converted
6. **Lambdas with auto** - Lambda syntax not converted to C
7. **operator[] overloading** - C++ operators not converted to functions

### Expected Behavior

The transpiler SHOULD convert:
- `namespace` → C naming prefixes
- `class` → `struct` with function pointers
- Templates → Monomorphized concrete types
- `constexpr` → Macros or inline functions
- `this` parameters → Regular function parameters
- Lambdas → Function pointers with context structs
- Operators → Named functions

## Transpiler Architecture Gaps

The current transpiler was designed for:
- C++98/C++11 features (classes, inheritance, virtual functions)
- Templates (with monomorphization)
- RTTI and exceptions

It does NOT handle:
- C++20/C++23 language extensions
- Modern metaprogramming features
- Explicit object parameters
- Constexpr/consteval compile-time evaluation
- Advanced operator overloading (static operators, multi-arg subscript)

## Next Steps

1. **Document current transpiler limitations** ✅
2. **Determine if C++23 support is feasible** - Requires major transpiler rewrites
3. **Consider subset approach** - Only transpile C++23 features that can map to C
4. **Alternative: Focus on C++11/14** - More realistic transpilation target

## Lines of Code

- **C++ Source**: ~400 lines
- **Transpiled C**: ~595 lines (but contains C++ syntax!)
- **C Headers**: ~499 lines (but contains C++ syntax!)

## Conclusion

This validation project demonstrates that the current transpiler is NOT capable of handling C++23 features. The output contains C++ syntax and would not compile as C99.

**Recommendation**: Establish a clear "supported C++ version" (e.g., C++11 or C++14) and document unsupported features, rather than attempting to support C++23.
