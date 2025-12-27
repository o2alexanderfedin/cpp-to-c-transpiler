# Real-World C++ Projects - Transpiled Output

**Status**: EMPTY - No Successful Transpilations
**Last Updated**: 2025-12-24
**Phase**: 30-01

## Overview

This directory is intended to contain the transpiled C code from the 5 real-world C++ test projects:

1. **json-parser** - Recursive descent JSON parser with RAII, exceptions, templates
2. **logger** - Multi-level logging system with templates, inheritance
3. **test-framework** - Unit test framework with macros, templates, exceptions
4. **string-formatter** - Type-safe string formatting with variadic templates
5. **resource-manager** - Generic resource management with smart pointers, move semantics

## Current Status

**This directory is empty because the transpiler cannot currently handle real-world C++ code.**

### Transpilation Results

| Project | Files | Attempted | Success | Status |
|---------|-------|-----------|---------|--------|
| json-parser | 4 cpp, 2 h | 1 | 0 | ❌ FAILED |
| logger | 2 cpp, 1 h | 0 | 0 | ⏸️  NOT ATTEMPTED |
| resource-manager | 1 cpp, 1 h | 0 | 0 | ⏸️  NOT ATTEMPTED |
| string-formatter | 1 cpp, 1 h | 0 | 0 | ⏸️  NOT ATTEMPTED |
| test-framework | 3 cpp, 1 h | 0 | 0 | ⏸️  NOT ATTEMPTED |
| **TOTAL** | **11 cpp, 6 h** | **1** | **0** | **0% success** |

## Why Transpilation Failed

### Critical Blockers

1. **Missing STL Support**
   - All projects use `std::string`, `std::vector`, `std::map`, etc.
   - No C equivalents provided
   - Transpiler cannot translate STL types
   - **Impact**: Fundamental blocker for any modern C++ code

2. **Include Path Resolution**
   - Transpiler cannot find project-specific headers
   - No mechanism to specify `-I` include directories
   - Results in "file not found" compiler errors
   - **Impact**: Cannot compile multi-file projects

3. **Complex C++ Features**
   - Smart pointers (`std::unique_ptr`, `std::shared_ptr`) not supported
   - Variadic templates partially supported
   - Exception handling incomplete (SJLJ model implementation issues)
   - Move semantics not implemented
   - RAII patterns generate low-quality C code
   - **Impact**: Cannot translate modern C++ patterns

4. **Transpiler Crashes**
   ```
   Assertion failed: (Name.isIdentifier() && "Name is not a simple identifier"),
   function getName, file Decl.h, line 301
   ```
   - Crashes on complex class hierarchies
   - No graceful error handling
   - Assertions instead of diagnostics
   - **Impact**: Unstable, unusable for production

5. **Output Quality**
   - Generated C code contains `<recovery-expr>` markers
   - Indicates incomplete parsing/translation
   - Example:
     ```c
     // C++ input
     std::string jsonStr = "...";
     JsonParser parser;
     auto root = parser.parse(jsonStr);

     // C output (broken)
     int jsonStr = <recovery-expr>("...");
     int parser;
     auto root = <recovery-expr>().parse(<recovery-expr>());
     ```
   - **Impact**: Output not compilable

## Sample Error Output

### Transpiling json-parser/tests/examples.cpp

**Clang Errors:**
```
error: invalid argument '-std=c++17' not allowed with 'C'
fatal error: 'string' file not found
```

**JSON Output:**
```json
{
  "success": false,
  "c": "int jsonStr = <recovery-expr>(\"...\");\n...",
  "diagnostics": [
    {
      "severity": "error",
      "message": "Transpilation failed - see compiler diagnostics"
    }
  ]
}
```

### Transpiling json-parser/src/JsonParser.cpp

**Result:** Transpiler crash (assertion failure), no JSON output produced

## What Works

Based on integration tests in `tests/`:

✅ **Supported Features** (in isolation):
- Basic classes and structs
- Simple inheritance (single, non-virtual bases)
- Virtual methods and vtables
- Basic templates (monomorphization limited)
- Constructor/destructor translation
- Member functions
- Operator overloading (basic)
- Basic RAII (constructor/destructor pairs)
- Exceptions (SJLJ model, basic cases)

❌ **Not Supported** (needed for real-world code):
- STL containers and algorithms
- Smart pointers
- Complex templates (variadic, SFINAE, concepts)
- Move semantics
- Multi-file projects with shared headers
- External library dependencies
- Modern C++ idioms (ranges, coroutines, etc.)

## Next Steps

### Phase 30-02: Simple Validation Tests

Before attempting real-world projects again, we need to:

1. **Create Simple Validation Suite**
   - Write single-file, self-contained C++ tests
   - One feature per file
   - No external dependencies
   - No STL usage
   - Examples:
     - `01-basic-class.cpp` - simple class with methods
     - `02-inheritance.cpp` - single inheritance
     - `03-virtual-methods.cpp` - polymorphism
     - `04-operator-overload.cpp` - basic operators
     - `05-raii-simple.cpp` - constructor/destructor

2. **Document Supported Features**
   - Create `docs/SUPPORTED_FEATURES.md`
   - Create `docs/LIMITATIONS.md`
   - Create `docs/MIGRATION_GUIDE.md`
   - Feature support matrix

3. **Fix Critical Bugs**
   - Convert assertion failures to diagnostics
   - Improve error messages
   - Add include path support (`-I` flag)
   - Reduce `<recovery-expr>` generation

4. **Future Work** (Medium to Long-Term)
   - Implement STL compatibility layer (months of effort)
   - Multi-file transpilation support
   - Enhanced template monomorphization
   - Mature exception handling
   - Consider scope reduction (define "transpilable C++" subset)

## How to Use This Directory (Future)

Once the transpiler is ready for real-world code:

1. Run transpilation:
   ```bash
   ./scripts/transpile-real-world.sh
   ```

2. Check results:
   ```bash
   cat test-logs/transpile-summary.txt
   ```

3. Compile transpiled code:
   ```bash
   cd tests/real-world/transpiled/<project>
   mkdir build && cd build
   cmake .. && make
   ```

4. Run tests:
   ```bash
   ctest --verbose
   ```

## Directory Structure (Expected Future State)

```
transpiled/
├── README.md (this file)
├── json-parser/
│   ├── src/
│   │   ├── JsonParser.c
│   │   ├── JsonParser.h
│   │   ├── JsonValue.c
│   │   └── JsonValue.h
│   ├── tests/
│   │   ├── examples.c
│   │   ├── examples.h
│   │   ├── test_json_parser.c
│   │   └── test_json_parser.h
│   └── CMakeLists.txt
├── logger/
│   ├── tests/
│   │   ├── examples.c
│   │   ├── examples.h
│   │   ├── test_logger.c
│   │   └── test_logger.h
│   └── CMakeLists.txt
├── resource-manager/
│   ├── tests/
│   │   ├── test_resource_manager.c
│   │   └── test_resource_manager.h
│   └── CMakeLists.txt
├── string-formatter/
│   ├── tests/
│   │   ├── test_string_formatter.c
│   │   └── test_string_formatter.h
│   └── CMakeLists.txt
└── test-framework/
    ├── src/
    │   ├── TestRegistry.c
    │   └── TestRegistry.h
    ├── tests/
    │   ├── examples.c
    │   ├── examples.h
    │   ├── test_framework.c
    │   └── test_framework.h
    └── CMakeLists.txt
```

## References

- **Phase Summary**: `/.planning/phases/30-transpile-real-world-tests/30-01-SUMMARY.md`
- **Detailed Log**: `/test-logs/transpile-real-world.log`
- **Summary Log**: `/test-logs/transpile-summary.txt`
- **Transpilation Script**: `/scripts/transpile-real-world.sh`
- **Original Projects**: `/tests/real-world/<project>/`

## Contributing

If you're working on improving the transpiler to handle real-world code:

1. Start with simple validation tests first
2. Document what you're adding to supported features
3. Update `docs/SUPPORTED_FEATURES.md`
4. Add integration tests to `tests/`
5. Only attempt real-world transpilation after validation tests pass

## Conclusion

**The transpiler is not ready for real-world C++ code.** It can handle isolated language features but lacks the STL support, multi-file coordination, and robustness needed for production code.

**Recommended focus**: Simple validation, bug fixes, feature documentation, STL compatibility layer design.

---

**Last Attempt**: 2025-12-24
**Status**: BLOCKED - Technical limitations prevent real-world transpilation
**Next Action**: Phase 30-02 - Create simple validation tests
