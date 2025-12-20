# Real-World Codebase Testing

This directory contains 5 representative real-world C++ projects used to validate the C++ to C transpiler on production-quality code.

## Projects

### 1. JSON Parser (1,091 LOC)
**Location**: `json-parser/`
**Features**: RAII, exceptions, recursion, templates, STL (map, vector), polymorphism
**Description**: Recursive descent JSON parser with full error handling

### 2. Logger (TBD LOC)
**Location**: `logger/`
**Features**: RAII, templates, inheritance, operator overloading, thread-safety
**Description**: Multi-level logging system with file/console outputs

### 3. Test Framework (TBD LOC)
**Location**: `test-framework/`
**Features**: Macros, templates, exceptions, RAII, function pointers
**Description**: Minimal unit test framework with assertions and test suites

### 4. String Formatter (TBD LOC)
**Location**: `string-formatter/`
**Features**: Templates, variadic templates, operator overloading, move semantics
**Description**: Type-safe string formatting utility

### 5. Resource Manager (TBD LOC)
**Location**: `resource-manager/`
**Features**: RAII, smart pointers, move semantics, exceptions, templates
**Description**: Generic resource management with custom deleters

## Total Lines of Code
Target: 10,000+ LOC across all projects
Current: 1,091 LOC (JSON Parser complete)

## Testing Infrastructure

### Build All Projects
```bash
cd tests/real-world
./build-all.sh
```

### Test All Projects
```bash
./test-all-real-world.sh
```

### Transpile and Validate
```bash
../../scripts/test-real-world.sh
```

## Validation Criteria

For each project:
1. ✓ Transpiled code compiles without errors
2. ✓ Generated code produces correct output
3. ✓ Performance within 20% of native C++
4. ✓ All C++ features correctly translated
5. ✓ Memory safe (no leaks, valgrind clean)

## Directory Structure

Each project follows:
```
<project>/
├── src/           # C++ source files
├── include/       # Header files
├── tests/         # Validation tests
├── expected/      # Expected outputs
├── CMakeLists.txt # Build configuration
└── README.md      # Project description
```

## Integration with CI/CD

These tests are integrated into:
- CMake build system (see main CMakeLists.txt)
- GitHub Actions workflow (`.github/workflows/real-world-tests.yml`)
- Automated reporting (`scripts/test-real-world.sh`)
