# Project 1: Math Library

## Purpose
Demonstrates basic C++ class structure with multi-file organization and mathematical operations without STL.

## Features Tested
- Classes with constructors
- Member functions (const and non-const)
- Multi-file structure (header + implementation)
- Simple mathematical operations
- No STL dependencies (uses plain float arrays)

## C++23 Features Used
- None (baseline C++ features only)

## Expected Output
```
Vector3D Tests:
  v1 = (1.0, 2.0, 3.0)
  v2 = (4.0, 5.0, 6.0)
  v1 + v2 = (5.0, 7.0, 9.0)
  v1 . v2 = 32.0
  v1 x v2 = (-3.0, 6.0, -3.0)

Matrix3x3 Tests:
  Identity * 2I = 2I (first element: 2.0)
  2I * v1 = (2.0, 4.0, 6.0)

Validation: PASS
```

## Build and Run (C++)
```bash
mkdir build && cd build
cmake ..
make
./math_library
echo $?  # Should output: 0
```

## Build and Run (Transpiled C)
```bash
# Transpile
../../../build_working/cpptoc \
    include/Vector3D.h src/Vector3D.cpp \
    include/Matrix3x3.h src/Matrix3x3.cpp \
    main.cpp \
    --output-dir transpiled/

# Compile
cd transpiled
gcc -I . *.c -o math_library_c -lm
./math_library_c
echo $?  # Should output: 0
```
