# Project 2: Custom Container (LinkedList)

## Purpose
Demonstrates template classes with manual memory management (new/delete) without STL containers.

## Features Tested
- Template class declaration and implementation
- Manual memory management (new/delete → malloc/free in C)
- Template monomorphization (LinkedList<int>, LinkedList<float>)
- Nested struct (Node inside LinkedList)
- Destructor with cleanup

## C++23 Features Used
- None (baseline template features only)

## Expected Output
```
LinkedList<int> Tests:
  Initial size: 0
  Is empty: true
  After push_back(10, 20, 30): size = 3
  Front element: 10
  After push_front(5): size = 4, front = 5
  After pop_front(): size = 3, front = 10

LinkedList<float> Tests:
  Size: 3
  Front: 1.5

Validation: PASS
```

## Build and Run (C++)
```bash
mkdir build && cd build
cmake ..
make
./custom_container
echo $?  # Should output: 0
```

## Build and Run (Transpiled C)
```bash
# Transpile
../../../build_working/cpptoc \
    include/LinkedList.h \
    main.cpp \
    --output-dir transpiled/

# Compile
cd transpiled
gcc -I . *.c -o custom_container_c
./custom_container_c
echo $?  # Should output: 0
```

## Key Transpiler Test
This project specifically tests:
1. Template monomorphization (generates LinkedList_int and LinkedList_float)
2. Manual memory management (new/delete → malloc/free)
3. Nested struct handling
4. RAII pattern (destructor cleanup)
