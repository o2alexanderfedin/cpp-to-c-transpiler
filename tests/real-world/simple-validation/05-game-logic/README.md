# Project 5: Game Logic

## Purpose
Demonstrates inheritance, virtual functions, and polymorphism without STL.

## Features Tested
- Abstract base class (Entity with pure virtual function)
- Inheritance (Player and Enemy inherit from Entity)
- Virtual functions and override
- Static member functions (CollisionDetector)
- AABB collision detection
- No STL dependencies

## C++23 Features Used
- None (baseline C++ OOP features)

## Expected Output
```
Game Logic Tests:
  Player: pos=(100.0, 100.0), health=100, score=0
  Enemy: pos=(150.0, 100.0), damage=10
  Initial collision: false
  After enemy moves to (110, 100): collision = true
  Player takes 10 damage
  Player health after damage: 90
  Player score after +100: 100
  Point (115, 115) inside player: true

Validation: PASS
```

## Build and Run (C++)
```bash
mkdir build && cd build
cmake ..
make
./game_logic
echo $?  # Should output: 0
```

## Build and Run (Transpiled C)
```bash
# Transpile
../../../build_working/cpptoc \
    include/Entity.h src/Entity.cpp \
    include/Player.h src/Player.cpp \
    include/Enemy.h src/Enemy.cpp \
    include/CollisionDetector.h src/CollisionDetector.cpp \
    main.cpp \
    --output-dir transpiled/

# Compile
cd transpiled
gcc -I . *.c -o game_logic_c
./game_logic_c
echo $?  # Should output: 0
```

## Key Transpiler Test
This project specifically tests:
1. Abstract base classes (pure virtual functions)
2. Inheritance hierarchy (Entity -> Player/Enemy)
3. Virtual function dispatch (vtable generation)
4. Override keyword handling
5. Static member functions
6. AABB collision detection algorithm
