# Project 3: State Machine

## Purpose
Demonstrates enum class usage and state transition logic without STL.

## Features Tested
- Enum class (C++11 scoped enums)
- State transition validation
- Multi-file structure (header + implementation)
- Switch statements with enum cases
- No STL dependencies

## C++23 Features Used
- None (baseline C++11 enum class)

## Expected Output
```
State Machine Tests:
  Initial state: Menu
  After Menu -> Playing: Playing
  After Playing -> Paused: Paused
  After Paused -> Playing: Playing
  After Playing -> GameOver: GameOver
  After GameOver -> Playing (invalid): GameOver
  After GameOver -> Menu: Menu
  Total valid transitions: 5

Validation: PASS
```

## Build and Run (C++)
```bash
mkdir build && cd build
cmake ..
make
./state_machine
echo $?  # Should output: 0
```

## Build and Run (Transpiled C)
```bash
# Transpile
../../../build_working/cpptoc \
    include/GameState.h \
    include/StateMachine.h src/StateMachine.cpp \
    main.cpp \
    --output-dir transpiled/

# Compile
cd transpiled
gcc -I . *.c -o state_machine_c
./state_machine_c
echo $?  # Should output: 0
```

## Key Transpiler Test
This project specifically tests:
1. Enum class → C enum translation
2. State machine pattern (common in embedded systems)
3. Switch statement handling
4. Validation logic (isValidTransition)
