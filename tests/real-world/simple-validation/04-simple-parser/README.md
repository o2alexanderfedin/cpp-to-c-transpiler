# Project 4: Simple Parser

## Purpose
Demonstrates string processing and parsing without std::string, using manual char* handling.

## Features Tested
- Manual string processing (const char*)
- Tokenizer pattern (lexical analysis)
- Recursive descent parser (expression evaluation)
- Operator precedence (* / before + -)
- No STL dependencies (no std::string, no std::vector)
- Manual memory management

## C++23 Features Used
- None (baseline C++ features only)

## Expected Output
```
Expression Evaluator Tests:
  2 + 3 = 5
  10 - 4 = 6
  2 * 3 + 4 = 10
  20 / 4 = 5
  2 + 3 * 4 = 14

Validation: PASS
```

## Build and Run (C++)
```bash
mkdir build && cd build
cmake ..
make
./simple_parser
echo $?  # Should output: 0
```

## Build and Run (Transpiled C)
```bash
# Transpile
../../../build_working/cpptoc \
    include/Token.h \
    include/Tokenizer.h src/Tokenizer.cpp \
    include/ExpressionEvaluator.h src/ExpressionEvaluator.cpp \
    main.cpp \
    --output-dir transpiled/

# Compile
cd transpiled
gcc -I . *.c -o simple_parser_c
./simple_parser_c
echo $?  # Should output: 0
```

## Key Transpiler Test
This project specifically tests:
1. const char* handling (C-style strings)
2. Manual string parsing (no std::string dependency)
3. Recursive function calls (parseTerm, parseFactor)
4. Operator precedence implementation
5. Manual memory management (new/delete)
