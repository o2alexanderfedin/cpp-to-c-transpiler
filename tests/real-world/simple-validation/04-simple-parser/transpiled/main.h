// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/main.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

#include "src/ExpressionEvaluator.h"
#include "src/Token.h"
#include "src/Tokenizer.h"

typedef enum {
    TokenType__Number = 0,
    TokenType__Plus = 1,
    TokenType__Minus = 2,
    TokenType__Multiply = 3,
    TokenType__Divide = 4,
    TokenType__EndOfInput = 5
} TokenType;
static void Token__ctor_copy(struct Token * this, const struct Token * other);
static void Tokenizer__ctor_copy(struct Tokenizer * this, const struct Tokenizer * other);
static void ExpressionEvaluator__ctor_copy(struct ExpressionEvaluator * this, const struct ExpressionEvaluator * other);
int main();
