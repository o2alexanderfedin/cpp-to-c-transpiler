// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/src/ExpressionEvaluator.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

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
struct ExpressionEvaluator {
	struct Tokenizer * tokenizer;
	struct Token currentToken;
};
static void ExpressionEvaluator__ctor_copy(struct ExpressionEvaluator * this, const struct ExpressionEvaluator * other);
void ExpressionEvaluator__dtor(struct ExpressionEvaluator * this);
void ExpressionEvaluator__ctor_0(struct ExpressionEvaluator * this);
void ExpressionEvaluator_advance(struct ExpressionEvaluator * this);
int ExpressionEvaluator_parseFactor(struct ExpressionEvaluator * this);
int ExpressionEvaluator_parseTerm(struct ExpressionEvaluator * this);
int ExpressionEvaluator_evaluate_const_int_ptr(struct ExpressionEvaluator * this, const char * expression);
extern int result;
extern TokenType op;
extern int right;
