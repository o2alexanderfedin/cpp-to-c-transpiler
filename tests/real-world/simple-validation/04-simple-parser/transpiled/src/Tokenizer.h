// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/./src/Tokenizer.cpp
// Header file

#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

#include "src/Token.h"

typedef enum {
    TokenType__Number = 0,
    TokenType__Plus = 1,
    TokenType__Minus = 2,
    TokenType__Multiply = 3,
    TokenType__Divide = 4,
    TokenType__EndOfInput = 5
} TokenType;
static void Token__ctor_copy(struct Token * this, const struct Token * other);
void Token__ctor_2(struct Token * this, int t, int v);
struct Tokenizer {
	const char * input;
	int position;
};
static void Tokenizer__ctor_copy(struct Tokenizer * this, const struct Tokenizer * other);
void Tokenizer__ctor_1(struct Tokenizer * this, const char * input);
void Tokenizer_skipWhitespace(struct Tokenizer * this);
int Tokenizer_parseNumber(struct Tokenizer * this);
struct Token Tokenizer_nextToken(struct Tokenizer * this);
bool Tokenizer_hasMore(struct Tokenizer * this);
extern int pos;
