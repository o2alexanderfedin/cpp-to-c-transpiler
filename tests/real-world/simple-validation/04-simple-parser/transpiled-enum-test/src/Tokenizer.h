// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/./src/Tokenizer.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

enum TokenType : int {
        Number,
        Plus,
        Minus,
        Multiply,
        Divide,
        EndOfInput
};
struct Token {
        TokenType type;
        int value;
};
static void Token__ctor_copy(struct Token * this, const struct Token * other);
void Token__ctor(struct Token * this, TokenType t, int v);
struct Tokenizer {
        const char *input;
        int position;
};
static void Tokenizer__ctor_copy(struct Tokenizer * this, const struct Tokenizer * other);
void Tokenizer_skipWhitespace(struct Tokenizer * this);
int Tokenizer_parseNumber(struct Tokenizer * this);
void Tokenizer_skipWhitespace(struct Tokenizer * this);
struct Token Tokenizer_nextToken(struct Tokenizer * this);
bool Tokenizer_hasMore(struct Tokenizer * this);
void Tokenizer__ctor(struct Tokenizer * this, const char * input);
