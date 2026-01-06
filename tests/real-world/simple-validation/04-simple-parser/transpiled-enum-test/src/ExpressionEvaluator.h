// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/./src/ExpressionEvaluator.cpp
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
struct ExpressionEvaluator {
        Tokenizer *tokenizer;
        Token currentToken;
};
static void ExpressionEvaluator__ctor_copy(struct ExpressionEvaluator * this, const struct ExpressionEvaluator * other);
void ExpressionEvaluator_advance(struct ExpressionEvaluator * this);
int ExpressionEvaluator_parseFactor(struct ExpressionEvaluator * this);
int ExpressionEvaluator_parseTerm(struct ExpressionEvaluator * this);
int ExpressionEvaluator_parseFactor(struct ExpressionEvaluator * this);
void ExpressionEvaluator__dtor(struct ExpressionEvaluator * this);
void ExpressionEvaluator_advance(struct ExpressionEvaluator * this);
int ExpressionEvaluator_parseTerm(struct ExpressionEvaluator * this);
int ExpressionEvaluator_evaluate(struct ExpressionEvaluator * this, const char * expression);
void ExpressionEvaluator__ctor(struct ExpressionEvaluator * this);
