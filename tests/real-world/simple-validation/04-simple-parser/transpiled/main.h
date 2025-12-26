// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/main.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

typedef enum {
    Number = 0,
    Plus = 1,
    Minus = 2,
    Multiply = 3,
    Divide = 4,
    EndOfInput = 5
} TokenType;
struct Token {
	TokenType type;
	int value;
};
static void Token__ctor_copy(struct Token * this, const struct Token * other);
void Token__ctor(struct Token * this, TokenType t, int v);
struct Tokenizer {
	const char * input;
	int position;
};
static void Tokenizer__ctor_copy(struct Tokenizer * this, const struct Tokenizer * other);
struct ExpressionEvaluator {
	struct Tokenizer * tokenizer;
	struct Token currentToken;
};
static void ExpressionEvaluator__ctor_copy(struct ExpressionEvaluator * this, const struct ExpressionEvaluator * other);
void ExpressionEvaluator__dtor(struct ExpressionEvaluator * this);
int ExpressionEvaluator_evaluate(struct ExpressionEvaluator * this, const char * expression);
int main();
