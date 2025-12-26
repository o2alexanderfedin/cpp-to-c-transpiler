// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/src/ExpressionEvaluator.cpp
// Implementation file

#include "ExpressionEvaluator.h"

static void Token__ctor_copy(struct Token * this, const struct Token * other) {
	this->type = other->type;
	this->value = other->value;
}

void Token__ctor(struct Token * this, TokenType t, int v) {
	this->type = t;
	this->value = v;
}

static void Tokenizer__ctor_copy(struct Tokenizer * this, const struct Tokenizer * other) {
	this->input = other->input;
	this->position = other->position;
}

static void ExpressionEvaluator__ctor_copy(struct ExpressionEvaluator * this, const struct ExpressionEvaluator * other) {
	this->tokenizer = other->tokenizer;
	Token__ctor_copy(&this->currentToken, &other->currentToken);
}

struct Token Tokenizer_nextToken(struct Tokenizer * this);
int ExpressionEvaluator_parseTerm(struct ExpressionEvaluator * this) {
	int left = ExpressionEvaluator_parseFactor(this);

	while (this->currentToken.type == 3 || this->currentToken.type == 4) 	{
		TokenType op = this->currentToken.type;

		ExpressionEvaluator_advance(this);
		int right = ExpressionEvaluator_parseFactor(this);

		if (op == 3) 		{
			left = left * right;
		}
 else 		{
			left = left / right;
		}

	}
	return left;
;
}

int ExpressionEvaluator_parseFactor(struct ExpressionEvaluator * this) {
	if (this->currentToken.type == 0) 	{
		int value = this->currentToken.value;

		ExpressionEvaluator_advance(this);
		return value;
;
	}

	return 0;
;
}

void ExpressionEvaluator__dtor(struct ExpressionEvaluator * this) {
	if (this->tokenizer != 0) 	{
		free(this->tokenizer);
	}

}

int ExpressionEvaluator_parseTerm(struct ExpressionEvaluator * this);
int ExpressionEvaluator_evaluate(struct ExpressionEvaluator * this, const char * expression) {
	if (this->tokenizer != 0) 	{
		free(this->tokenizer);
	}

	this->tokenizer = malloc(sizeof(Tokenizer));
	ExpressionEvaluator_advance(this);
	int result = ExpressionEvaluator_parseTerm(this);

	while (this->currentToken.type == 1 || this->currentToken.type == 2) 	{
		TokenType op = this->currentToken.type;

		ExpressionEvaluator_advance(this);
		int right = ExpressionEvaluator_parseTerm(this);

		if (op == 1) 		{
			result = result + right;
		}
 else 		{
			result = result - right;
		}

	}
	return result;
;
}

void ExpressionEvaluator__ctor(struct ExpressionEvaluator * this) {
	this->tokenizer = 0;
	Token__ctor(&this->currentToken, 5);
}

