// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/src/ExpressionEvaluator.cpp
// Implementation file

#include "ExpressionEvaluator.h"

static void Token__ctor_copy(struct Token * this, const struct Token * other) {
	this->type = other->type;
	this->value = other->value;
}

static void Tokenizer__ctor_copy(struct Tokenizer * this, const struct Tokenizer * other) {
	this->input = other->input;
	this->position = other->position;
}

static void ExpressionEvaluator__ctor_copy(struct ExpressionEvaluator * this, const struct ExpressionEvaluator * other) {
	this->tokenizer = other->tokenizer;
	Token__ctor_copy(&this->currentToken, &other->currentToken);
}

void ExpressionEvaluator__dtor(struct ExpressionEvaluator * this) {
	if (this->tokenizer != 0) 	{
		free(this->tokenizer);
	}

}

void ExpressionEvaluator__ctor_0(struct ExpressionEvaluator * this) {
	this->tokenizer = 0;
	Token__ctor_2(&this->currentToken, TokenType__EndOfInput);
}

void ExpressionEvaluator_advance(struct ExpressionEvaluator * this) {
	this->currentToken = this->tokenizer->nextToken();
}

int ExpressionEvaluator_parseFactor(struct ExpressionEvaluator * this) {
	if (this->currentToken.type == TokenType__Number) 	{
		int value = this->currentToken.value;
		ExpressionEvaluator_advance(this);
		return value;
;
	}

	return 0;
;
}

int ExpressionEvaluator_parseTerm(struct ExpressionEvaluator * this) {
	int left = ExpressionEvaluator_parseFactor(this);
	while (this->currentToken.type == TokenType__Multiply || this->currentToken.type == TokenType__Divide) 	{
		TokenType op = this->currentToken.type;
		ExpressionEvaluator_advance(this);
		int right = ExpressionEvaluator_parseFactor(this);
		if (op == TokenType__Multiply) 		{
			left = left * right;
		}
 else 		{
			left = left / right;
		}

	}
	return left;
;
}

int ExpressionEvaluator_evaluate_const_int_ptr(struct ExpressionEvaluator * this, const char * expression) {
	if (this->tokenizer != 0) 	{
		free(this->tokenizer);
	}

	this->tokenizer = malloc(sizeof(Tokenizer));
	ExpressionEvaluator_advance(this);
	int result = ExpressionEvaluator_parseTerm(this);
	while (this->currentToken.type == TokenType__Plus || this->currentToken.type == TokenType__Minus) 	{
		TokenType op = this->currentToken.type;
		ExpressionEvaluator_advance(this);
		int right = ExpressionEvaluator_parseTerm(this);
		if (op == TokenType__Plus) 		{
			result = result + right;
		}
 else 		{
			result = result - right;
		}

	}
	return result;
;
}

int result = ExpressionEvaluator_parseTerm(this);
TokenType op = this->currentToken.type;
int right = ExpressionEvaluator_parseTerm(this);
