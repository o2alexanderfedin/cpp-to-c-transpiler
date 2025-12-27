// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/./src/ExpressionEvaluator.cpp
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

void ExpressionEvaluator_advance(struct ExpressionEvaluator * this) {
	this->currentToken = this->tokenizer->nextToken();
}

int ExpressionEvaluator_parseFactor(struct ExpressionEvaluator * this);
int ExpressionEvaluator_parseTerm(struct ExpressionEvaluator * this) {
	int left = ExpressionEvaluator_parseFactor(this);

	while (this->currentToken.type == TokenType::Multiply || this->currentToken.type == TokenType::Divide)
        {
                TokenType op = this->currentToken.type;
                this->advance();
                int right = this->parseFactor();
                if (op == TokenType::Multiply) {
                        left = left * right;
                } else {
                        left = left / right;
                }
        }

	return left;

}

int ExpressionEvaluator_parseFactor(struct ExpressionEvaluator * this) {
	if (this->currentToken.type == TokenType::Number) {
        int value = this->currentToken.value;
        this->advance();
        return value;
}

	return 0;

}

void ExpressionEvaluator__dtor(struct ExpressionEvaluator * this) {
	if (this->tokenizer != nullptr) {
        delete this->tokenizer;
}

}

void ExpressionEvaluator_advance(struct ExpressionEvaluator * this);
int ExpressionEvaluator_parseTerm(struct ExpressionEvaluator * this);
int ExpressionEvaluator_evaluate(struct ExpressionEvaluator * this, const char * expression) {
	if (this->tokenizer != nullptr) {
        delete this->tokenizer;
}

	this->tokenizer = new Tokenizer(expression);
	ExpressionEvaluator_advance(this);
	int result = ExpressionEvaluator_parseTerm(this);

	while (this->currentToken.type == TokenType::Plus || this->currentToken.type == TokenType::Minus)
        {
                TokenType op = this->currentToken.type;
                this->advance();
                int right = this->parseTerm();
                if (op == TokenType::Plus) {
                        result = result + right;
                } else {
                        result = result - right;
                }
        }

	return result;

}

void ExpressionEvaluator__ctor(struct ExpressionEvaluator * this) {
	this->tokenizer = nullptr;
	Token__ctor(&this->currentToken, TokenType::EndOfInput);
}

