// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/src/Tokenizer.cpp
// Implementation file

#include "Tokenizer.h"

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

void Tokenizer__ctor(struct Tokenizer * this, const char * input) {
	this->input = input;
	this->position = 0;
}

void Tokenizer_skipWhitespace(struct Tokenizer * this) {
	while (this->input[this->position] == ' ' || this->input[this->position] == '\t') 	{
		this->position++;
	}
}

int Tokenizer_parseNumber(struct Tokenizer * this) {
	int value = 0;
	while (isdigit(this->input[this->position])) 	{
		value = value * 10 + (this->input[this->position] - '0');
		this->position++;
	}
	return value;
;
}

struct Token Tokenizer_nextToken(struct Tokenizer * this) {
	Tokenizer_skipWhitespace(this);
	if (this->input[this->position] == '\x00') 	{
		{
			struct Token __return_temp;
			Token__ctor(&__return_temp, TokenType__EndOfInput);
			return __return_temp;
;
		}
	}

	if (isdigit(this->input[this->position])) 	{
		int value = Tokenizer_parseNumber(this);
		{
			struct Token __return_temp;
			Token__ctor(&__return_temp, TokenType__Number, value);
			return __return_temp;
;
		}
	}

	char current = this->input[this->position++];
	switch (current) 	{
		case '+':
			{
				struct Token __return_temp;
				Token__ctor(&__return_temp, TokenType__Plus);
				return __return_temp;
;
			}
		case '-':
			{
				struct Token __return_temp;
				Token__ctor(&__return_temp, TokenType__Minus);
				return __return_temp;
;
			}
		case '*':
			{
				struct Token __return_temp;
				Token__ctor(&__return_temp, TokenType__Multiply);
				return __return_temp;
;
			}
		case '/':
			{
				struct Token __return_temp;
				Token__ctor(&__return_temp, TokenType__Divide);
				return __return_temp;
;
			}
		default:
			{
				struct Token __return_temp;
				Token__ctor(&__return_temp, TokenType__EndOfInput);
				return __return_temp;
;
			}
	}

}

bool Tokenizer_hasMore(struct Tokenizer * this) {
	int pos = this->position;
	while (this->input[pos] == ' ' || this->input[pos] == '\t') 	{
		pos++;
	}
	return this->input[pos] != '\x00';
;
}

int pos = this->position;
