// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/simple-validation/04-simple-parser/./src/Tokenizer.cpp
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

void Tokenizer_skipWhitespace(struct Tokenizer * this) {
	while (this->input[this->position] == ' ' || this->input[this->position] == '\t')
        {
                this->position++;
        }

}

int Tokenizer_parseNumber(struct Tokenizer * this) {
	int value = 0;

	return value;

}

void Tokenizer_skipWhitespace(struct Tokenizer * this);
struct Token Tokenizer_nextToken(struct Tokenizer * this) {
	Tokenizer_skipWhitespace(this);
	if (this->input[this->position] == '\x00') {
        return Token(TokenType::EndOfInput);
}

	char current = this->input[this->position++];

	switch (current) {
      case '+':
        return Token(TokenType::Plus);
      case '-':
        return Token(TokenType::Minus);
      case '*':
        return Token(TokenType::Multiply);
      case '/':
        return Token(TokenType::Divide);
      default:
        return Token(TokenType::EndOfInput);
}

}

bool Tokenizer_hasMore(struct Tokenizer * this) {
	int pos = this->position;

	while (this->input[pos] == ' ' || this->input[pos] == '\t')
        {
                pos++;
        }

	return this->input[pos] != '\x00';

}

void Tokenizer__ctor(struct Tokenizer * this, const char * input) {
	this->input = input;
	this->position = 0;
}

