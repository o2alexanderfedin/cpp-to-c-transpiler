#include "Tokenizer.h"

void Tokenizer__skipWhitespace__void(struct Tokenizer * this) {
	while (this->input[this->position] == ' ' || this->input[this->position] == '\t') 	{
		this->position++;
	}
}

int Tokenizer__parseNumber__void(struct Tokenizer * this) {
	int value = 0;
	while (isdigit(this->input[this->position])) 	{
		value = value * 10 + (this->input[this->position] - '0');
		this->position++;
	}
	return value;
;
}

struct Token Tokenizer__nextToken__void(struct Tokenizer * this) {
	Tokenizer__skipWhitespace__void(&this);
	if (this->input[this->position] == '\x00') 	{
		return (Token)(Token){EndOfInput, 0};
;
	}

	if (isdigit(this->input[this->position])) 	{
		int value = Tokenizer__parseNumber__void(&this);
		return (Token){Number, value};
;
	}

	char current = this->input[this->position++];
	switch (current) 	{
	}

}

bool Tokenizer__hasMore__void(struct Tokenizer * this) {
	int pos = this->position;
	while (this->input[pos] == ' ' || this->input[pos] == '\t') 	{
		pos++;
	}
	return this->input[pos] != '\x00';
;
}

