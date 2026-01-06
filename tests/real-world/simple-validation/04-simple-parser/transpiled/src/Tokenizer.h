#pragma once

struct Tokenizer {
	const char * input;
	int position;
};
void Tokenizer__skipWhitespace__void(struct Tokenizer * this);
int Tokenizer__parseNumber__void(struct Tokenizer * this);
struct Token Tokenizer__nextToken__void(struct Tokenizer * this);
bool Tokenizer__hasMore__void(struct Tokenizer * this);
