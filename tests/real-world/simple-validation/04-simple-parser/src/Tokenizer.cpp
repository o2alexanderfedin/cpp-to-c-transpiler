#include "Tokenizer.h"
#include <cctype>

Tokenizer::Tokenizer(const char* input) : input(input), position(0) {}

void Tokenizer::skipWhitespace() {
    while (input[position] == ' ' || input[position] == '\t') {
        position++;
    }
}

int Tokenizer::parseNumber() {
    int value = 0;
    while (isdigit(input[position])) {
        value = value * 10 + (input[position] - '0');
        position++;
    }
    return value;
}

Token Tokenizer::nextToken() {
    skipWhitespace();

    if (input[position] == '\0') {
        return Token(TokenType::EndOfInput);
    }

    if (isdigit(input[position])) {
        int value = parseNumber();
        return Token(TokenType::Number, value);
    }

    char current = input[position++];
    switch (current) {
        case '+': return Token(TokenType::Plus);
        case '-': return Token(TokenType::Minus);
        case '*': return Token(TokenType::Multiply);
        case '/': return Token(TokenType::Divide);
        default: return Token(TokenType::EndOfInput);
    }
}

bool Tokenizer::hasMore() const {
    int pos = position;
    while (input[pos] == ' ' || input[pos] == '\t') {
        pos++;
    }
    return input[pos] != '\0';
}
