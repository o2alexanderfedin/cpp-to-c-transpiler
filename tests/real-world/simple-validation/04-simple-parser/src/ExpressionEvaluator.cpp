#include "ExpressionEvaluator.h"

ExpressionEvaluator::ExpressionEvaluator()
    : tokenizer(nullptr), currentToken(TokenType::EndOfInput) {}

ExpressionEvaluator::~ExpressionEvaluator() {
    if (tokenizer != nullptr) {
        delete tokenizer;
    }
}

void ExpressionEvaluator::advance() {
    currentToken = tokenizer->nextToken();
}

int ExpressionEvaluator::parseFactor() {
    if (currentToken.type == TokenType::Number) {
        int value = currentToken.value;
        advance();
        return value;
    }
    return 0;
}

int ExpressionEvaluator::parseTerm() {
    int left = parseFactor();

    while (currentToken.type == TokenType::Multiply ||
           currentToken.type == TokenType::Divide) {
        TokenType op = currentToken.type;
        advance();
        int right = parseFactor();

        if (op == TokenType::Multiply) {
            left = left * right;
        } else {
            left = left / right;
        }
    }

    return left;
}

int ExpressionEvaluator::evaluate(const char* expression) {
    // Clean up previous tokenizer
    if (tokenizer != nullptr) {
        delete tokenizer;
    }

    tokenizer = new Tokenizer(expression);
    advance();

    int result = parseTerm();

    while (currentToken.type == TokenType::Plus ||
           currentToken.type == TokenType::Minus) {
        TokenType op = currentToken.type;
        advance();
        int right = parseTerm();

        if (op == TokenType::Plus) {
            result = result + right;
        } else {
            result = result - right;
        }
    }

    return result;
}
