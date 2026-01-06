#ifndef EXPRESSION_EVALUATOR_H
#define EXPRESSION_EVALUATOR_H

#include "Tokenizer.h"

class ExpressionEvaluator {
private:
    Tokenizer* tokenizer;
    Token currentToken;

    void advance();
    int parseTerm();
    int parseFactor();

public:
    ExpressionEvaluator();
    ~ExpressionEvaluator();
    int evaluate(const char* expression);
};

#endif // EXPRESSION_EVALUATOR_H
