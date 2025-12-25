#ifndef TOKENIZER_H
#define TOKENIZER_H

#include "Token.h"

class Tokenizer {
private:
    const char* input;
    int position;

    void skipWhitespace();
    int parseNumber();

public:
    Tokenizer(const char* input);
    Token nextToken();
    bool hasMore() const;
};

#endif // TOKENIZER_H
