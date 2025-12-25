#ifndef TOKEN_H
#define TOKEN_H

enum class TokenType {
    Number,
    Plus,
    Minus,
    Multiply,
    Divide,
    EndOfInput
};

struct Token {
    TokenType type;
    int value;  // Only used for Number tokens

    Token(TokenType t, int v = 0) : type(t), value(v) {}
};

#endif // TOKEN_H
