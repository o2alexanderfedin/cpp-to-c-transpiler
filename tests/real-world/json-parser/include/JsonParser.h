#ifndef JSON_PARSER_H
#define JSON_PARSER_H

#include "JsonValue.h"
#include <string>
#include <memory>

namespace json {

// JSON Parser using recursive descent
class JsonParser {
private:
    const char* input_;
    const char* current_;
    size_t line_;
    size_t column_;

    // Character classification
    bool isWhitespace(char c) const {
        return c == ' ' || c == '\t' || c == '\n' || c == '\r';
    }

    bool isDigit(char c) const {
        return c >= '0' && c <= '9';
    }

    bool isHexDigit(char c) const {
        return (c >= '0' && c <= '9') ||
               (c >= 'a' && c <= 'f') ||
               (c >= 'A' && c <= 'F');
    }

    // Input management
    char peek() const {
        return *current_;
    }

    char advance() {
        char c = *current_++;
        if (c == '\n') {
            ++line_;
            column_ = 1;
        } else {
            ++column_;
        }
        return c;
    }

    bool match(char expected) {
        if (peek() != expected) return false;
        advance();
        return true;
    }

    void skipWhitespace();

    // Error handling
    [[noreturn]] void error(const std::string& message);

    // Parsing methods
    std::unique_ptr<JsonValue> parseValue();
    std::unique_ptr<JsonValue> parseNull();
    std::unique_ptr<JsonValue> parseBool();
    std::unique_ptr<JsonValue> parseNumber();
    std::unique_ptr<JsonValue> parseString();
    std::unique_ptr<JsonValue> parseArray();
    std::unique_ptr<JsonValue> parseObject();

    std::string parseStringLiteral();
    char parseEscapeSequence();
    uint32_t parseUnicodeEscape();

public:
    JsonParser() : input_(nullptr), current_(nullptr), line_(1), column_(1) {}

    // Parse JSON from string
    std::unique_ptr<JsonValue> parse(const std::string& json);
};

} // namespace json

#endif // JSON_PARSER_H
