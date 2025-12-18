#include "JsonParser.h"
#include <cctype>
#include <cstring>
#include <sstream>

namespace json {

void JsonParser::skipWhitespace() {
    while (isWhitespace(peek())) {
        advance();
    }
}

void JsonParser::error(const std::string& message) {
    throw ParseError(message, line_, column_);
}

std::unique_ptr<JsonValue> JsonParser::parse(const std::string& json) {
    input_ = json.c_str();
    current_ = input_;
    line_ = 1;
    column_ = 1;

    skipWhitespace();

    if (peek() == '\0') {
        error("Empty JSON input");
    }

    auto value = parseValue();

    skipWhitespace();
    if (peek() != '\0') {
        error("Unexpected characters after JSON value");
    }

    return value;
}

std::unique_ptr<JsonValue> JsonParser::parseValue() {
    skipWhitespace();

    char c = peek();

    if (c == 'n') {
        return parseNull();
    } else if (c == 't' || c == 'f') {
        return parseBool();
    } else if (c == '"') {
        return parseString();
    } else if (c == '[') {
        return parseArray();
    } else if (c == '{') {
        return parseObject();
    } else if (c == '-' || isDigit(c)) {
        return parseNumber();
    } else if (c == '\0') {
        error("Unexpected end of input");
    } else {
        error(std::string("Unexpected character: '") + c + "'");
    }
}

std::unique_ptr<JsonValue> JsonParser::parseNull() {
    const char* expected = "null";
    for (int i = 0; i < 4; ++i) {
        if (peek() != expected[i]) {
            error("Invalid null literal");
        }
        advance();
    }
    return std::make_unique<JsonNull>();
}

std::unique_ptr<JsonValue> JsonParser::parseBool() {
    if (peek() == 't') {
        const char* expected = "true";
        for (int i = 0; i < 4; ++i) {
            if (peek() != expected[i]) {
                error("Invalid boolean literal");
            }
            advance();
        }
        return std::make_unique<JsonBool>(true);
    } else {
        const char* expected = "false";
        for (int i = 0; i < 5; ++i) {
            if (peek() != expected[i]) {
                error("Invalid boolean literal");
            }
            advance();
        }
        return std::make_unique<JsonBool>(false);
    }
}

std::unique_ptr<JsonValue> JsonParser::parseNumber() {
    const char* start = current_;

    // Optional minus sign
    if (peek() == '-') {
        advance();
    }

    // Integer part
    if (peek() == '0') {
        advance();
        // After leading zero, must be decimal point or end
        if (isDigit(peek())) {
            error("Invalid number: leading zero");
        }
    } else if (isDigit(peek())) {
        while (isDigit(peek())) {
            advance();
        }
    } else {
        error("Invalid number: expected digit");
    }

    // Fractional part
    if (peek() == '.') {
        advance();
        if (!isDigit(peek())) {
            error("Invalid number: expected digit after decimal point");
        }
        while (isDigit(peek())) {
            advance();
        }
    }

    // Exponent part
    if (peek() == 'e' || peek() == 'E') {
        advance();
        if (peek() == '+' || peek() == '-') {
            advance();
        }
        if (!isDigit(peek())) {
            error("Invalid number: expected digit in exponent");
        }
        while (isDigit(peek())) {
            advance();
        }
    }

    // Convert to double
    std::string numStr(start, current_);
    double value;
    try {
        value = std::stod(numStr);
    } catch (const std::exception& e) {
        error("Invalid number format");
    }

    return std::make_unique<JsonNumber>(value);
}

std::unique_ptr<JsonValue> JsonParser::parseString() {
    return std::make_unique<JsonString>(parseStringLiteral());
}

std::string JsonParser::parseStringLiteral() {
    if (peek() != '"') {
        error("Expected '\"'");
    }
    advance(); // Skip opening quote

    std::string result;

    while (peek() != '"' && peek() != '\0') {
        if (peek() == '\\') {
            advance(); // Skip backslash
            result += parseEscapeSequence();
        } else {
            char c = peek();
            if (static_cast<unsigned char>(c) < 0x20) {
                error("Invalid control character in string");
            }
            result += c;
            advance();
        }
    }

    if (peek() != '"') {
        error("Unterminated string");
    }
    advance(); // Skip closing quote

    return result;
}

char JsonParser::parseEscapeSequence() {
    char c = advance();

    switch (c) {
        case '"': return '"';
        case '\\': return '\\';
        case '/': return '/';
        case 'b': return '\b';
        case 'f': return '\f';
        case 'n': return '\n';
        case 'r': return '\r';
        case 't': return '\t';
        case 'u': {
            uint32_t codepoint = parseUnicodeEscape();
            // For simplicity, only handle ASCII range
            if (codepoint > 127) {
                error("Non-ASCII Unicode escape not supported in this implementation");
            }
            return static_cast<char>(codepoint);
        }
        default:
            error(std::string("Invalid escape sequence: \\") + c);
    }
}

uint32_t JsonParser::parseUnicodeEscape() {
    uint32_t codepoint = 0;

    for (int i = 0; i < 4; ++i) {
        char c = advance();
        if (!isHexDigit(c)) {
            error("Invalid unicode escape sequence");
        }

        codepoint <<= 4;
        if (c >= '0' && c <= '9') {
            codepoint |= c - '0';
        } else if (c >= 'a' && c <= 'f') {
            codepoint |= c - 'a' + 10;
        } else if (c >= 'A' && c <= 'F') {
            codepoint |= c - 'A' + 10;
        }
    }

    return codepoint;
}

std::unique_ptr<JsonValue> JsonParser::parseArray() {
    if (peek() != '[') {
        error("Expected '['");
    }
    advance(); // Skip '['

    auto arr = std::make_unique<JsonArray>();

    skipWhitespace();

    // Empty array
    if (peek() == ']') {
        advance();
        return arr;
    }

    // Parse elements
    while (true) {
        arr->push(parseValue());

        skipWhitespace();

        if (peek() == ',') {
            advance();
            skipWhitespace();

            // Trailing comma check
            if (peek() == ']') {
                error("Trailing comma in array");
            }
        } else if (peek() == ']') {
            break;
        } else {
            error("Expected ',' or ']' in array");
        }
    }

    advance(); // Skip ']'
    return arr;
}

std::unique_ptr<JsonValue> JsonParser::parseObject() {
    if (peek() != '{') {
        error("Expected '{'");
    }
    advance(); // Skip '{'

    auto obj = std::make_unique<JsonObject>();

    skipWhitespace();

    // Empty object
    if (peek() == '}') {
        advance();
        return obj;
    }

    // Parse members
    while (true) {
        skipWhitespace();

        // Parse key
        if (peek() != '"') {
            error("Expected string key in object");
        }
        std::string key = parseStringLiteral();

        skipWhitespace();

        // Parse colon
        if (peek() != ':') {
            error("Expected ':' after object key");
        }
        advance();

        skipWhitespace();

        // Parse value
        auto value = parseValue();

        // Insert into object
        if (obj->contains(key)) {
            error("Duplicate key in object: " + key);
        }
        obj->insert(key, std::move(value));

        skipWhitespace();

        if (peek() == ',') {
            advance();
            skipWhitespace();

            // Trailing comma check
            if (peek() == '}') {
                error("Trailing comma in object");
            }
        } else if (peek() == '}') {
            break;
        } else {
            error("Expected ',' or '}' in object");
        }
    }

    advance(); // Skip '}'
    return obj;
}

} // namespace json
