// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/json-parser/src/JsonParser.cpp
// Implementation file

#include "JsonParser.h"

namespace json {
        class ParseError {
        public:
                explicit ParseError(const int &message) {
                }
                ParseError(const int &message, int line, int column) {
                }
        };
        class JsonObject;
        class JsonArray;
        class JsonValue {
        public:
                enum class Type : int {
                        Null,
                        Bool,
                        Number,
                        String,
                        Array,
                        Object
                };
                virtual ~JsonValue() noexcept = default;                virtual Type getType() const = 0;
                int toString() const;
                int clone() const;
                bool isNull() const {
                        return this->getType() == Type::Null;
                }
                bool isBool() const {
                        return this->getType() == Type::Bool;
                }
                bool isNumber() const {
                        return this->getType() == Type::Number;
                }
                bool isString() const {
                        return this->getType() == Type::String;
                }
                bool isArray() const {
                        return this->getType() == Type::Array;
                }
                bool isObject() const {
                        return this->getType() == Type::Object;
                }
                bool asBool() const;
                double asNumber() const;
                const int &asString() const;
                const JsonArray &asArray() const;
                const JsonObject &asObject() const;
                JsonArray &asArray();
                JsonObject &asObject();
        };
        class JsonNull : public JsonValue {
        public:
                JsonNull() = default;
                Type getType() const override {
                        return Type::Null;
                }
                int toString() const override {
                        return <recovery-expr>("null");
                }
                int clone() const override {
                }
        };
        class JsonBool : public JsonValue {
        private:
                bool value_;
        public:
                explicit JsonBool(bool value) : value_(value) {
                }
                Type getType() const override {
                        return Type::Bool;
                }
                int toString() const override {
                        return <recovery-expr>(this->value_ ? "true" : "false");
                }
                bool getValue() const {
                        return this->value_;
                }
                int clone() const override {
                }
        };
        class JsonNumber : public JsonValue {
        private:
                double value_;
        public:
                explicit JsonNumber(double value) : value_(value) {
                }
                Type getType() const override {
                        return Type::Number;
                }
                int toString() const override;
                double getValue() const {
                        return this->value_;
                }
                int clone() const override {
                }
        };
        class JsonString : public JsonValue {
        private:
                int value_;
        public:
                explicit JsonString(const int &value) {
                }
                explicit JsonString(int &&value) {
                }
                Type getType() const override {
                        return Type::String;
                }
                int toString() const override;
                const int &getValue() const {
                }
                int clone() const override {
                }
        };
        class JsonArray : public JsonValue {
        private:
        public:
                JsonArray() = default;
                JsonArray(JsonArray &&other) noexcept {
                }
                JsonArray &operator=(JsonArray &&other) noexcept {
                        if (this != &other) {
                        }
                        return *this;
                }
                JsonArray(const JsonArray &) = delete;
                JsonArray &operator=(const JsonArray &) = delete;
                Type getType() const override {
                        return Type::Array;
                }
                int toString() const override;
                void push(int value) {
                }
                int size() const {
                }
                bool empty() const {
                }
                const JsonValue &operator[](int index) const {
                        if (<recovery-expr>()) {
                        }
                }
                JsonValue &operator[](int index) {
                        if (<recovery-expr>()) {
                        }
                }
                int clone() const override;
        };
        class JsonObject : public JsonValue {
        private:
        public:
                JsonObject() = default;
                JsonObject(JsonObject &&other) noexcept {
                }
                JsonObject &operator=(JsonObject &&other) noexcept {
                        if (this != &other) {
                        }
                        return *this;
                }
                JsonObject(const JsonObject &) = delete;
                JsonObject &operator=(const JsonObject &) = delete;
                Type getType() const override {
                        return Type::Object;
                }
                int toString() const override;
                void insert(const int &key, int value) {
                }
                bool contains(const int &key) const {
                }
                int size() const {
                }
                bool empty() const {
                }
                const JsonValue &operator[](const int &key) const {
                        auto it;
                        if (<recovery-expr>()) {
                        }
                        return *<recovery-expr>()->second;
                }
                JsonValue &operator[](const int &key) {
                        auto it;
                        if (<recovery-expr>()) {
                        }
                        return *<recovery-expr>()->second;
                }
                int clone() const override;
                int begin() const {
                }
                int end() const {
                }
        };
}
namespace json {
        class JsonParser {
        private:
                const char *input_;
                const char *current_;
                int line_;
                int column_;
                bool isWhitespace(char c) const {
                        return c == ' ' || c == '\t' || c == '\n' || c == '\r';
                }
                bool isDigit(char c) const {
                        return c >= '0' && c <= '9';
                }
                bool isHexDigit(char c) const {
                        return (c >= '0' && c <= '9') || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F');
                }
                char peek() const {
                        return *this->current_;
                }
                char advance() {
                        char c = *this->current_++;
                        if (c == '\n') {
                        } else {
                        }
                        return c;
                }
                bool match(char expected) {
                        if (this->peek() != expected)
                                return false;
                        this->advance();
                        return true;
                }
                void skipWhitespace();
                [[noreturn]] void error(const int &message);
                int parseValue();
                int parseNull();
                int parseBool();
                int parseNumber();
                int parseString();
                int parseArray();
                int parseObject();
                int parseStringLiteral();
                char parseEscapeSequence();
                int parseUnicodeEscape();
        public:
                JsonParser() : input_(nullptr), current_(nullptr) {
                }
                int parse(const int &json);
        };
}
namespace json {
        void JsonParser::skipWhitespace() {
                while (this->isWhitespace(this->peek()))
                        {
                                this->advance();
                        }
        }
        void JsonParser::error(const int &message) {
        }
        int JsonParser::parse(const int &json) {
                this->input_ = <recovery-expr>().c_str();
                this->current_ = this->input_;
                this->skipWhitespace();
                if (this->peek() == '\x00') {
                }
                auto value;
                this->skipWhitespace();
                if (this->peek() != '\x00') {
                }
                return <recovery-expr>();
        }
        int JsonParser::parseValue() {
                this->skipWhitespace();
                char c = this->peek();
                if (c == 'n') {
                } else if (c == 't' || c == 'f') {
                } else if (c == '"') {
                } else if (c == '[') {
                } else if (c == '{') {
                } else if (c == '-' || this->isDigit(c)) {
                } else if (c == '\x00') {
                } else {
                }
        }
        int JsonParser::parseNull() {
                const char *expected = "null";
                for (int i = 0; i < 4; ++i) {
                        if (this->peek() != expected[i]) {
                        }
                        this->advance();
                }
        }
        int JsonParser::parseBool() {
                if (this->peek() == 't') {
                        const char *expected = "true";
                        for (int i = 0; i < 4; ++i) {
                                if (this->peek() != expected[i]) {
                                }
                                this->advance();
                        }
                } else {
                        const char *expected = "false";
                        for (int i = 0; i < 5; ++i) {
                                if (this->peek() != expected[i]) {
                                }
                                this->advance();
                        }
                }
        }
        int JsonParser::parseNumber() {
                const char *start = this->current_;
                if (this->peek() == '-') {
                        this->advance();
                }
                if (this->peek() == '0') {
                        this->advance();
                        if (this->isDigit(this->peek())) {
                        }
                } else if (this->isDigit(this->peek())) {
                        while (this->isDigit(this->peek()))
                                {
                                        this->advance();
                                }
                } else {
                }
                if (this->peek() == '.') {
                        this->advance();
                        if (!this->isDigit(this->peek())) {
                        }
                        while (this->isDigit(this->peek()))
                                {
                                        this->advance();
                                }
                }
                if (this->peek() == 'e' || this->peek() == 'E') {
                        this->advance();
                        if (this->peek() == '+' || this->peek() == '-') {
                                this->advance();
                        }
                        if (!this->isDigit(this->peek())) {
                        }
                        while (this->isDigit(this->peek()))
                                {
                                        this->advance();
                                }
                }
                double value;
                try {
                } catch (const int &e) {
                }
        }
        int JsonParser::parseString() {
        }
        int JsonParser::parseStringLiteral() {
                if (this->peek() != '"') {
                }
                this->advance();
                int result;
                while (this->peek() != '"' && this->peek() != '\x00')
                        {
                                if (this->peek() == '\\') {
                                        this->advance();
                                        <recovery-expr>(result) += this->parseEscapeSequence();
                                } else {
                                        char c = this->peek();
                                        if (static_cast<unsigned char>(c) < 32) {
                                        }
                                        <recovery-expr>(result) += c;
                                        this->advance();
                                }
                        }
                if (this->peek() != '"') {
                }
                this->advance();
                return <recovery-expr>();
        }
        char JsonParser::parseEscapeSequence() {
                char c = this->advance();
                switch (c) {
                      case '"':
                        return '"';
                      case '\\':
                        return '\\';
                      case '/':
                        return '/';
                      case 'b':
                        return '\b';
                      case 'f':
                        return '\f';
                      case 'n':
                        return '\n';
                      case 'r':
                        return '\r';
                      case 't':
                        return '\t';
                      case 'u':
                        {
                                int codepoint;
                                if (<recovery-expr>(codepoint) > 127) {
                                }
                                return static_cast<char>(<recovery-expr>());
                        }
                      default:
                        ;
                }
        }
        int JsonParser::parseUnicodeEscape() {
                int codepoint = <recovery-expr>(0);
                for (int i = 0; i < 4; ++i) {
                        char c = this->advance();
                        if (!this->isHexDigit(c)) {
                        }
                        <recovery-expr>(codepoint) <<= 4;
                        if (c >= '0' && c <= '9') {
                                <recovery-expr>(codepoint) |= c - '0';
                        } else if (c >= 'a' && c <= 'f') {
                                <recovery-expr>(codepoint) |= c - 'a' + 10;
                        } else if (c >= 'A' && c <= 'F') {
                                <recovery-expr>(codepoint) |= c - 'A' + 10;
                        }
                }
                return <recovery-expr>();
        }
        int JsonParser::parseArray() {
                if (this->peek() != '[') {
                }
                this->advance();
                auto arr;
                this->skipWhitespace();
                if (this->peek() == ']') {
                        this->advance();
                        return <recovery-expr>();
                }
                while (true)
                        {
                                <recovery-expr>(<recovery-expr>(arr)->push);
                                this->skipWhitespace();
                                if (this->peek() == ',') {
                                        this->advance();
                                        this->skipWhitespace();
                                        if (this->peek() == ']') {
                                        }
                                } else if (this->peek() == ']') {
                                        break;
                                } else {
                                }
                        }
                this->advance();
                return <recovery-expr>();
        }
        int JsonParser::parseObject() {
                if (this->peek() != '{') {
                }
                this->advance();
                auto obj;
                this->skipWhitespace();
                if (this->peek() == '}') {
                        this->advance();
                        return <recovery-expr>();
                }
                while (true)
                        {
                                this->skipWhitespace();
                                if (this->peek() != '"') {
                                }
                                int key;
                                this->skipWhitespace();
                                if (this->peek() != ':') {
                                }
                                this->advance();
                                this->skipWhitespace();
                                auto value;
                                if (<recovery-expr>(obj)->contains(<recovery-expr>())) {
                                }
                                <recovery-expr>(<recovery-expr>(obj)->insert, <recovery-expr>());
                                this->skipWhitespace();
                                if (this->peek() == ',') {
                                        this->advance();
                                        this->skipWhitespace();
                                        if (this->peek() == '}') {
                                        }
                                } else if (this->peek() == '}') {
                                        break;
                                } else {
                                }
                        }
                this->advance();
                return <recovery-expr>();
        }
}
