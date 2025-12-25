// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/json-parser/tests/test_json_parser.cpp
// Header file

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
using namespace json
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST(int, int);
int TEST_int_int(int, int);
int TEST_int_int_1(int, int);
int TEST_int_int_2(int, int);
int TEST_int_int_3(int, int);
int TEST_int_int_4(int, int);
int TEST_int_int_5(int, int);
int TEST_int_int_6(int, int);
int TEST_int_int_7(int, int);
int TEST_int_int_8(int, int);
int TEST_int_int_9(int, int);
int TEST_int_int_10(int, int);
int TEST_int_int_11(int, int);
int TEST_int_int_12(int, int);
int TEST_int_int_13(int, int);
int TEST_int_int_14(int, int);
int TEST_int_int_15(int, int);
int TEST_int_int_16(int, int);
int TEST_int_int_17(int, int);
int TEST_int_int_18(int, int);
int TEST_int_int_19(int, int);
int TEST_int_int_20(int, int);
int TEST_int_int_21(int, int);
int TEST_int_int_22(int, int);
int TEST_int_int_23(int, int);
int TEST_int_int_24(int, int);
int TEST_int_int_25(int, int);
int TEST_int_int_26(int, int);
int TEST_int_int_27(int, int);
int TEST_int_int_28(int, int);
int TEST_int_int_29(int, int);
int TEST_int_int_30(int, int);
int TEST_int_int_31(int, int);
int TEST_int_int_32(int, int);
int TEST_int_int_33(int, int);
int TEST_int_int_34(int, int);
int TEST_int_int_35(int, int);
int TEST_int_int_36(int, int);
int TEST_int_int_37(int, int);
int TEST_int_int_38(int, int);
int TEST_int_int_39(int, int);
int TEST_int_int_40(int, int);
int TEST_int_int_41(int, int);
int TEST_int_int_42(int, int);
int TEST_int_int_43(int, int);
int TEST_int_int_44(int, int);
int TEST_int_int_45(int, int);
int TEST_int_int_46(int, int);
int TEST_int_int_47(int, int);
int TEST_int_int_48(int, int);
int TEST_int_int_49(int, int);
int TEST_int_int_50(int, int);
int TEST_int_int_51(int, int);
int TEST_int_int_52(int, int);
int TEST_int_int_53(int, int);
int TEST_int_int_54(int, int);
int TEST_int_int_55(int, int);
int TEST_int_int_56(int, int);
int TEST_int_int_57(int, int);
int TEST_int_int_58(int, int);
int TEST_int_int_59(int, int);
int TEST_int_int_60(int, int);
int TEST_int_int_61(int, int);
int TEST_int_int_62(int, int);
int TEST_int_int_63(int, int);
int TEST_int_int_64(int, int);
int TEST_int_int_65(int, int);
int TEST_int_int_66(int, int);
int TEST_int_int_67(int, int);
int TEST_int_int_68(int, int);
