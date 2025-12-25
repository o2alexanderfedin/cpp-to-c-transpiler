// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/json-parser/tests/test_json_parser.cpp
// Implementation file

#include "test_json_parser.h"

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
int TEST(int, int) {
        JsonParser parser;
        auto value = <recovery-expr>(parser)("null");
        ASSERT_TRUE(<recovery-expr>()->isNull());
}

int TEST(int, int) {
        JsonParser parser;
        auto value = <recovery-expr>(parser)("null");
        ASSERT_EQ(<recovery-expr>()->toString(), "null");
}

int TEST(int, int) {
        JsonParser parser;
        auto trueValue = <recovery-expr>(parser)("true");
        ASSERT_TRUE(<recovery-expr>()->isBool());
}

int TEST(int, int) {
        JsonParser parser;
        auto trueValue = <recovery-expr>(parser)("true");
        ASSERT_EQ(<recovery-expr>()->asBool(), true);
}

int TEST(int, int) {
        JsonParser parser;
        auto trueValue = <recovery-expr>(parser)("true");
        ASSERT_EQ(<recovery-expr>()->toString(), "true");
}

int TEST(int, int) {
        JsonParser parser;
        auto falseValue = <recovery-expr>(parser)("false");
        ASSERT_TRUE(<recovery-expr>()->isBool());
}

int TEST(int, int) {
        JsonParser parser;
        auto falseValue = <recovery-expr>(parser)("false");
        ASSERT_EQ(<recovery-expr>()->asBool(), false);
}

int TEST(int, int) {
        JsonParser parser;
        auto falseValue = <recovery-expr>(parser)("false");
        ASSERT_EQ(<recovery-expr>()->toString(), "false");
}

int TEST(int, int) {
        JsonParser parser;
        auto int1 = <recovery-expr>(parser)("42");
        ASSERT_TRUE(<recovery-expr>()->isNumber());
}

int TEST(int, int) {
        JsonParser parser;
        auto int1 = <recovery-expr>(parser)("42");
        ASSERT_EQ(<recovery-expr>()->asNumber(), 42.);
}

int TEST(int, int) {
        JsonParser parser;
        auto int1 = <recovery-expr>(parser)("42");
        ASSERT_EQ(<recovery-expr>()->toString(), "42");
}

int TEST(int, int) {
        JsonParser parser;
        auto int2 = <recovery-expr>(parser)("-123");
        ASSERT_EQ(<recovery-expr>()->asNumber(), -123.);
}

int TEST(int, int) {
        JsonParser parser;
        auto dec1 = <recovery-expr>(parser)("3.14159");
        ASSERT_TRUE(<recovery-expr>()->isNumber());
}

int TEST(int, int) {
        JsonParser parser;
        auto dec1 = <recovery-expr>(parser)("3.14159");
        ASSERT_TRUE(<recovery-expr>()->asNumber() > 3.1400000000000001 && <recovery-expr>()->asNumber() < 3.1499999999999999);
}

int TEST(int, int) {
        JsonParser parser;
        auto exp1 = <recovery-expr>(parser)("1e10");
        ASSERT_TRUE(<recovery-expr>()->isNumber());
}

int TEST(int, int) {
        JsonParser parser;
        auto exp1 = <recovery-expr>(parser)("1e10");
        ASSERT_EQ(<recovery-expr>()->asNumber(), 1.0E+10);
}

int TEST(int, int) {
        JsonParser parser;
        auto exp2 = <recovery-expr>(parser)("2.5e-3");
        ASSERT_EQ(<recovery-expr>()->asNumber(), 0.0025000000000000001);
}

int TEST(int, int) {
        JsonParser parser;
        auto str1 = <recovery-expr>(parser)("\"hello\"");
        ASSERT_TRUE(<recovery-expr>()->isString());
}

int TEST(int, int) {
        JsonParser parser;
        auto str1 = <recovery-expr>(parser)("\"hello\"");
        ASSERT_EQ(<recovery-expr>()->asString(), "hello");
}

int TEST(int, int) {
        JsonParser parser;
        auto str1 = <recovery-expr>(parser)("\"hello\"");
        ASSERT_EQ(<recovery-expr>()->toString(), "\"hello\"");
}

int TEST(int, int) {
        JsonParser parser;
        auto str2 = <recovery-expr>(parser)("\"Hello, World!\"");
        ASSERT_EQ(<recovery-expr>()->asString(), "Hello, World!");
}

int TEST(int, int) {
        JsonParser parser;
        auto str3 = <recovery-expr>(parser)("\"Line 1\\nLine 2\"");
        ASSERT_EQ(<recovery-expr>()->asString(), "Line 1\nLine 2");
}

int TEST(int, int) {
        JsonParser parser;
        auto str4 = <recovery-expr>(parser)("\"Quote: \\\"text\\\"\"");
        ASSERT_EQ(<recovery-expr>()->asString(), "Quote: \"text\"");
}

int TEST(int, int) {
        JsonParser parser;
        auto str5 = <recovery-expr>(parser)("\"\"");
        ASSERT_EQ(<recovery-expr>()->asString(), "");
}

int TEST(int, int) {
        JsonParser parser;
        auto arr1 = <recovery-expr>(parser)("[]");
        ASSERT_TRUE(<recovery-expr>()->isArray());
}

int TEST(int, int) {
        JsonParser parser;
        auto arr1 = <recovery-expr>(parser)("[]");
        ASSERT_EQ(<recovery-expr>()->asArray().size(), 0);
}

int TEST(int, int) {
        JsonParser parser;
        auto arr1 = <recovery-expr>(parser)("[]");
        ASSERT_EQ(<recovery-expr>()->toString(), "[]");
}

int TEST(int, int) {
        JsonParser parser;
        auto arr2 = <recovery-expr>(parser)("[1, 2, 3]");
        ASSERT_TRUE(<recovery-expr>()->isArray());
}

int TEST(int, int) {
        JsonParser parser;
        auto arr2 = <recovery-expr>(parser)("[1, 2, 3]");
        ASSERT_EQ(<recovery-expr>()->asArray().size(), 3);
}

int TEST(int, int) {
        JsonParser parser;
        auto arr2 = <recovery-expr>(parser)("[1, 2, 3]");
        ASSERT_EQ(<recovery-expr>()->asArray()[0].asNumber(), 1.);
}

int TEST(int, int) {
        JsonParser parser;
        auto arr2 = <recovery-expr>(parser)("[1, 2, 3]");
        ASSERT_EQ(<recovery-expr>()->asArray()[1].asNumber(), 2.);
}

int TEST(int, int) {
        JsonParser parser;
        auto arr2 = <recovery-expr>(parser)("[1, 2, 3]");
        ASSERT_EQ(<recovery-expr>()->asArray()[2].asNumber(), 3.);
}

int TEST(int, int) {
        JsonParser parser;
        auto arr3 = <recovery-expr>(parser)("[\"a\", \"b\", \"c\"]");
        ASSERT_EQ(<recovery-expr>()->asArray().size(), 3);
}

int TEST(int, int) {
        JsonParser parser;
        auto arr3 = <recovery-expr>(parser)("[\"a\", \"b\", \"c\"]");
        ASSERT_EQ(<recovery-expr>()->asArray()[0].asString(), "a");
}

int TEST(int, int) {
        JsonParser parser;
        auto arr4 = <recovery-expr>(parser)("[1, \"two\", true, null]");
        ASSERT_EQ(<recovery-expr>()->asArray().size(), 4);
}

int TEST(int, int) {
        JsonParser parser;
        auto arr4 = <recovery-expr>(parser)("[1, \"two\", true, null]");
        ASSERT_EQ(<recovery-expr>()->asArray()[0].asNumber(), 1.);
}

int TEST(int, int) {
        JsonParser parser;
        auto arr4 = <recovery-expr>(parser)("[1, \"two\", true, null]");
        ASSERT_EQ(<recovery-expr>()->asArray()[1].asString(), "two");
}

int TEST(int, int) {
        JsonParser parser;
        auto arr4 = <recovery-expr>(parser)("[1, \"two\", true, null]");
        ASSERT_EQ(<recovery-expr>()->asArray()[2].asBool(), true);
}

int TEST(int, int) {
        JsonParser parser;
        auto arr4 = <recovery-expr>(parser)("[1, \"two\", true, null]");
        ASSERT_TRUE(<recovery-expr>()->asArray()[3].isNull());
}

int TEST(int, int) {
        JsonParser parser;
        auto arr5 = <recovery-expr>(parser)("[[1, 2], [3, 4]]");
        ASSERT_EQ(<recovery-expr>()->asArray().size(), 2);
}

int TEST(int, int) {
        JsonParser parser;
        auto arr5 = <recovery-expr>(parser)("[[1, 2], [3, 4]]");
        ASSERT_EQ(<recovery-expr>()->asArray()[0].asArray()[0].asNumber(), 1.);
}

int TEST(int, int) {
        JsonParser parser;
        auto obj1 = <recovery-expr>(parser)("{}");
        ASSERT_TRUE(<recovery-expr>()->isObject());
}

int TEST(int, int) {
        JsonParser parser;
        auto obj1 = <recovery-expr>(parser)("{}");
        ASSERT_EQ(<recovery-expr>()->asObject().size(), 0);
}

int TEST(int, int) {
        JsonParser parser;
        auto obj1 = <recovery-expr>(parser)("{}");
        ASSERT_EQ(<recovery-expr>()->toString(), "{}");
}

int TEST(int, int) {
        JsonParser parser;
        auto obj2 = <recovery-expr>(parser)("{\"name\": \"John\"}");
        ASSERT_TRUE(<recovery-expr>()->isObject());
}

int TEST(int, int) {
        JsonParser parser;
        auto obj2 = <recovery-expr>(parser)("{\"name\": \"John\"}");
        ASSERT_EQ(<recovery-expr>()->asObject().size(), 1);
}

int TEST(int, int) {
        JsonParser parser;
        auto obj2 = <recovery-expr>(parser)("{\"name\": \"John\"}");
        ASSERT_TRUE(<recovery-expr>()->asObject().contains("name"));
}

int TEST(int, int) {
        JsonParser parser;
        auto obj2 = <recovery-expr>(parser)("{\"name\": \"John\"}");
        ASSERT_EQ(<recovery-expr>()->asObject()["name"].asString(), "John");
}

int TEST(int, int) {
        JsonParser parser;
        auto obj3 = <recovery-expr>(parser)("{\"age\": 30, \"active\": true}");
        ASSERT_EQ(<recovery-expr>()->asObject().size(), 2);
}

int TEST(int, int) {
        JsonParser parser;
        auto obj3 = <recovery-expr>(parser)("{\"age\": 30, \"active\": true}");
        ASSERT_EQ(<recovery-expr>()->asObject()["age"].asNumber(), 30.);
}

int TEST(int, int) {
        JsonParser parser;
        auto obj3 = <recovery-expr>(parser)("{\"age\": 30, \"active\": true}");
        ASSERT_EQ(<recovery-expr>()->asObject()["active"].asBool(), true);
}

int TEST(int, int) {
        JsonParser parser;
        auto obj4 = <recovery-expr>(parser)("{\"person\": {\"name\": \"Alice\", \"age\": 25}}");
        ASSERT_TRUE(<recovery-expr>()->asObject()["person"].isObject());
}

int TEST(int, int) {
        JsonParser parser;
        auto obj4 = <recovery-expr>(parser)("{\"person\": {\"name\": \"Alice\", \"age\": 25}}");
        ASSERT_EQ(<recovery-expr>()->asObject()["person"].asObject()["name"].asString(), "Alice");
}

int TEST(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        ASSERT_TRUE(<recovery-expr>()->isObject());
}

int TEST(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        ASSERT_EQ(<recovery-expr>()["name"].asString(), "Test User");
}

int TEST(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        ASSERT_EQ(<recovery-expr>()["age"].asNumber(), 30.);
}

int TEST(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        ASSERT_EQ(<recovery-expr>()["active"].asBool(), true);
}

int TEST(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        ASSERT_TRUE(<recovery-expr>()["metadata"].isNull());
}

int TEST(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        const auto &address = <recovery-expr>()["address"].asObject();
        ASSERT_EQ(<recovery-expr>()["city"].asString(), "Boston");
}

int TEST(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        const auto &hobbies = <recovery-expr>()["hobbies"].asArray();
        ASSERT_EQ(<recovery-expr>().size(), 3);
}

int TEST(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        const auto &hobbies = <recovery-expr>()["hobbies"].asArray();
        ASSERT_EQ(<recovery-expr>()[0].asString(), "reading");
}

int TEST(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        const auto &scores = <recovery-expr>()["scores"].asArray();
        ASSERT_EQ(<recovery-expr>().size(), 3);
}

int TEST(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        const auto &scores = <recovery-expr>()["scores"].asArray();
        ASSERT_EQ(<recovery-expr>()[0].asNumber(), 95.);
}

int TEST(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("nul"));
}

int TEST(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("tru"));
}

int TEST(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("\"unterminated"));
}

int TEST(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("[1, 2, 3,]"));
}

int TEST(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("{\"key\": \"value\",}"));
}

int TEST(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("{\"key\" \"value\"}"));
}

int TEST(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("{\"key\": 1, \"key\": 2}"));
}

int TEST(int, int) {
        JsonParser parser;
        auto value = <recovery-expr>(parser)("null");
        ASSERT_TRUE(<recovery-expr>()->isNull());
}

int TEST_int_int(int, int) {
        JsonParser parser;
        auto value = <recovery-expr>(parser)("null");
        ASSERT_EQ(<recovery-expr>()->toString(), "null");
}

int TEST_int_int_1(int, int) {
        JsonParser parser;
        auto trueValue = <recovery-expr>(parser)("true");
        ASSERT_TRUE(<recovery-expr>()->isBool());
}

int TEST_int_int_2(int, int) {
        JsonParser parser;
        auto trueValue = <recovery-expr>(parser)("true");
        ASSERT_EQ(<recovery-expr>()->asBool(), true);
}

int TEST_int_int_3(int, int) {
        JsonParser parser;
        auto trueValue = <recovery-expr>(parser)("true");
        ASSERT_EQ(<recovery-expr>()->toString(), "true");
}

int TEST_int_int_4(int, int) {
        JsonParser parser;
        auto falseValue = <recovery-expr>(parser)("false");
        ASSERT_TRUE(<recovery-expr>()->isBool());
}

int TEST_int_int_5(int, int) {
        JsonParser parser;
        auto falseValue = <recovery-expr>(parser)("false");
        ASSERT_EQ(<recovery-expr>()->asBool(), false);
}

int TEST_int_int_6(int, int) {
        JsonParser parser;
        auto falseValue = <recovery-expr>(parser)("false");
        ASSERT_EQ(<recovery-expr>()->toString(), "false");
}

int TEST_int_int_7(int, int) {
        JsonParser parser;
        auto int1 = <recovery-expr>(parser)("42");
        ASSERT_TRUE(<recovery-expr>()->isNumber());
}

int TEST_int_int_8(int, int) {
        JsonParser parser;
        auto int1 = <recovery-expr>(parser)("42");
        ASSERT_EQ(<recovery-expr>()->asNumber(), 42.);
}

int TEST_int_int_9(int, int) {
        JsonParser parser;
        auto int1 = <recovery-expr>(parser)("42");
        ASSERT_EQ(<recovery-expr>()->toString(), "42");
}

int TEST_int_int_10(int, int) {
        JsonParser parser;
        auto int2 = <recovery-expr>(parser)("-123");
        ASSERT_EQ(<recovery-expr>()->asNumber(), -123.);
}

int TEST_int_int_11(int, int) {
        JsonParser parser;
        auto dec1 = <recovery-expr>(parser)("3.14159");
        ASSERT_TRUE(<recovery-expr>()->isNumber());
}

int TEST_int_int_12(int, int) {
        JsonParser parser;
        auto dec1 = <recovery-expr>(parser)("3.14159");
        ASSERT_TRUE(<recovery-expr>()->asNumber() > 3.1400000000000001 && <recovery-expr>()->asNumber() < 3.1499999999999999);
}

int TEST_int_int_13(int, int) {
        JsonParser parser;
        auto exp1 = <recovery-expr>(parser)("1e10");
        ASSERT_TRUE(<recovery-expr>()->isNumber());
}

int TEST_int_int_14(int, int) {
        JsonParser parser;
        auto exp1 = <recovery-expr>(parser)("1e10");
        ASSERT_EQ(<recovery-expr>()->asNumber(), 1.0E+10);
}

int TEST_int_int_15(int, int) {
        JsonParser parser;
        auto exp2 = <recovery-expr>(parser)("2.5e-3");
        ASSERT_EQ(<recovery-expr>()->asNumber(), 0.0025000000000000001);
}

int TEST_int_int_16(int, int) {
        JsonParser parser;
        auto str1 = <recovery-expr>(parser)("\"hello\"");
        ASSERT_TRUE(<recovery-expr>()->isString());
}

int TEST_int_int_17(int, int) {
        JsonParser parser;
        auto str1 = <recovery-expr>(parser)("\"hello\"");
        ASSERT_EQ(<recovery-expr>()->asString(), "hello");
}

int TEST_int_int_18(int, int) {
        JsonParser parser;
        auto str1 = <recovery-expr>(parser)("\"hello\"");
        ASSERT_EQ(<recovery-expr>()->toString(), "\"hello\"");
}

int TEST_int_int_19(int, int) {
        JsonParser parser;
        auto str2 = <recovery-expr>(parser)("\"Hello, World!\"");
        ASSERT_EQ(<recovery-expr>()->asString(), "Hello, World!");
}

int TEST_int_int_20(int, int) {
        JsonParser parser;
        auto str3 = <recovery-expr>(parser)("\"Line 1\\nLine 2\"");
        ASSERT_EQ(<recovery-expr>()->asString(), "Line 1\nLine 2");
}

int TEST_int_int_21(int, int) {
        JsonParser parser;
        auto str4 = <recovery-expr>(parser)("\"Quote: \\\"text\\\"\"");
        ASSERT_EQ(<recovery-expr>()->asString(), "Quote: \"text\"");
}

int TEST_int_int_22(int, int) {
        JsonParser parser;
        auto str5 = <recovery-expr>(parser)("\"\"");
        ASSERT_EQ(<recovery-expr>()->asString(), "");
}

int TEST_int_int_23(int, int) {
        JsonParser parser;
        auto arr1 = <recovery-expr>(parser)("[]");
        ASSERT_TRUE(<recovery-expr>()->isArray());
}

int TEST_int_int_24(int, int) {
        JsonParser parser;
        auto arr1 = <recovery-expr>(parser)("[]");
        ASSERT_EQ(<recovery-expr>()->asArray().size(), 0);
}

int TEST_int_int_25(int, int) {
        JsonParser parser;
        auto arr1 = <recovery-expr>(parser)("[]");
        ASSERT_EQ(<recovery-expr>()->toString(), "[]");
}

int TEST_int_int_26(int, int) {
        JsonParser parser;
        auto arr2 = <recovery-expr>(parser)("[1, 2, 3]");
        ASSERT_TRUE(<recovery-expr>()->isArray());
}

int TEST_int_int_27(int, int) {
        JsonParser parser;
        auto arr2 = <recovery-expr>(parser)("[1, 2, 3]");
        ASSERT_EQ(<recovery-expr>()->asArray().size(), 3);
}

int TEST_int_int_28(int, int) {
        JsonParser parser;
        auto arr2 = <recovery-expr>(parser)("[1, 2, 3]");
        ASSERT_EQ(<recovery-expr>()->asArray()[0].asNumber(), 1.);
}

int TEST_int_int_29(int, int) {
        JsonParser parser;
        auto arr2 = <recovery-expr>(parser)("[1, 2, 3]");
        ASSERT_EQ(<recovery-expr>()->asArray()[1].asNumber(), 2.);
}

int TEST_int_int_30(int, int) {
        JsonParser parser;
        auto arr2 = <recovery-expr>(parser)("[1, 2, 3]");
        ASSERT_EQ(<recovery-expr>()->asArray()[2].asNumber(), 3.);
}

int TEST_int_int_31(int, int) {
        JsonParser parser;
        auto arr3 = <recovery-expr>(parser)("[\"a\", \"b\", \"c\"]");
        ASSERT_EQ(<recovery-expr>()->asArray().size(), 3);
}

int TEST_int_int_32(int, int) {
        JsonParser parser;
        auto arr3 = <recovery-expr>(parser)("[\"a\", \"b\", \"c\"]");
        ASSERT_EQ(<recovery-expr>()->asArray()[0].asString(), "a");
}

int TEST_int_int_33(int, int) {
        JsonParser parser;
        auto arr4 = <recovery-expr>(parser)("[1, \"two\", true, null]");
        ASSERT_EQ(<recovery-expr>()->asArray().size(), 4);
}

int TEST_int_int_34(int, int) {
        JsonParser parser;
        auto arr4 = <recovery-expr>(parser)("[1, \"two\", true, null]");
        ASSERT_EQ(<recovery-expr>()->asArray()[0].asNumber(), 1.);
}

int TEST_int_int_35(int, int) {
        JsonParser parser;
        auto arr4 = <recovery-expr>(parser)("[1, \"two\", true, null]");
        ASSERT_EQ(<recovery-expr>()->asArray()[1].asString(), "two");
}

int TEST_int_int_36(int, int) {
        JsonParser parser;
        auto arr4 = <recovery-expr>(parser)("[1, \"two\", true, null]");
        ASSERT_EQ(<recovery-expr>()->asArray()[2].asBool(), true);
}

int TEST_int_int_37(int, int) {
        JsonParser parser;
        auto arr4 = <recovery-expr>(parser)("[1, \"two\", true, null]");
        ASSERT_TRUE(<recovery-expr>()->asArray()[3].isNull());
}

int TEST_int_int_38(int, int) {
        JsonParser parser;
        auto arr5 = <recovery-expr>(parser)("[[1, 2], [3, 4]]");
        ASSERT_EQ(<recovery-expr>()->asArray().size(), 2);
}

int TEST_int_int_39(int, int) {
        JsonParser parser;
        auto arr5 = <recovery-expr>(parser)("[[1, 2], [3, 4]]");
        ASSERT_EQ(<recovery-expr>()->asArray()[0].asArray()[0].asNumber(), 1.);
}

int TEST_int_int_40(int, int) {
        JsonParser parser;
        auto obj1 = <recovery-expr>(parser)("{}");
        ASSERT_TRUE(<recovery-expr>()->isObject());
}

int TEST_int_int_41(int, int) {
        JsonParser parser;
        auto obj1 = <recovery-expr>(parser)("{}");
        ASSERT_EQ(<recovery-expr>()->asObject().size(), 0);
}

int TEST_int_int_42(int, int) {
        JsonParser parser;
        auto obj1 = <recovery-expr>(parser)("{}");
        ASSERT_EQ(<recovery-expr>()->toString(), "{}");
}

int TEST_int_int_43(int, int) {
        JsonParser parser;
        auto obj2 = <recovery-expr>(parser)("{\"name\": \"John\"}");
        ASSERT_TRUE(<recovery-expr>()->isObject());
}

int TEST_int_int_44(int, int) {
        JsonParser parser;
        auto obj2 = <recovery-expr>(parser)("{\"name\": \"John\"}");
        ASSERT_EQ(<recovery-expr>()->asObject().size(), 1);
}

int TEST_int_int_45(int, int) {
        JsonParser parser;
        auto obj2 = <recovery-expr>(parser)("{\"name\": \"John\"}");
        ASSERT_TRUE(<recovery-expr>()->asObject().contains("name"));
}

int TEST_int_int_46(int, int) {
        JsonParser parser;
        auto obj2 = <recovery-expr>(parser)("{\"name\": \"John\"}");
        ASSERT_EQ(<recovery-expr>()->asObject()["name"].asString(), "John");
}

int TEST_int_int_47(int, int) {
        JsonParser parser;
        auto obj3 = <recovery-expr>(parser)("{\"age\": 30, \"active\": true}");
        ASSERT_EQ(<recovery-expr>()->asObject().size(), 2);
}

int TEST_int_int_48(int, int) {
        JsonParser parser;
        auto obj3 = <recovery-expr>(parser)("{\"age\": 30, \"active\": true}");
        ASSERT_EQ(<recovery-expr>()->asObject()["age"].asNumber(), 30.);
}

int TEST_int_int_49(int, int) {
        JsonParser parser;
        auto obj3 = <recovery-expr>(parser)("{\"age\": 30, \"active\": true}");
        ASSERT_EQ(<recovery-expr>()->asObject()["active"].asBool(), true);
}

int TEST_int_int_50(int, int) {
        JsonParser parser;
        auto obj4 = <recovery-expr>(parser)("{\"person\": {\"name\": \"Alice\", \"age\": 25}}");
        ASSERT_TRUE(<recovery-expr>()->asObject()["person"].isObject());
}

int TEST_int_int_51(int, int) {
        JsonParser parser;
        auto obj4 = <recovery-expr>(parser)("{\"person\": {\"name\": \"Alice\", \"age\": 25}}");
        ASSERT_EQ(<recovery-expr>()->asObject()["person"].asObject()["name"].asString(), "Alice");
}

int TEST_int_int_52(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        ASSERT_TRUE(<recovery-expr>()->isObject());
}

int TEST_int_int_53(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        ASSERT_EQ(<recovery-expr>()["name"].asString(), "Test User");
}

int TEST_int_int_54(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        ASSERT_EQ(<recovery-expr>()["age"].asNumber(), 30.);
}

int TEST_int_int_55(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        ASSERT_EQ(<recovery-expr>()["active"].asBool(), true);
}

int TEST_int_int_56(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        ASSERT_TRUE(<recovery-expr>()["metadata"].isNull());
}

int TEST_int_int_57(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        const auto &address = <recovery-expr>()["address"].asObject();
        ASSERT_EQ(<recovery-expr>()["city"].asString(), "Boston");
}

int TEST_int_int_58(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        const auto &hobbies = <recovery-expr>()["hobbies"].asArray();
        ASSERT_EQ(<recovery-expr>().size(), 3);
}

int TEST_int_int_59(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        const auto &hobbies = <recovery-expr>()["hobbies"].asArray();
        ASSERT_EQ(<recovery-expr>()[0].asString(), "reading");
}

int TEST_int_int_60(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        const auto &scores = <recovery-expr>()["scores"].asArray();
        ASSERT_EQ(<recovery-expr>().size(), 3);
}

int TEST_int_int_61(int, int) {
        JsonParser parser;
        auto root = <recovery-expr>(parser)(<recovery-expr>());
        const auto &obj = <recovery-expr>()->asObject();
        const auto &scores = <recovery-expr>()["scores"].asArray();
        ASSERT_EQ(<recovery-expr>()[0].asNumber(), 95.);
}

int TEST_int_int_62(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("nul"));
}

int TEST_int_int_63(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("tru"));
}

int TEST_int_int_64(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("\"unterminated"));
}

int TEST_int_int_65(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("[1, 2, 3,]"));
}

int TEST_int_int_66(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("{\"key\": \"value\",}"));
}

int TEST_int_int_67(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("{\"key\" \"value\"}"));
}

int TEST_int_int_68(int, int) {
        JsonParser parser;
        <recovery-expr>(ASSERT_THROW, <recovery-expr>(parser)("{\"key\": 1, \"key\": 2}"));
}

