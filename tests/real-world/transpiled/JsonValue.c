// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/real-world/json-parser/src/JsonValue.cpp
// Implementation file

#include "JsonValue.h"

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
        bool JsonValue::asBool() const {
                if (!this->isBool()) {
                }
                return static_cast<const JsonBool *>(this)->getValue();
        }
        double JsonValue::asNumber() const {
                if (!this->isNumber()) {
                }
                return static_cast<const JsonNumber *>(this)->getValue();
        }
        const int &JsonValue::asString() const {
                if (!this->isString()) {
                }
        }
        const JsonArray &JsonValue::asArray() const {
                if (!this->isArray()) {
                }
                return *static_cast<const JsonArray *>(this);
        }
        const JsonObject &JsonValue::asObject() const {
                if (!this->isObject()) {
                }
                return *static_cast<const JsonObject *>(this);
        }
        JsonArray &JsonValue::asArray() {
                if (!this->isArray()) {
                }
                return *static_cast<JsonArray *>(this);
        }
        JsonObject &JsonValue::asObject() {
                if (!this->isObject()) {
                }
                return *static_cast<JsonObject *>(this);
        }
        int JsonNumber::toString() const {
                int oss;
                if (<recovery-expr>()) {
                        <recovery-expr>(oss) << static_cast<long long>(this->value_);
                } else {
                }
                return <recovery-expr>().str();
        }
        int JsonString::toString() const {
                int oss;
                <recovery-expr>(oss) << '"';
                <recovery-expr>(oss) << '"';
                return <recovery-expr>().str();
        }
        int JsonArray::toString() const {
                if (<recovery-expr>()) {
                        return <recovery-expr>("[]");
                }
                int oss;
                <recovery-expr>(oss) << '[';
                for (int i = <recovery-expr>(0); <recovery-expr>(); ++<recovery-expr>()) {
                        if (<recovery-expr>(i) > 0)
                                <recovery-expr>(oss) << ", ";
                }
                <recovery-expr>(oss) << ']';
                return <recovery-expr>().str();
        }
        int JsonArray::clone() const {
                auto arr;
                return <recovery-expr>();
        }
        int JsonObject::toString() const {
                if (<recovery-expr>()) {
                        return <recovery-expr>("{}");
                }
                int oss;
                <recovery-expr>(oss) << '{';
                bool first = true;
                <recovery-expr>(oss) << '}';
                return <recovery-expr>().str();
        }
        int JsonObject::clone() const {
                auto obj;
                return <recovery-expr>();
        }
}
