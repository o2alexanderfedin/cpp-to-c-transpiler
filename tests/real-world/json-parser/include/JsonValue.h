#ifndef JSON_VALUE_H
#define JSON_VALUE_H

#include <string>
#include <map>
#include <vector>
#include <memory>
#include <stdexcept>

namespace json {

// Exception for JSON parsing errors
class ParseError : public std::runtime_error {
public:
    explicit ParseError(const std::string& message)
        : std::runtime_error("JSON Parse Error: " + message) {}

    ParseError(const std::string& message, size_t line, size_t column)
        : std::runtime_error("JSON Parse Error at line " + std::to_string(line) +
                           ", column " + std::to_string(column) + ": " + message) {}
};

// Forward declarations
class JsonObject;
class JsonArray;

// Base class for all JSON values (polymorphic)
class JsonValue {
public:
    enum class Type {
        Null,
        Bool,
        Number,
        String,
        Array,
        Object
    };

    virtual ~JsonValue() = default;

    virtual Type getType() const = 0;
    virtual std::string toString() const = 0;
    virtual std::unique_ptr<JsonValue> clone() const = 0;

    // Type checking
    bool isNull() const { return getType() == Type::Null; }
    bool isBool() const { return getType() == Type::Bool; }
    bool isNumber() const { return getType() == Type::Number; }
    bool isString() const { return getType() == Type::String; }
    bool isArray() const { return getType() == Type::Array; }
    bool isObject() const { return getType() == Type::Object; }

    // Type casting (throws if wrong type)
    bool asBool() const;
    double asNumber() const;
    const std::string& asString() const;
    const JsonArray& asArray() const;
    const JsonObject& asObject() const;

    JsonArray& asArray();
    JsonObject& asObject();
};

// JSON Null value
class JsonNull : public JsonValue {
public:
    JsonNull() = default;

    Type getType() const override { return Type::Null; }
    std::string toString() const override { return "null"; }
    std::unique_ptr<JsonValue> clone() const override {
        return std::make_unique<JsonNull>();
    }
};

// JSON Boolean value
class JsonBool : public JsonValue {
private:
    bool value_;

public:
    explicit JsonBool(bool value) : value_(value) {}

    Type getType() const override { return Type::Bool; }
    std::string toString() const override { return value_ ? "true" : "false"; }
    bool getValue() const { return value_; }

    std::unique_ptr<JsonValue> clone() const override {
        return std::make_unique<JsonBool>(value_);
    }
};

// JSON Number value
class JsonNumber : public JsonValue {
private:
    double value_;

public:
    explicit JsonNumber(double value) : value_(value) {}

    Type getType() const override { return Type::Number; }
    std::string toString() const override;
    double getValue() const { return value_; }

    std::unique_ptr<JsonValue> clone() const override {
        return std::make_unique<JsonNumber>(value_);
    }
};

// JSON String value
class JsonString : public JsonValue {
private:
    std::string value_;

public:
    explicit JsonString(const std::string& value) : value_(value) {}
    explicit JsonString(std::string&& value) : value_(std::move(value)) {}

    Type getType() const override { return Type::String; }
    std::string toString() const override;
    const std::string& getValue() const { return value_; }

    std::unique_ptr<JsonValue> clone() const override {
        return std::make_unique<JsonString>(value_);
    }
};

// JSON Array value
class JsonArray : public JsonValue {
private:
    std::vector<std::unique_ptr<JsonValue>> elements_;

public:
    JsonArray() = default;

    // Move constructor
    JsonArray(JsonArray&& other) noexcept : elements_(std::move(other.elements_)) {}

    // Move assignment
    JsonArray& operator=(JsonArray&& other) noexcept {
        if (this != &other) {
            elements_ = std::move(other.elements_);
        }
        return *this;
    }

    // Delete copy (unique_ptr cannot be copied)
    JsonArray(const JsonArray&) = delete;
    JsonArray& operator=(const JsonArray&) = delete;

    Type getType() const override { return Type::Array; }
    std::string toString() const override;

    void push(std::unique_ptr<JsonValue> value) {
        elements_.push_back(std::move(value));
    }

    size_t size() const { return elements_.size(); }
    bool empty() const { return elements_.empty(); }

    const JsonValue& operator[](size_t index) const {
        if (index >= elements_.size()) {
            throw std::out_of_range("Array index out of range");
        }
        return *elements_[index];
    }

    JsonValue& operator[](size_t index) {
        if (index >= elements_.size()) {
            throw std::out_of_range("Array index out of range");
        }
        return *elements_[index];
    }

    std::unique_ptr<JsonValue> clone() const override;
};

// JSON Object value
class JsonObject : public JsonValue {
private:
    std::map<std::string, std::unique_ptr<JsonValue>> members_;

public:
    JsonObject() = default;

    // Move constructor
    JsonObject(JsonObject&& other) noexcept : members_(std::move(other.members_)) {}

    // Move assignment
    JsonObject& operator=(JsonObject&& other) noexcept {
        if (this != &other) {
            members_ = std::move(other.members_);
        }
        return *this;
    }

    // Delete copy (unique_ptr cannot be copied)
    JsonObject(const JsonObject&) = delete;
    JsonObject& operator=(const JsonObject&) = delete;

    Type getType() const override { return Type::Object; }
    std::string toString() const override;

    void insert(const std::string& key, std::unique_ptr<JsonValue> value) {
        members_[key] = std::move(value);
    }

    bool contains(const std::string& key) const {
        return members_.find(key) != members_.end();
    }

    size_t size() const { return members_.size(); }
    bool empty() const { return members_.empty(); }

    const JsonValue& operator[](const std::string& key) const {
        auto it = members_.find(key);
        if (it == members_.end()) {
            throw std::out_of_range("Key not found: " + key);
        }
        return *it->second;
    }

    JsonValue& operator[](const std::string& key) {
        auto it = members_.find(key);
        if (it == members_.end()) {
            throw std::out_of_range("Key not found: " + key);
        }
        return *it->second;
    }

    std::unique_ptr<JsonValue> clone() const override;

    // Iterator access
    using const_iterator = std::map<std::string, std::unique_ptr<JsonValue>>::const_iterator;
    const_iterator begin() const { return members_.begin(); }
    const_iterator end() const { return members_.end(); }
};

} // namespace json

#endif // JSON_VALUE_H
