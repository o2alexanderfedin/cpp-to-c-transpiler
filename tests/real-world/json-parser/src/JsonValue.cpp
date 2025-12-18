#include "JsonValue.h"
#include <sstream>
#include <iomanip>
#include <cmath>

namespace json {

// JsonValue type casting implementations
bool JsonValue::asBool() const {
    if (!isBool()) {
        throw std::runtime_error("Value is not a boolean");
    }
    return static_cast<const JsonBool*>(this)->getValue();
}

double JsonValue::asNumber() const {
    if (!isNumber()) {
        throw std::runtime_error("Value is not a number");
    }
    return static_cast<const JsonNumber*>(this)->getValue();
}

const std::string& JsonValue::asString() const {
    if (!isString()) {
        throw std::runtime_error("Value is not a string");
    }
    return static_cast<const JsonString*>(this)->getValue();
}

const JsonArray& JsonValue::asArray() const {
    if (!isArray()) {
        throw std::runtime_error("Value is not an array");
    }
    return *static_cast<const JsonArray*>(this);
}

const JsonObject& JsonValue::asObject() const {
    if (!isObject()) {
        throw std::runtime_error("Value is not an object");
    }
    return *static_cast<const JsonObject*>(this);
}

JsonArray& JsonValue::asArray() {
    if (!isArray()) {
        throw std::runtime_error("Value is not an array");
    }
    return *static_cast<JsonArray*>(this);
}

JsonObject& JsonValue::asObject() {
    if (!isObject()) {
        throw std::runtime_error("Value is not an object");
    }
    return *static_cast<JsonObject*>(this);
}

// JsonNumber toString
std::string JsonNumber::toString() const {
    std::ostringstream oss;

    // Check if number is integer
    if (std::floor(value_) == value_ && !std::isinf(value_) && !std::isnan(value_)) {
        oss << static_cast<long long>(value_);
    } else {
        oss << std::setprecision(17) << value_;
    }

    return oss.str();
}

// JsonString toString
std::string JsonString::toString() const {
    std::ostringstream oss;
    oss << '"';

    for (char c : value_) {
        switch (c) {
            case '"': oss << "\\\""; break;
            case '\\': oss << "\\\\"; break;
            case '\b': oss << "\\b"; break;
            case '\f': oss << "\\f"; break;
            case '\n': oss << "\\n"; break;
            case '\r': oss << "\\r"; break;
            case '\t': oss << "\\t"; break;
            default:
                if (static_cast<unsigned char>(c) < 0x20) {
                    oss << "\\u" << std::hex << std::setw(4) << std::setfill('0')
                        << static_cast<int>(c);
                } else {
                    oss << c;
                }
        }
    }

    oss << '"';
    return oss.str();
}

// JsonArray toString
std::string JsonArray::toString() const {
    if (elements_.empty()) {
        return "[]";
    }

    std::ostringstream oss;
    oss << '[';

    for (size_t i = 0; i < elements_.size(); ++i) {
        if (i > 0) oss << ", ";
        oss << elements_[i]->toString();
    }

    oss << ']';
    return oss.str();
}

// JsonArray clone
std::unique_ptr<JsonValue> JsonArray::clone() const {
    auto arr = std::make_unique<JsonArray>();
    for (const auto& elem : elements_) {
        arr->push(elem->clone());
    }
    return arr;
}

// JsonObject toString
std::string JsonObject::toString() const {
    if (members_.empty()) {
        return "{}";
    }

    std::ostringstream oss;
    oss << '{';

    bool first = true;
    for (const auto& pair : members_) {
        if (!first) oss << ", ";
        first = false;

        oss << '"' << pair.first << "\": " << pair.second->toString();
    }

    oss << '}';
    return oss.str();
}

// JsonObject clone
std::unique_ptr<JsonValue> JsonObject::clone() const {
    auto obj = std::make_unique<JsonObject>();
    for (const auto& pair : members_) {
        obj->insert(pair.first, pair.second->clone());
    }
    return obj;
}

} // namespace json
