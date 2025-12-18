#include "JsonParser.h"
#include "JsonValue.h"
#include <iostream>
#include <cassert>
#include <memory>

using namespace json;

// Test helper
void test(const std::string& name, bool condition) {
    if (condition) {
        std::cout << "[PASS] " << name << std::endl;
    } else {
        std::cout << "[FAIL] " << name << std::endl;
        throw std::runtime_error("Test failed: " + name);
    }
}

void testNullValue() {
    JsonParser parser;
    auto value = parser.parse("null");

    test("Parse null", value->isNull());
    test("Null toString", value->toString() == "null");
}

void testBooleanValues() {
    JsonParser parser;

    auto trueValue = parser.parse("true");
    test("Parse true", trueValue->isBool());
    test("True value", trueValue->asBool() == true);
    test("True toString", trueValue->toString() == "true");

    auto falseValue = parser.parse("false");
    test("Parse false", falseValue->isBool());
    test("False value", falseValue->asBool() == false);
    test("False toString", falseValue->toString() == "false");
}

void testNumbers() {
    JsonParser parser;

    auto int1 = parser.parse("42");
    test("Parse integer", int1->isNumber());
    test("Integer value", int1->asNumber() == 42.0);
    test("Integer toString", int1->toString() == "42");

    auto int2 = parser.parse("-123");
    test("Parse negative integer", int2->asNumber() == -123.0);

    auto dec1 = parser.parse("3.14159");
    test("Parse decimal", dec1->isNumber());
    test("Decimal value", dec1->asNumber() > 3.14 && dec1->asNumber() < 3.15);

    auto exp1 = parser.parse("1e10");
    test("Parse exponent", exp1->isNumber());
    test("Exponent value", exp1->asNumber() == 1e10);

    auto exp2 = parser.parse("2.5e-3");
    test("Parse decimal exponent", exp2->asNumber() == 2.5e-3);
}

void testStrings() {
    JsonParser parser;

    auto str1 = parser.parse("\"hello\"");
    test("Parse string", str1->isString());
    test("String value", str1->asString() == "hello");
    test("String toString", str1->toString() == "\"hello\"");

    auto str2 = parser.parse("\"Hello, World!\"");
    test("String with punctuation", str2->asString() == "Hello, World!");

    auto str3 = parser.parse("\"Line 1\\nLine 2\"");
    test("String with escape", str3->asString() == "Line 1\nLine 2");

    auto str4 = parser.parse("\"Quote: \\\"text\\\"\"");
    test("String with quote escape", str4->asString() == "Quote: \"text\"");

    auto str5 = parser.parse("\"\"");
    test("Empty string", str5->asString() == "");
}

void testArrays() {
    JsonParser parser;

    auto arr1 = parser.parse("[]");
    test("Parse empty array", arr1->isArray());
    test("Empty array size", arr1->asArray().size() == 0);
    test("Empty array toString", arr1->toString() == "[]");

    auto arr2 = parser.parse("[1, 2, 3]");
    test("Parse integer array", arr2->isArray());
    test("Array size", arr2->asArray().size() == 3);
    test("Array element 0", arr2->asArray()[0].asNumber() == 1.0);
    test("Array element 1", arr2->asArray()[1].asNumber() == 2.0);
    test("Array element 2", arr2->asArray()[2].asNumber() == 3.0);

    auto arr3 = parser.parse("[\"a\", \"b\", \"c\"]");
    test("Parse string array", arr3->asArray().size() == 3);
    test("String array element 0", arr3->asArray()[0].asString() == "a");

    auto arr4 = parser.parse("[1, \"two\", true, null]");
    test("Parse mixed array", arr4->asArray().size() == 4);
    test("Mixed array number", arr4->asArray()[0].asNumber() == 1.0);
    test("Mixed array string", arr4->asArray()[1].asString() == "two");
    test("Mixed array bool", arr4->asArray()[2].asBool() == true);
    test("Mixed array null", arr4->asArray()[3].isNull());

    auto arr5 = parser.parse("[[1, 2], [3, 4]]");
    test("Parse nested array", arr5->asArray().size() == 2);
    test("Nested array element", arr5->asArray()[0].asArray()[0].asNumber() == 1.0);
}

void testObjects() {
    JsonParser parser;

    auto obj1 = parser.parse("{}");
    test("Parse empty object", obj1->isObject());
    test("Empty object size", obj1->asObject().size() == 0);
    test("Empty object toString", obj1->toString() == "{}");

    auto obj2 = parser.parse("{\"name\": \"John\"}");
    test("Parse simple object", obj2->isObject());
    test("Object size", obj2->asObject().size() == 1);
    test("Object contains key", obj2->asObject().contains("name"));
    test("Object value", obj2->asObject()["name"].asString() == "John");

    auto obj3 = parser.parse("{\"age\": 30, \"active\": true}");
    test("Parse multi-field object", obj3->asObject().size() == 2);
    test("Object number field", obj3->asObject()["age"].asNumber() == 30.0);
    test("Object bool field", obj3->asObject()["active"].asBool() == true);

    auto obj4 = parser.parse("{\"person\": {\"name\": \"Alice\", \"age\": 25}}");
    test("Parse nested object", obj4->asObject()["person"].isObject());
    test("Nested object value",
         obj4->asObject()["person"].asObject()["name"].asString() == "Alice");
}

void testComplexJSON() {
    JsonParser parser;

    std::string json = R"({
        "name": "Test User",
        "age": 30,
        "active": true,
        "address": {
            "street": "123 Main St",
            "city": "Boston",
            "zip": "02101"
        },
        "hobbies": ["reading", "coding", "hiking"],
        "scores": [95, 87, 92],
        "metadata": null
    })";

    auto root = parser.parse(json);
    test("Parse complex JSON", root->isObject());

    const auto& obj = root->asObject();
    test("Complex object name", obj["name"].asString() == "Test User");
    test("Complex object age", obj["age"].asNumber() == 30.0);
    test("Complex object active", obj["active"].asBool() == true);
    test("Complex object metadata", obj["metadata"].isNull());

    const auto& address = obj["address"].asObject();
    test("Nested address city", address["city"].asString() == "Boston");

    const auto& hobbies = obj["hobbies"].asArray();
    test("Hobbies array size", hobbies.size() == 3);
    test("Hobbies first", hobbies[0].asString() == "reading");

    const auto& scores = obj["scores"].asArray();
    test("Scores array size", scores.size() == 3);
    test("Scores first", scores[0].asNumber() == 95.0);
}

void testErrorHandling() {
    JsonParser parser;
    bool caught;

    // Invalid null
    caught = false;
    try {
        parser.parse("nul");
    } catch (const ParseError& e) {
        caught = true;
    }
    test("Error on invalid null", caught);

    // Invalid boolean
    caught = false;
    try {
        parser.parse("tru");
    } catch (const ParseError& e) {
        caught = true;
    }
    test("Error on invalid boolean", caught);

    // Unterminated string
    caught = false;
    try {
        parser.parse("\"unterminated");
    } catch (const ParseError& e) {
        caught = true;
    }
    test("Error on unterminated string", caught);

    // Trailing comma in array
    caught = false;
    try {
        parser.parse("[1, 2, 3,]");
    } catch (const ParseError& e) {
        caught = true;
    }
    test("Error on trailing comma in array", caught);

    // Trailing comma in object
    caught = false;
    try {
        parser.parse("{\"key\": \"value\",}");
    } catch (const ParseError& e) {
        caught = true;
    }
    test("Error on trailing comma in object", caught);

    // Missing colon
    caught = false;
    try {
        parser.parse("{\"key\" \"value\"}");
    } catch (const ParseError& e) {
        caught = true;
    }
    test("Error on missing colon", caught);

    // Duplicate key
    caught = false;
    try {
        parser.parse("{\"key\": 1, \"key\": 2}");
    } catch (const ParseError& e) {
        caught = true;
    }
    test("Error on duplicate key", caught);
}

int main() {
    try {
        std::cout << "=== JSON Parser Tests ===" << std::endl;

        testNullValue();
        testBooleanValues();
        testNumbers();
        testStrings();
        testArrays();
        testObjects();
        testComplexJSON();
        testErrorHandling();

        std::cout << "\n=== All tests passed! ===" << std::endl;
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Test failed with exception: " << e.what() << std::endl;
        return 1;
    }
}
