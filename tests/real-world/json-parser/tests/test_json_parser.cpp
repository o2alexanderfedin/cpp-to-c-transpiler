#include <gtest/gtest.h>
#include "JsonParser.h"
#include "JsonValue.h"
#include <memory>

using namespace json;

// Test Null Value
TEST(JsonParserTest, ParseNull) {
    JsonParser parser;
    auto value = parser.parse("null");

    ASSERT_TRUE(value->isNull());
}

TEST(JsonParserTest, NullToString) {
    JsonParser parser;
    auto value = parser.parse("null");

    ASSERT_EQ(value->toString(), "null");
}

// Test Boolean Values
TEST(JsonParserTest, ParseTrue) {
    JsonParser parser;
    auto trueValue = parser.parse("true");

    ASSERT_TRUE(trueValue->isBool());
}

TEST(JsonParserTest, TrueValue) {
    JsonParser parser;
    auto trueValue = parser.parse("true");

    ASSERT_EQ(trueValue->asBool(), true);
}

TEST(JsonParserTest, TrueToString) {
    JsonParser parser;
    auto trueValue = parser.parse("true");

    ASSERT_EQ(trueValue->toString(), "true");
}

TEST(JsonParserTest, ParseFalse) {
    JsonParser parser;
    auto falseValue = parser.parse("false");

    ASSERT_TRUE(falseValue->isBool());
}

TEST(JsonParserTest, FalseValue) {
    JsonParser parser;
    auto falseValue = parser.parse("false");

    ASSERT_EQ(falseValue->asBool(), false);
}

TEST(JsonParserTest, FalseToString) {
    JsonParser parser;
    auto falseValue = parser.parse("false");

    ASSERT_EQ(falseValue->toString(), "false");
}

// Test Numbers
TEST(JsonParserTest, ParseInteger) {
    JsonParser parser;
    auto int1 = parser.parse("42");

    ASSERT_TRUE(int1->isNumber());
}

TEST(JsonParserTest, IntegerValue) {
    JsonParser parser;
    auto int1 = parser.parse("42");

    ASSERT_EQ(int1->asNumber(), 42.0);
}

TEST(JsonParserTest, IntegerToString) {
    JsonParser parser;
    auto int1 = parser.parse("42");

    ASSERT_EQ(int1->toString(), "42");
}

TEST(JsonParserTest, ParseNegativeInteger) {
    JsonParser parser;
    auto int2 = parser.parse("-123");

    ASSERT_EQ(int2->asNumber(), -123.0);
}

TEST(JsonParserTest, ParseDecimal) {
    JsonParser parser;
    auto dec1 = parser.parse("3.14159");

    ASSERT_TRUE(dec1->isNumber());
}

TEST(JsonParserTest, DecimalValue) {
    JsonParser parser;
    auto dec1 = parser.parse("3.14159");

    ASSERT_TRUE(dec1->asNumber() > 3.14 && dec1->asNumber() < 3.15);
}

TEST(JsonParserTest, ParseExponent) {
    JsonParser parser;
    auto exp1 = parser.parse("1e10");

    ASSERT_TRUE(exp1->isNumber());
}

TEST(JsonParserTest, ExponentValue) {
    JsonParser parser;
    auto exp1 = parser.parse("1e10");

    ASSERT_EQ(exp1->asNumber(), 1e10);
}

TEST(JsonParserTest, ParseDecimalExponent) {
    JsonParser parser;
    auto exp2 = parser.parse("2.5e-3");

    ASSERT_EQ(exp2->asNumber(), 2.5e-3);
}

// Test Strings
TEST(JsonParserTest, ParseString) {
    JsonParser parser;
    auto str1 = parser.parse("\"hello\"");

    ASSERT_TRUE(str1->isString());
}

TEST(JsonParserTest, StringValue) {
    JsonParser parser;
    auto str1 = parser.parse("\"hello\"");

    ASSERT_EQ(str1->asString(), "hello");
}

TEST(JsonParserTest, StringToString) {
    JsonParser parser;
    auto str1 = parser.parse("\"hello\"");

    ASSERT_EQ(str1->toString(), "\"hello\"");
}

TEST(JsonParserTest, StringWithPunctuation) {
    JsonParser parser;
    auto str2 = parser.parse("\"Hello, World!\"");

    ASSERT_EQ(str2->asString(), "Hello, World!");
}

TEST(JsonParserTest, StringWithEscape) {
    JsonParser parser;
    auto str3 = parser.parse("\"Line 1\\nLine 2\"");

    ASSERT_EQ(str3->asString(), "Line 1\nLine 2");
}

TEST(JsonParserTest, StringWithQuoteEscape) {
    JsonParser parser;
    auto str4 = parser.parse("\"Quote: \\\"text\\\"\"");

    ASSERT_EQ(str4->asString(), "Quote: \"text\"");
}

TEST(JsonParserTest, EmptyString) {
    JsonParser parser;
    auto str5 = parser.parse("\"\"");

    ASSERT_EQ(str5->asString(), "");
}

// Test Arrays
TEST(JsonParserTest, ParseEmptyArray) {
    JsonParser parser;
    auto arr1 = parser.parse("[]");

    ASSERT_TRUE(arr1->isArray());
}

TEST(JsonParserTest, EmptyArraySize) {
    JsonParser parser;
    auto arr1 = parser.parse("[]");

    ASSERT_EQ(arr1->asArray().size(), 0);
}

TEST(JsonParserTest, EmptyArrayToString) {
    JsonParser parser;
    auto arr1 = parser.parse("[]");

    ASSERT_EQ(arr1->toString(), "[]");
}

TEST(JsonParserTest, ParseIntegerArray) {
    JsonParser parser;
    auto arr2 = parser.parse("[1, 2, 3]");

    ASSERT_TRUE(arr2->isArray());
}

TEST(JsonParserTest, ArraySize) {
    JsonParser parser;
    auto arr2 = parser.parse("[1, 2, 3]");

    ASSERT_EQ(arr2->asArray().size(), 3);
}

TEST(JsonParserTest, ArrayElement0) {
    JsonParser parser;
    auto arr2 = parser.parse("[1, 2, 3]");

    ASSERT_EQ(arr2->asArray()[0].asNumber(), 1.0);
}

TEST(JsonParserTest, ArrayElement1) {
    JsonParser parser;
    auto arr2 = parser.parse("[1, 2, 3]");

    ASSERT_EQ(arr2->asArray()[1].asNumber(), 2.0);
}

TEST(JsonParserTest, ArrayElement2) {
    JsonParser parser;
    auto arr2 = parser.parse("[1, 2, 3]");

    ASSERT_EQ(arr2->asArray()[2].asNumber(), 3.0);
}

TEST(JsonParserTest, ParseStringArray) {
    JsonParser parser;
    auto arr3 = parser.parse("[\"a\", \"b\", \"c\"]");

    ASSERT_EQ(arr3->asArray().size(), 3);
}

TEST(JsonParserTest, StringArrayElement0) {
    JsonParser parser;
    auto arr3 = parser.parse("[\"a\", \"b\", \"c\"]");

    ASSERT_EQ(arr3->asArray()[0].asString(), "a");
}

TEST(JsonParserTest, ParseMixedArray) {
    JsonParser parser;
    auto arr4 = parser.parse("[1, \"two\", true, null]");

    ASSERT_EQ(arr4->asArray().size(), 4);
}

TEST(JsonParserTest, MixedArrayNumber) {
    JsonParser parser;
    auto arr4 = parser.parse("[1, \"two\", true, null]");

    ASSERT_EQ(arr4->asArray()[0].asNumber(), 1.0);
}

TEST(JsonParserTest, MixedArrayString) {
    JsonParser parser;
    auto arr4 = parser.parse("[1, \"two\", true, null]");

    ASSERT_EQ(arr4->asArray()[1].asString(), "two");
}

TEST(JsonParserTest, MixedArrayBool) {
    JsonParser parser;
    auto arr4 = parser.parse("[1, \"two\", true, null]");

    ASSERT_EQ(arr4->asArray()[2].asBool(), true);
}

TEST(JsonParserTest, MixedArrayNull) {
    JsonParser parser;
    auto arr4 = parser.parse("[1, \"two\", true, null]");

    ASSERT_TRUE(arr4->asArray()[3].isNull());
}

TEST(JsonParserTest, ParseNestedArray) {
    JsonParser parser;
    auto arr5 = parser.parse("[[1, 2], [3, 4]]");

    ASSERT_EQ(arr5->asArray().size(), 2);
}

TEST(JsonParserTest, NestedArrayElement) {
    JsonParser parser;
    auto arr5 = parser.parse("[[1, 2], [3, 4]]");

    ASSERT_EQ(arr5->asArray()[0].asArray()[0].asNumber(), 1.0);
}

// Test Objects
TEST(JsonParserTest, ParseEmptyObject) {
    JsonParser parser;
    auto obj1 = parser.parse("{}");

    ASSERT_TRUE(obj1->isObject());
}

TEST(JsonParserTest, EmptyObjectSize) {
    JsonParser parser;
    auto obj1 = parser.parse("{}");

    ASSERT_EQ(obj1->asObject().size(), 0);
}

TEST(JsonParserTest, EmptyObjectToString) {
    JsonParser parser;
    auto obj1 = parser.parse("{}");

    ASSERT_EQ(obj1->toString(), "{}");
}

TEST(JsonParserTest, ParseSimpleObject) {
    JsonParser parser;
    auto obj2 = parser.parse("{\"name\": \"John\"}");

    ASSERT_TRUE(obj2->isObject());
}

TEST(JsonParserTest, ObjectSize) {
    JsonParser parser;
    auto obj2 = parser.parse("{\"name\": \"John\"}");

    ASSERT_EQ(obj2->asObject().size(), 1);
}

TEST(JsonParserTest, ObjectContainsKey) {
    JsonParser parser;
    auto obj2 = parser.parse("{\"name\": \"John\"}");

    ASSERT_TRUE(obj2->asObject().contains("name"));
}

TEST(JsonParserTest, ObjectValue) {
    JsonParser parser;
    auto obj2 = parser.parse("{\"name\": \"John\"}");

    ASSERT_EQ(obj2->asObject()["name"].asString(), "John");
}

TEST(JsonParserTest, ParseMultiFieldObject) {
    JsonParser parser;
    auto obj3 = parser.parse("{\"age\": 30, \"active\": true}");

    ASSERT_EQ(obj3->asObject().size(), 2);
}

TEST(JsonParserTest, ObjectNumberField) {
    JsonParser parser;
    auto obj3 = parser.parse("{\"age\": 30, \"active\": true}");

    ASSERT_EQ(obj3->asObject()["age"].asNumber(), 30.0);
}

TEST(JsonParserTest, ObjectBoolField) {
    JsonParser parser;
    auto obj3 = parser.parse("{\"age\": 30, \"active\": true}");

    ASSERT_EQ(obj3->asObject()["active"].asBool(), true);
}

TEST(JsonParserTest, ParseNestedObject) {
    JsonParser parser;
    auto obj4 = parser.parse("{\"person\": {\"name\": \"Alice\", \"age\": 25}}");

    ASSERT_TRUE(obj4->asObject()["person"].isObject());
}

TEST(JsonParserTest, NestedObjectValue) {
    JsonParser parser;
    auto obj4 = parser.parse("{\"person\": {\"name\": \"Alice\", \"age\": 25}}");

    ASSERT_EQ(obj4->asObject()["person"].asObject()["name"].asString(), "Alice");
}

// Test Complex JSON
TEST(JsonParserTest, ParseComplexJSON) {
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
    ASSERT_TRUE(root->isObject());
}

TEST(JsonParserTest, ComplexObjectName) {
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
    const auto& obj = root->asObject();
    ASSERT_EQ(obj["name"].asString(), "Test User");
}

TEST(JsonParserTest, ComplexObjectAge) {
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
    const auto& obj = root->asObject();
    ASSERT_EQ(obj["age"].asNumber(), 30.0);
}

TEST(JsonParserTest, ComplexObjectActive) {
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
    const auto& obj = root->asObject();
    ASSERT_EQ(obj["active"].asBool(), true);
}

TEST(JsonParserTest, ComplexObjectMetadata) {
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
    const auto& obj = root->asObject();
    ASSERT_TRUE(obj["metadata"].isNull());
}

TEST(JsonParserTest, NestedAddressCity) {
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
    const auto& obj = root->asObject();
    const auto& address = obj["address"].asObject();
    ASSERT_EQ(address["city"].asString(), "Boston");
}

TEST(JsonParserTest, HobbiesArraySize) {
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
    const auto& obj = root->asObject();
    const auto& hobbies = obj["hobbies"].asArray();
    ASSERT_EQ(hobbies.size(), 3);
}

TEST(JsonParserTest, HobbiesFirst) {
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
    const auto& obj = root->asObject();
    const auto& hobbies = obj["hobbies"].asArray();
    ASSERT_EQ(hobbies[0].asString(), "reading");
}

TEST(JsonParserTest, ScoresArraySize) {
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
    const auto& obj = root->asObject();
    const auto& scores = obj["scores"].asArray();
    ASSERT_EQ(scores.size(), 3);
}

TEST(JsonParserTest, ScoresFirst) {
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
    const auto& obj = root->asObject();
    const auto& scores = obj["scores"].asArray();
    ASSERT_EQ(scores[0].asNumber(), 95.0);
}

// Test Error Handling
TEST(JsonParserTest, ErrorOnInvalidNull) {
    JsonParser parser;
    ASSERT_THROW(parser.parse("nul"), ParseError);
}

TEST(JsonParserTest, ErrorOnInvalidBoolean) {
    JsonParser parser;
    ASSERT_THROW(parser.parse("tru"), ParseError);
}

TEST(JsonParserTest, ErrorOnUnterminatedString) {
    JsonParser parser;
    ASSERT_THROW(parser.parse("\"unterminated"), ParseError);
}

TEST(JsonParserTest, ErrorOnTrailingCommaInArray) {
    JsonParser parser;
    ASSERT_THROW(parser.parse("[1, 2, 3,]"), ParseError);
}

TEST(JsonParserTest, ErrorOnTrailingCommaInObject) {
    JsonParser parser;
    ASSERT_THROW(parser.parse("{\"key\": \"value\",}"), ParseError);
}

TEST(JsonParserTest, ErrorOnMissingColon) {
    JsonParser parser;
    ASSERT_THROW(parser.parse("{\"key\" \"value\"}"), ParseError);
}

TEST(JsonParserTest, ErrorOnDuplicateKey) {
    JsonParser parser;
    ASSERT_THROW(parser.parse("{\"key\": 1, \"key\": 2}"), ParseError);
}
