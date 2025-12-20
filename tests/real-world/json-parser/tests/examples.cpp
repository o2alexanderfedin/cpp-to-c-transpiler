#include "JsonParser.h"
#include "JsonValue.h"
#include <iostream>
#include <fstream>
#include <sstream>

using namespace json;

// Example 1: Parse simple JSON
void exampleSimpleJSON() {
    std::string jsonStr = R"({
        "name": "John Doe",
        "age": 30,
        "email": "john.doe@example.com"
    })";

    JsonParser parser;
    auto root = parser.parse(jsonStr);

    if (root->isObject()) {
        const auto& obj = root->asObject();
        std::cout << "Name: " << obj["name"].asString() << std::endl;
        std::cout << "Age: " << obj["age"].asNumber() << std::endl;
        std::cout << "Email: " << obj["email"].asString() << std::endl;
    }
}

// Example 2: Parse nested JSON
void exampleNestedJSON() {
    std::string jsonStr = R"({
        "company": {
            "name": "Tech Corp",
            "employees": [
                {
                    "name": "Alice",
                    "role": "Engineer",
                    "skills": ["C++", "Python", "Go"]
                },
                {
                    "name": "Bob",
                    "role": "Manager",
                    "skills": ["Leadership", "Planning"]
                }
            ]
        }
    })";

    JsonParser parser;
    auto root = parser.parse(jsonStr);

    const auto& company = root->asObject()["company"].asObject();
    std::cout << "Company: " << company["name"].asString() << std::endl;

    const auto& employees = company["employees"].asArray();
    for (size_t i = 0; i < employees.size(); ++i) {
        const auto& emp = employees[i].asObject();
        std::cout << "\nEmployee " << (i + 1) << ":" << std::endl;
        std::cout << "  Name: " << emp["name"].asString() << std::endl;
        std::cout << "  Role: " << emp["role"].asString() << std::endl;

        const auto& skills = emp["skills"].asArray();
        std::cout << "  Skills: ";
        for (size_t j = 0; j < skills.size(); ++j) {
            if (j > 0) std::cout << ", ";
            std::cout << skills[j].asString();
        }
        std::cout << std::endl;
    }
}

// Example 3: Build JSON programmatically
void exampleBuildJSON() {
    auto root = std::make_unique<JsonObject>();

    root->insert("title", std::make_unique<JsonString>("Example"));
    root->insert("version", std::make_unique<JsonNumber>(1.0));
    root->insert("active", std::make_unique<JsonBool>(true));

    auto features = std::make_unique<JsonArray>();
    features->push(std::make_unique<JsonString>("Fast"));
    features->push(std::make_unique<JsonString>("Reliable"));
    features->push(std::make_unique<JsonString>("Secure"));
    root->insert("features", std::move(features));

    auto config = std::make_unique<JsonObject>();
    config->insert("timeout", std::make_unique<JsonNumber>(30));
    config->insert("retries", std::make_unique<JsonNumber>(3));
    root->insert("config", std::move(config));

    std::cout << "Built JSON: " << root->toString() << std::endl;
}

// Example 4: Parse array of objects
void exampleArrayOfObjects() {
    std::string jsonStr = R"([
        {"id": 1, "name": "Item 1", "price": 10.99},
        {"id": 2, "name": "Item 2", "price": 20.50},
        {"id": 3, "name": "Item 3", "price": 15.75}
    ])";

    JsonParser parser;
    auto root = parser.parse(jsonStr);

    const auto& items = root->asArray();
    double total = 0.0;

    for (size_t i = 0; i < items.size(); ++i) {
        const auto& item = items[i].asObject();
        int id = static_cast<int>(item["id"].asNumber());
        const std::string& name = item["name"].asString();
        double price = item["price"].asNumber();

        std::cout << "Item " << id << ": " << name << " - $" << price << std::endl;
        total += price;
    }

    std::cout << "Total: $" << total << std::endl;
}

// Example 5: Parse configuration file
void exampleConfigFile() {
    std::string config = R"({
        "database": {
            "host": "localhost",
            "port": 5432,
            "name": "mydb",
            "credentials": {
                "username": "admin",
                "password": "secret"
            }
        },
        "server": {
            "host": "0.0.0.0",
            "port": 8080,
            "workers": 4,
            "ssl": true
        },
        "logging": {
            "level": "info",
            "file": "/var/log/app.log",
            "rotate": true
        }
    })";

    JsonParser parser;
    auto root = parser.parse(config);

    const auto& obj = root->asObject();

    // Database config
    const auto& db = obj["database"].asObject();
    std::cout << "Database: " << db["host"].asString() << ":"
              << static_cast<int>(db["port"].asNumber()) << std::endl;

    // Server config
    const auto& server = obj["server"].asObject();
    std::cout << "Server: " << server["host"].asString() << ":"
              << static_cast<int>(server["port"].asNumber())
              << " (workers: " << static_cast<int>(server["workers"].asNumber()) << ")"
              << std::endl;

    // Logging config
    const auto& logging = obj["logging"].asObject();
    std::cout << "Logging: " << logging["level"].asString()
              << " -> " << logging["file"].asString() << std::endl;
}

// Example 6: Clone and modify JSON
void exampleCloneAndModify() {
    std::string original = R"({"name": "Original", "value": 100})";

    JsonParser parser;
    auto root = parser.parse(original);

    // Clone
    auto clone = root->clone();

    // Modify clone
    clone->asObject().insert("name", std::make_unique<JsonString>("Modified"));
    clone->asObject().insert("value", std::make_unique<JsonNumber>(200));

    std::cout << "Original: " << root->toString() << std::endl;
    std::cout << "Clone: " << clone->toString() << std::endl;
}

// Example 7: Handle missing keys gracefully
void exampleMissingKeys() {
    std::string jsonStr = R"({"name": "Test", "age": 25})";

    JsonParser parser;
    auto root = parser.parse(jsonStr);

    const auto& obj = root->asObject();

    // Safe access
    if (obj.contains("name")) {
        std::cout << "Name: " << obj["name"].asString() << std::endl;
    }

    if (obj.contains("email")) {
        std::cout << "Email: " << obj["email"].asString() << std::endl;
    } else {
        std::cout << "Email: (not provided)" << std::endl;
    }
}

// Example 8: Parse number types
void exampleNumberTypes() {
    std::string jsonStr = R"({
        "integer": 42,
        "negative": -100,
        "decimal": 3.14159,
        "scientific": 1.23e-4,
        "large": 1000000
    })";

    JsonParser parser;
    auto root = parser.parse(jsonStr);

    const auto& obj = root->asObject();

    std::cout << "Integer: " << obj["integer"].asNumber() << std::endl;
    std::cout << "Negative: " << obj["negative"].asNumber() << std::endl;
    std::cout << "Decimal: " << obj["decimal"].asNumber() << std::endl;
    std::cout << "Scientific: " << obj["scientific"].asNumber() << std::endl;
    std::cout << "Large: " << obj["large"].asNumber() << std::endl;
}

// Example 9: Parse boolean and null values
void exampleSpecialValues() {
    std::string jsonStr = R"({
        "enabled": true,
        "disabled": false,
        "nothing": null
    })";

    JsonParser parser;
    auto root = parser.parse(jsonStr);

    const auto& obj = root->asObject();

    std::cout << "Enabled: " << (obj["enabled"].asBool() ? "yes" : "no") << std::endl;
    std::cout << "Disabled: " << (obj["disabled"].asBool() ? "yes" : "no") << std::endl;
    std::cout << "Nothing is null: " << (obj["nothing"].isNull() ? "yes" : "no") << std::endl;
}

// Example 10: Parse escaped strings
void exampleEscapedStrings() {
    std::string jsonStr = R"({
        "quote": "He said \"Hello\"",
        "newline": "Line 1\nLine 2",
        "tab": "Column1\tColumn2",
        "backslash": "Path\\to\\file"
    })";

    JsonParser parser;
    auto root = parser.parse(jsonStr);

    const auto& obj = root->asObject();

    std::cout << "Quote: " << obj["quote"].asString() << std::endl;
    std::cout << "Newline: " << obj["newline"].asString() << std::endl;
    std::cout << "Tab: " << obj["tab"].asString() << std::endl;
    std::cout << "Backslash: " << obj["backslash"].asString() << std::endl;
}

// Example 11: Deeply nested structure
void exampleDeeplyNested() {
    std::string jsonStr = R"({
        "level1": {
            "level2": {
                "level3": {
                    "level4": {
                        "value": "deeply nested"
                    }
                }
            }
        }
    })";

    JsonParser parser;
    auto root = parser.parse(jsonStr);

    const auto& l1 = root->asObject()["level1"].asObject();
    const auto& l2 = l1["level2"].asObject();
    const auto& l3 = l2["level3"].asObject();
    const auto& l4 = l3["level4"].asObject();

    std::cout << "Deep value: " << l4["value"].asString() << std::endl;
}

// Example 12: Mixed array types
void exampleMixedArray() {
    std::string jsonStr = R"([
        42,
        "string",
        true,
        null,
        {"nested": "object"},
        [1, 2, 3]
    ])";

    JsonParser parser;
    auto root = parser.parse(jsonStr);

    const auto& arr = root->asArray();

    std::cout << "Array element types:" << std::endl;
    for (size_t i = 0; i < arr.size(); ++i) {
        std::cout << "  [" << i << "]: ";
        if (arr[i].isNumber()) std::cout << "number";
        else if (arr[i].isString()) std::cout << "string";
        else if (arr[i].isBool()) std::cout << "boolean";
        else if (arr[i].isNull()) std::cout << "null";
        else if (arr[i].isObject()) std::cout << "object";
        else if (arr[i].isArray()) std::cout << "array";
        std::cout << std::endl;
    }
}

// Example 13: Generate formatted JSON
void exampleFormattedOutput() {
    auto root = std::make_unique<JsonObject>();

    root->insert("name", std::make_unique<JsonString>("Product"));
    root->insert("price", std::make_unique<JsonNumber>(99.99));
    root->insert("inStock", std::make_unique<JsonBool>(true));

    auto tags = std::make_unique<JsonArray>();
    tags->push(std::make_unique<JsonString>("electronics"));
    tags->push(std::make_unique<JsonString>("sale"));
    root->insert("tags", std::move(tags));

    std::cout << "Compact JSON: " << root->toString() << std::endl;
}

// Example 14: Error handling
void exampleErrorHandling() {
    std::vector<std::string> invalidJSON = {
        "nul",           // Invalid null
        "tru",           // Invalid boolean
        "{unclosed",     // Unclosed object
        "[1, 2, 3,]",    // Trailing comma
        "{key: value}",  // Unquoted key
        "\"unterminated" // Unterminated string
    };

    JsonParser parser;

    for (const auto& json : invalidJSON) {
        try {
            parser.parse(json);
            std::cout << "UNEXPECTED: Parsed invalid JSON: " << json << std::endl;
        } catch (const ParseError& e) {
            std::cout << "Correctly rejected: " << json << std::endl;
        }
    }
}

// Example 15: Real-world API response
void exampleAPIResponse() {
    std::string response = R"({
        "status": "success",
        "data": {
            "users": [
                {
                    "id": 1,
                    "name": "Alice Johnson",
                    "email": "alice@example.com",
                    "roles": ["admin", "user"],
                    "active": true
                },
                {
                    "id": 2,
                    "name": "Bob Smith",
                    "email": "bob@example.com",
                    "roles": ["user"],
                    "active": true
                },
                {
                    "id": 3,
                    "name": "Charlie Brown",
                    "email": "charlie@example.com",
                    "roles": ["user"],
                    "active": false
                }
            ],
            "total": 3,
            "page": 1,
            "pageSize": 10
        },
        "timestamp": "2025-01-15T10:30:00Z"
    })";

    JsonParser parser;
    auto root = parser.parse(response);

    const auto& obj = root->asObject();
    std::cout << "Status: " << obj["status"].asString() << std::endl;
    std::cout << "Timestamp: " << obj["timestamp"].asString() << std::endl;

    const auto& data = obj["data"].asObject();
    const auto& users = data["users"].asArray();

    std::cout << "\nUsers (total: " << static_cast<int>(data["total"].asNumber()) << "):" << std::endl;

    for (size_t i = 0; i < users.size(); ++i) {
        const auto& user = users[i].asObject();
        std::cout << "  " << user["name"].asString();
        std::cout << " (" << user["email"].asString() << ")";
        std::cout << " - " << (user["active"].asBool() ? "Active" : "Inactive");

        const auto& roles = user["roles"].asArray();
        std::cout << " - Roles: ";
        for (size_t j = 0; j < roles.size(); ++j) {
            if (j > 0) std::cout << ", ";
            std::cout << roles[j].asString();
        }
        std::cout << std::endl;
    }
}

int main() {
    std::cout << "=== JSON Parser Examples ===" << std::endl << std::endl;

    std::cout << "Example 1: Simple JSON\n";
    exampleSimpleJSON();

    std::cout << "\nExample 2: Nested JSON\n";
    exampleNestedJSON();

    std::cout << "\nExample 3: Build JSON\n";
    exampleBuildJSON();

    std::cout << "\nExample 4: Array of Objects\n";
    exampleArrayOfObjects();

    std::cout << "\nExample 5: Config File\n";
    exampleConfigFile();

    std::cout << "\nExample 6: Clone and Modify\n";
    exampleCloneAndModify();

    std::cout << "\nExample 7: Missing Keys\n";
    exampleMissingKeys();

    std::cout << "\nExample 8: Number Types\n";
    exampleNumberTypes();

    std::cout << "\nExample 9: Special Values\n";
    exampleSpecialValues();

    std::cout << "\nExample 10: Escaped Strings\n";
    exampleEscapedStrings();

    std::cout << "\nExample 11: Deeply Nested\n";
    exampleDeeplyNested();

    std::cout << "\nExample 12: Mixed Array\n";
    exampleMixedArray();

    std::cout << "\nExample 13: Formatted Output\n";
    exampleFormattedOutput();

    std::cout << "\nExample 14: Error Handling\n";
    exampleErrorHandling();

    std::cout << "\nExample 15: API Response\n";
    exampleAPIResponse();

    return 0;
}
