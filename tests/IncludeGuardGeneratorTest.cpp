// TDD Tests for IncludeGuardGenerator - Epic #19 Implementation
// Story #138: Include Guard Generation

#include "IncludeGuardGenerator.h"
#include <iostream>

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Test 1: Simple filename "Point.h" → "POINT_H"
void test_SimpleFilenameToGuardName() {
    TEST_START("SimpleFilenameToGuardName");

    IncludeGuardGenerator generator;
    std::string guardName = generator.generateGuardName("Point.h");

    ASSERT(guardName == "POINT_H",
           "Expected 'POINT_H', got '" + guardName + "'");

    TEST_PASS("SimpleFilenameToGuardName");
}

// Test 2: CamelCase filename "MyClass.h" → "MYCLASS_H"
void test_CamelCaseFilename() {
    TEST_START("CamelCaseFilename");

    IncludeGuardGenerator generator;
    std::string guardName = generator.generateGuardName("MyClass.h");

    ASSERT(guardName == "MYCLASS_H",
           "Expected 'MYCLASS_H', got '" + guardName + "'");

    TEST_PASS("CamelCaseFilename");
}

// Test 3: Hyphenated filename "my-class.h" → "MY_CLASS_H"
void test_HyphenatedFilename() {
    TEST_START("HyphenatedFilename");

    IncludeGuardGenerator generator;
    std::string guardName = generator.generateGuardName("my-class.h");

    ASSERT(guardName == "MY_CLASS_H",
           "Expected 'MY_CLASS_H', got '" + guardName + "'");

    TEST_PASS("HyphenatedFilename");
}

// Test 4: Underscored filename "name_space_class.h" → "NAME_SPACE_CLASS_H"
void test_UnderscoredFilename() {
    TEST_START("UnderscoredFilename");

    IncludeGuardGenerator generator;
    std::string guardName = generator.generateGuardName("name_space_class.h");

    ASSERT(guardName == "NAME_SPACE_CLASS_H",
           "Expected 'NAME_SPACE_CLASS_H', got '" + guardName + "'");

    TEST_PASS("UnderscoredFilename");
}

// Test 5: Full guard emission
void test_GuardEmission() {
    TEST_START("GuardEmission");

    IncludeGuardGenerator generator;
    std::string guardName = "POINT_H";

    std::string guardBegin = generator.emitGuardBegin(guardName);
    std::string guardEnd = generator.emitGuardEnd(guardName);

    // Verify #ifndef and #define are emitted
    ASSERT(guardBegin.find("#ifndef POINT_H") != std::string::npos,
           "Expected '#ifndef POINT_H' in guard begin");
    ASSERT(guardBegin.find("#define POINT_H") != std::string::npos,
           "Expected '#define POINT_H' in guard begin");

    // Verify #endif is emitted
    ASSERT(guardEnd.find("#endif") != std::string::npos,
           "Expected '#endif' in guard end");
    ASSERT(guardEnd.find("POINT_H") != std::string::npos,
           "Expected 'POINT_H' comment in guard end");

    TEST_PASS("GuardEmission");
}

int main() {
    std::cout << "\n=== IncludeGuardGenerator Tests (Story #138) ===\n\n";

    // Run all tests
    test_SimpleFilenameToGuardName();
    test_CamelCaseFilename();
    test_HyphenatedFilename();
    test_UnderscoredFilename();
    test_GuardEmission();

    // Summary
    std::cout << "\n=== Test Summary ===\n";
    std::cout << "Passed: " << tests_passed << "\n";
    std::cout << "Failed: " << tests_failed << "\n";

    return tests_failed > 0 ? 1 : 0;
}
