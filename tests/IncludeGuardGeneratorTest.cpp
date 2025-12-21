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

// Test 5: Full guard emission (traditional mode)
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

// Test 6: #pragma once mode - guard begin
void test_PragmaOnceGuardBegin() {
    TEST_START("PragmaOnceGuardBegin");

    IncludeGuardGenerator generator(true); // Enable pragma once mode
    std::string guardName = "POINT_H";

    std::string guardBegin = generator.emitGuardBegin(guardName);

    // Verify #pragma once is emitted
    ASSERT(guardBegin.find("#pragma once") != std::string::npos,
           "Expected '#pragma once' in guard begin");

    // Verify traditional guards are NOT emitted
    ASSERT(guardBegin.find("#ifndef") == std::string::npos,
           "Should not contain '#ifndef' in pragma once mode");
    ASSERT(guardBegin.find("#define") == std::string::npos,
           "Should not contain '#define' in pragma once mode");

    TEST_PASS("PragmaOnceGuardBegin");
}

// Test 7: #pragma once mode - guard end
void test_PragmaOnceGuardEnd() {
    TEST_START("PragmaOnceGuardEnd");

    IncludeGuardGenerator generator(true); // Enable pragma once mode
    std::string guardName = "POINT_H";

    std::string guardEnd = generator.emitGuardEnd(guardName);

    // In pragma once mode, guard end should be empty or minimal
    ASSERT(guardEnd.find("#endif") == std::string::npos,
           "Should not contain '#endif' in pragma once mode");

    TEST_PASS("PragmaOnceGuardEnd");
}

// Test 8: Traditional mode explicitly set
void test_TraditionalModeExplicit() {
    TEST_START("TraditionalModeExplicit");

    IncludeGuardGenerator generator(false); // Explicitly disable pragma once
    std::string guardName = "TEST_H";

    std::string guardBegin = generator.emitGuardBegin(guardName);
    std::string guardEnd = generator.emitGuardEnd(guardName);

    // Verify traditional guards are emitted
    ASSERT(guardBegin.find("#ifndef TEST_H") != std::string::npos,
           "Expected '#ifndef TEST_H' in traditional mode");
    ASSERT(guardBegin.find("#define TEST_H") != std::string::npos,
           "Expected '#define TEST_H' in traditional mode");
    ASSERT(guardEnd.find("#endif") != std::string::npos,
           "Expected '#endif' in traditional mode");

    TEST_PASS("TraditionalModeExplicit");
}

// Test 9: Toggle between modes
void test_ModeToggle() {
    TEST_START("ModeToggle");

    IncludeGuardGenerator generator;
    std::string guardName = "TOGGLE_H";

    // Default should be traditional
    std::string guardBegin1 = generator.emitGuardBegin(guardName);
    ASSERT(guardBegin1.find("#ifndef") != std::string::npos,
           "Default should use traditional guards");

    // Switch to pragma once
    generator.setUsePragmaOnce(true);
    std::string guardBegin2 = generator.emitGuardBegin(guardName);
    ASSERT(guardBegin2.find("#pragma once") != std::string::npos,
           "Should use pragma once after enabling");

    // Switch back to traditional
    generator.setUsePragmaOnce(false);
    std::string guardBegin3 = generator.emitGuardBegin(guardName);
    ASSERT(guardBegin3.find("#ifndef") != std::string::npos,
           "Should use traditional guards after disabling pragma once");

    TEST_PASS("ModeToggle");
}

// Test 10: Filename with path components
void test_FilenameWithPath() {
    TEST_START("FilenameWithPath");

    IncludeGuardGenerator generator;
    std::string guardName = generator.generateGuardName("include/Point.h");

    // Should only use filename, not path
    ASSERT(guardName == "POINT_H",
           "Expected 'POINT_H' from path 'include/Point.h', got '" + guardName + "'");

    TEST_PASS("FilenameWithPath");
}

int main() {
    std::cout << "\n=== IncludeGuardGenerator Tests (Story #138) ===\n\n";

    // Run all tests
    test_SimpleFilenameToGuardName();
    test_CamelCaseFilename();
    test_HyphenatedFilename();
    test_UnderscoredFilename();
    test_GuardEmission();
    test_PragmaOnceGuardBegin();
    test_PragmaOnceGuardEnd();
    test_TraditionalModeExplicit();
    test_ModeToggle();
    test_FilenameWithPath();

    // Summary
    std::cout << "\n=== Test Summary ===\n";
    std::cout << "Passed: " << tests_passed << "\n";
    std::cout << "Failed: " << tests_failed << "\n";

    return tests_failed > 0 ? 1 : 0;
}
