// tests/IncludeGuardGeneratorTest_GTest.cpp
// Migrated from IncludeGuardGeneratorTest.cpp to Google Test framework
// Story #138: Include Guard Generation

#include <gtest/gtest.h>
#include "../include/IncludeGuardGenerator.h"

// Test fixture for IncludeGuardGenerator tests
class IncludeGuardGeneratorTestFixture : public ::testing::Test {
protected:
};

// Test 1: Simple filename "Point.h" → "POINT_H"
TEST_F(IncludeGuardGeneratorTestFixture, SimpleFilenameToGuardName) {
    IncludeGuardGenerator generator;
    std::string guardName = generator.generateGuardName("Point.h");

    ASSERT_EQ(guardName, "POINT_H")
           << "Expected 'POINT_H', got '" << guardName << "'";
}

// Test 2: CamelCase filename "MyClass.h" → "MYCLASS_H"
TEST_F(IncludeGuardGeneratorTestFixture, CamelCaseFilename) {
    IncludeGuardGenerator generator;
    std::string guardName = generator.generateGuardName("MyClass.h");

    ASSERT_EQ(guardName, "MYCLASS_H")
           << "Expected 'MYCLASS_H', got '" << guardName << "'";
}

// Test 3: Hyphenated filename "my-class.h" → "MY_CLASS_H"
TEST_F(IncludeGuardGeneratorTestFixture, HyphenatedFilename) {
    IncludeGuardGenerator generator;
    std::string guardName = generator.generateGuardName("my-class.h");

    ASSERT_EQ(guardName, "MY_CLASS_H")
           << "Expected 'MY_CLASS_H', got '" << guardName << "'";
}

// Test 4: Underscored filename "name_space_class.h" → "NAME_SPACE_CLASS_H"
TEST_F(IncludeGuardGeneratorTestFixture, UnderscoredFilename) {
    IncludeGuardGenerator generator;
    std::string guardName = generator.generateGuardName("name_space_class.h");

    ASSERT_EQ(guardName, "NAME_SPACE_CLASS_H")
           << "Expected 'NAME_SPACE_CLASS_H', got '" << guardName << "'";
}

// Test 5: Full guard emission (traditional mode)
TEST_F(IncludeGuardGeneratorTestFixture, GuardEmission) {
    IncludeGuardGenerator generator;
    std::string guardName = "POINT_H";

    std::string guardBegin = generator.emitGuardBegin(guardName);
    std::string guardEnd = generator.emitGuardEnd(guardName);

    // Verify #ifndef and #define are emitted
    ASSERT_NE(guardBegin.find("#ifndef POINT_H"), std::string::npos)
           << "Expected '#ifndef POINT_H' in guard begin";
    ASSERT_NE(guardBegin.find("#define POINT_H"), std::string::npos)
           << "Expected '#define POINT_H' in guard begin";

    // Verify #endif is emitted
    ASSERT_NE(guardEnd.find("#endif"), std::string::npos)
           << "Expected '#endif' in guard end";
    ASSERT_NE(guardEnd.find("POINT_H"), std::string::npos)
           << "Expected 'POINT_H' comment in guard end";
}

// Test 6: #pragma once mode - guard begin
TEST_F(IncludeGuardGeneratorTestFixture, PragmaOnceGuardBegin) {
    IncludeGuardGenerator generator(true); // Enable pragma once mode
    std::string guardName = "POINT_H";

    std::string guardBegin = generator.emitGuardBegin(guardName);

    // Verify #pragma once is emitted
    ASSERT_NE(guardBegin.find("#pragma once"), std::string::npos)
           << "Expected '#pragma once' in guard begin";

    // Verify traditional guards are NOT emitted
    ASSERT_EQ(guardBegin.find("#ifndef"), std::string::npos)
           << "Should not contain '#ifndef' in pragma once mode";
    ASSERT_EQ(guardBegin.find("#define"), std::string::npos)
           << "Should not contain '#define' in pragma once mode";
}

// Test 7: #pragma once mode - guard end
TEST_F(IncludeGuardGeneratorTestFixture, PragmaOnceGuardEnd) {
    IncludeGuardGenerator generator(true); // Enable pragma once mode
    std::string guardName = "POINT_H";

    std::string guardEnd = generator.emitGuardEnd(guardName);

    // In pragma once mode, guard end should be empty or minimal
    ASSERT_EQ(guardEnd.find("#endif"), std::string::npos)
           << "Should not contain '#endif' in pragma once mode";
}

// Test 8: Traditional mode explicitly set
TEST_F(IncludeGuardGeneratorTestFixture, TraditionalModeExplicit) {
    IncludeGuardGenerator generator(false); // Explicitly disable pragma once
    std::string guardName = "TEST_H";

    std::string guardBegin = generator.emitGuardBegin(guardName);
    std::string guardEnd = generator.emitGuardEnd(guardName);

    // Verify traditional guards are emitted
    ASSERT_NE(guardBegin.find("#ifndef TEST_H"), std::string::npos)
           << "Expected '#ifndef TEST_H' in traditional mode";
    ASSERT_NE(guardBegin.find("#define TEST_H"), std::string::npos)
           << "Expected '#define TEST_H' in traditional mode";
    ASSERT_NE(guardEnd.find("#endif"), std::string::npos)
           << "Expected '#endif' in traditional mode";
}

// Test 9: Toggle between modes
TEST_F(IncludeGuardGeneratorTestFixture, ModeToggle) {
    IncludeGuardGenerator generator;
    std::string guardName = "TOGGLE_H";

    // Default should be traditional
    std::string guardBegin1 = generator.emitGuardBegin(guardName);
    ASSERT_NE(guardBegin1.find("#ifndef"), std::string::npos)
           << "Default should use traditional guards";

    // Switch to pragma once
    generator.setUsePragmaOnce(true);
    std::string guardBegin2 = generator.emitGuardBegin(guardName);
    ASSERT_NE(guardBegin2.find("#pragma once"), std::string::npos)
           << "Should use pragma once after enabling";

    // Switch back to traditional
    generator.setUsePragmaOnce(false);
    std::string guardBegin3 = generator.emitGuardBegin(guardName);
    ASSERT_NE(guardBegin3.find("#ifndef"), std::string::npos)
           << "Should use traditional guards after disabling pragma once";
}
