// TDD Tests for IncludeGuardGenerator - Epic #19 Implementation
// Story #138: Include Guard Generation
// Simple test counter

#include <gtest/gtest.h>
#include "IncludeGuardGenerator.h"

using namespace clang;

TEST(IncludeGuardGenerator, SimpleFilenameToGuardName) {
    IncludeGuardGenerator generator;
        std::string guardName = generator.generateGuardName("Point.h");

        ASSERT_TRUE(guardName == "POINT_H") << "Expected 'POINT_H', got '" + guardName + "'";
}

TEST(IncludeGuardGenerator, CamelCaseFilename) {
    IncludeGuardGenerator generator;
        std::string guardName = generator.generateGuardName("MyClass.h");

        ASSERT_TRUE(guardName == "MYCLASS_H") << "Expected 'MYCLASS_H', got '" + guardName + "'";
}

TEST(IncludeGuardGenerator, HyphenatedFilename) {
    IncludeGuardGenerator generator;
        std::string guardName = generator.generateGuardName("my-class.h");

        ASSERT_TRUE(guardName == "MY_CLASS_H") << "Expected 'MY_CLASS_H', got '" + guardName + "'";
}

TEST(IncludeGuardGenerator, UnderscoredFilename) {
    IncludeGuardGenerator generator;
        std::string guardName = generator.generateGuardName("name_space_class.h");

        ASSERT_TRUE(guardName == "NAME_SPACE_CLASS_H") << "Expected 'NAME_SPACE_CLASS_H', got '" + guardName + "'";
}

TEST(IncludeGuardGenerator, GuardEmission) {
    IncludeGuardGenerator generator;
        std::string guardName = "POINT_H";

        std::string guardBegin = generator.emitGuardBegin(guardName);
        std::string guardEnd = generator.emitGuardEnd(guardName);

        // Verify #ifndef and #define are emitted
        ASSERT_TRUE(guardBegin.find("#ifndef POINT_H") != std::string::npos) << "Expected '#ifndef POINT_H' in guard begin";
        ASSERT_TRUE(guardBegin.find("#define POINT_H") != std::string::npos) << "Expected '#define POINT_H' in guard begin";

        // Verify #endif is emitted
        ASSERT_TRUE(guardEnd.find("#endif") != std::string::npos) << "Expected '#endif' in guard end";
        ASSERT_TRUE(guardEnd.find("POINT_H") != std::string::npos) << "Expected 'POINT_H' comment in guard end";
}

TEST(IncludeGuardGenerator, PragmaOnceGuardBegin) {
    IncludeGuardGenerator generator(true); // Enable pragma once mode
        std::string guardName = "POINT_H";

        std::string guardBegin = generator.emitGuardBegin(guardName);

        // Verify #pragma once is emitted
        ASSERT_TRUE(guardBegin.find("#pragma once") != std::string::npos) << "Expected '#pragma once' in guard begin";

        // Verify traditional guards are NOT emitted
        ASSERT_TRUE(guardBegin.find("#ifndef") == std::string::npos) << "Should not contain '#ifndef' in pragma once mode";
        ASSERT_TRUE(guardBegin.find("#define") == std::string::npos) << "Should not contain '#define' in pragma once mode";
}

TEST(IncludeGuardGenerator, PragmaOnceGuardEnd) {
    IncludeGuardGenerator generator(true); // Enable pragma once mode
        std::string guardName = "POINT_H";

        std::string guardEnd = generator.emitGuardEnd(guardName);

        // In pragma once mode, guard end should be empty or minimal
        ASSERT_TRUE(guardEnd.find("#endif") == std::string::npos) << "Should not contain '#endif' in pragma once mode";
}

TEST(IncludeGuardGenerator, TraditionalModeExplicit) {
    IncludeGuardGenerator generator(false); // Explicitly disable pragma once
        std::string guardName = "TEST_H";

        std::string guardBegin = generator.emitGuardBegin(guardName);
        std::string guardEnd = generator.emitGuardEnd(guardName);

        // Verify traditional guards are emitted
        ASSERT_TRUE(guardBegin.find("#ifndef TEST_H") != std::string::npos) << "Expected '#ifndef TEST_H' in traditional mode";
        ASSERT_TRUE(guardBegin.find("#define TEST_H") != std::string::npos) << "Expected '#define TEST_H' in traditional mode";
        ASSERT_TRUE(guardEnd.find("#endif") != std::string::npos) << "Expected '#endif' in traditional mode";
}

TEST(IncludeGuardGenerator, ModeToggle) {
    IncludeGuardGenerator generator;
        std::string guardName = "TOGGLE_H";

        // Default should be traditional
        std::string guardBegin1 = generator.emitGuardBegin(guardName);
        ASSERT_TRUE(guardBegin1.find("#ifndef") != std::string::npos) << "Default should use traditional guards";

        // Switch to pragma once
        generator.setUsePragmaOnce(true);
        std::string guardBegin2 = generator.emitGuardBegin(guardName);
        ASSERT_TRUE(guardBegin2.find("#pragma once") != std::string::npos) << "Should use pragma once after enabling";

        // Switch back to traditional
        generator.setUsePragmaOnce(false);
        std::string guardBegin3 = generator.emitGuardBegin(guardName);
        ASSERT_TRUE(guardBegin3.find("#ifndef") != std::string::npos) << "Should use traditional guards after disabling pragma once";
}

TEST(IncludeGuardGenerator, FilenameWithPath) {
    IncludeGuardGenerator generator;
        std::string guardName = generator.generateGuardName("include/Point.h");

        // Should only use filename, not path
        ASSERT_TRUE(guardName == "POINT_H") << "Expected 'POINT_H' from path 'include/Point.h', got '" + guardName + "'";
}
