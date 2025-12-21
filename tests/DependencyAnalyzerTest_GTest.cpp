// tests/DependencyAnalyzerTest_GTest.cpp
// Migrated from DependencyAnalyzerTest.cpp to Google Test framework
// Story #140: Dependency Tracking

#include <gtest/gtest.h>
#include "../include/DependencyAnalyzer.h"
#include <vector>

// Test fixture for DependencyAnalyzer tests
class DependencyAnalyzerTestFixture : public ::testing::Test {
protected:
};

// Test 1: Simple case → includes own .h only
TEST_F(DependencyAnalyzerTestFixture, IncludesOwnHeaderOnly) {
    DependencyAnalyzer analyzer("Point.h");

    auto includes = analyzer.getRequiredIncludes();

    // Should include own header
    ASSERT_EQ(includes.size(), 1)
           << "Expected 1 include (own header)";
    ASSERT_EQ(includes[0], "Point.h")
           << "Expected 'Point.h' in includes";
}

// Test 2: Include order - own header should be first
TEST_F(DependencyAnalyzerTestFixture, IncludeOrderOwnHeaderFirst) {
    DependencyAnalyzer analyzer("MyClass.h");

    // Future: add runtime library dependencies
    // analyzer.addRuntimeDependency("exceptions.h");

    auto includes = analyzer.getRequiredIncludes();

    // Own header should always be first
    ASSERT_GE(includes.size(), 1)
           << "Expected at least own header";
    ASSERT_EQ(includes[0], "MyClass.h")
           << "Expected own header 'MyClass.h' to be first";
}

// Test 3: Generate #include directives
TEST_F(DependencyAnalyzerTestFixture, GenerateIncludeDirectives) {
    DependencyAnalyzer analyzer("Test.h");

    std::string includeDirectives = analyzer.emitIncludes();

    // Should contain #include "Test.h"
    ASSERT_NE(includeDirectives.find("#include \"Test.h\""), std::string::npos)
           << "Expected '#include \"Test.h\"' in output";
}

// Test 4: No duplicate includes
TEST_F(DependencyAnalyzerTestFixture, NoDuplicateIncludes) {
    DependencyAnalyzer analyzer("Foo.h");

    // Get includes multiple times
    auto includes1 = analyzer.getRequiredIncludes();
    auto includes2 = analyzer.getRequiredIncludes();

    // Should be identical (no duplicates added)
    ASSERT_EQ(includes1.size(), includes2.size())
           << "Include list should be consistent";
    ASSERT_EQ(includes1[0], includes2[0])
           << "Includes should be identical";
}

// Test 5: Extensibility for future runtime dependencies
TEST_F(DependencyAnalyzerTestFixture, ExtensibleForRuntimeDeps) {
    DependencyAnalyzer analyzer("Example.h");

    // Verify we have the method to add runtime deps (future-proofing)
    // For now, just verify structure is extensible
    auto includes = analyzer.getRequiredIncludes();

    ASSERT_GE(includes.size(), 1)
           << "Should have at least own header";

    // Future: Test addRuntimeDependency() when implemented
    // analyzer.addRuntimeDependency("runtime.h");
    // includes = analyzer.getRequiredIncludes();
    // ASSERT_EQ(includes.size(), 2) << "Should have 2 includes";
}
