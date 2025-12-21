// TDD Tests for DependencyAnalyzer - Epic #19 Implementation
// Story #140: Dependency Tracking
// Simple test counter

#include <gtest/gtest.h>
#include "DependencyAnalyzer.h"
#include <vector>

using namespace clang;

TEST(DependencyAnalyzer, IncludesOwnHeaderOnly) {
    DependencyAnalyzer analyzer("Point.h");

        auto includes = analyzer.getRequiredIncludes();

        // Should include own header
        ASSERT_TRUE(includes.size() == 1) << "Expected 1 include (own header;");
        ASSERT_TRUE(includes[0] == "Point.h") << "Expected 'Point.h' in includes";
}

TEST(DependencyAnalyzer, IncludeOrderOwnHeaderFirst) {
    DependencyAnalyzer analyzer("MyClass.h");

        // Future: add runtime library dependencies
        // analyzer.addRuntimeDependency("exceptions.h");

        auto includes = analyzer.getRequiredIncludes();

        // Own header should always be first
        ASSERT_TRUE(includes.size() >= 1) << "Expected at least own header";
        ASSERT_TRUE(includes[0] == "MyClass.h") << "Expected own header 'MyClass.h' to be first";
}

TEST(DependencyAnalyzer, GenerateIncludeDirectives) {
    DependencyAnalyzer analyzer("Test.h");

        std::string includeDirectives = analyzer.emitIncludes();

        // Should contain #include "Test.h"
        ASSERT_TRUE(includeDirectives.find("#include \"Test.h\"") != std::string::npos) << "Expected '#include \"Test.h\"' in output";
}

TEST(DependencyAnalyzer, NoDuplicateIncludes) {
    DependencyAnalyzer analyzer("Foo.h");

        // Get includes multiple times
        auto includes1 = analyzer.getRequiredIncludes();
        auto includes2 = analyzer.getRequiredIncludes();

        // Should be identical (no duplicates added)
        ASSERT_TRUE(includes1.size() == includes2.size()) << "Include list should be consistent";
        ASSERT_TRUE(includes1[0] == includes2[0]) << "Includes should be identical";
}

TEST(DependencyAnalyzer, ExtensibleForRuntimeDeps) {
    DependencyAnalyzer analyzer("Example.h");

        // Verify we have the method to add runtime deps (future-proofing)
        // For now, just verify structure is extensible
        auto includes = analyzer.getRequiredIncludes();

        ASSERT_TRUE(includes.size() >= 1) << "Should have at least own header";

        // Future: Test addRuntimeDependency() when implemented
        // analyzer.addRuntimeDependency("runtime.h");
        // includes = analyzer.getRequiredIncludes();
        // ASSERT_TRUE(includes.size() == 2) << "Should have 2 includes";
}
