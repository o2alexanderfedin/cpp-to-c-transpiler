// TDD Tests for DependencyAnalyzer - Epic #19 Implementation
// Story #140: Dependency Tracking

#include "DependencyAnalyzer.h"
#include <iostream>
#include <vector>

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Test 1: Simple case → includes own .h only
void test_IncludesOwnHeaderOnly() {
    TEST_START("IncludesOwnHeaderOnly");

    DependencyAnalyzer analyzer("Point.h");

    auto includes = analyzer.getRequiredIncludes();

    // Should include own header
    ASSERT(includes.size() == 1,
           "Expected 1 include (own header)");
    ASSERT(includes[0] == "Point.h",
           "Expected 'Point.h' in includes");

    TEST_PASS("IncludesOwnHeaderOnly");
}

// Test 2: Include order - own header should be first
void test_IncludeOrderOwnHeaderFirst() {
    TEST_START("IncludeOrderOwnHeaderFirst");

    DependencyAnalyzer analyzer("MyClass.h");

    // Future: add runtime library dependencies
    // analyzer.addRuntimeDependency("exceptions.h");

    auto includes = analyzer.getRequiredIncludes();

    // Own header should always be first
    ASSERT(includes.size() >= 1,
           "Expected at least own header");
    ASSERT(includes[0] == "MyClass.h",
           "Expected own header 'MyClass.h' to be first");

    TEST_PASS("IncludeOrderOwnHeaderFirst");
}

// Test 3: Generate #include directives
void test_GenerateIncludeDirectives() {
    TEST_START("GenerateIncludeDirectives");

    DependencyAnalyzer analyzer("Test.h");

    std::string includeDirectives = analyzer.emitIncludes();

    // Should contain #include "Test.h"
    ASSERT(includeDirectives.find("#include \"Test.h\"") != std::string::npos,
           "Expected '#include \"Test.h\"' in output");

    TEST_PASS("GenerateIncludeDirectives");
}

// Test 4: No duplicate includes
void test_NoDuplicateIncludes() {
    TEST_START("NoDuplicateIncludes");

    DependencyAnalyzer analyzer("Foo.h");

    // Get includes multiple times
    auto includes1 = analyzer.getRequiredIncludes();
    auto includes2 = analyzer.getRequiredIncludes();

    // Should be identical (no duplicates added)
    ASSERT(includes1.size() == includes2.size(),
           "Include list should be consistent");
    ASSERT(includes1[0] == includes2[0],
           "Includes should be identical");

    TEST_PASS("NoDuplicateIncludes");
}

// Test 5: Extensibility for future runtime dependencies
void test_ExtensibleForRuntimeDeps() {
    TEST_START("ExtensibleForRuntimeDeps");

    DependencyAnalyzer analyzer("Example.h");

    // Verify we have the method to add runtime deps (future-proofing)
    // For now, just verify structure is extensible
    auto includes = analyzer.getRequiredIncludes();

    ASSERT(includes.size() >= 1,
           "Should have at least own header");

    // Future: Test addRuntimeDependency() when implemented
    // analyzer.addRuntimeDependency("runtime.h");
    // includes = analyzer.getRequiredIncludes();
    // ASSERT(includes.size() == 2, "Should have 2 includes");

    TEST_PASS("ExtensibleForRuntimeDeps");
}

int main() {
    std::cout << "\n=== DependencyAnalyzer Tests (Story #140) ===\n\n";

    // Run all tests
    test_IncludesOwnHeaderOnly();
    test_IncludeOrderOwnHeaderFirst();
    test_GenerateIncludeDirectives();
    test_NoDuplicateIncludes();
    test_ExtensibleForRuntimeDeps();

    // Summary
    std::cout << "\n=== Test Summary ===\n";
    std::cout << "Passed: " << tests_passed << "\n";
    std::cout << "Failed: " << tests_failed << "\n";

    return tests_failed > 0 ? 1 : 0;
}
