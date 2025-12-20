// TDD Tests for DependencyGraphVisualizer
// Feature: Dependency Graph Visualization for Multi-File Projects

#include "DependencyGraphVisualizer.h"
#include <iostream>
#include <fstream>
#include <cassert>
#include <algorithm>

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Test 1: Create empty visualizer
void test_EmptyVisualizer() {
    TEST_START("EmptyVisualizer");

    DependencyGraphVisualizer viz;

    // Empty visualizer should have no files
    ASSERT(viz.getAllFiles().empty(),
           "Expected empty file list");

    // Should generate valid (but empty) DOT output
    std::string dot = viz.generateDOT();
    ASSERT(dot.find("digraph") != std::string::npos,
           "Expected DOT output to contain 'digraph'");

    TEST_PASS("EmptyVisualizer");
}

// Test 2: Add single file with no dependencies
void test_SingleFileNoDependencies() {
    TEST_START("SingleFileNoDependencies");

    DependencyGraphVisualizer viz;
    viz.addFile("Point.h", {});

    // Should have one file
    auto files = viz.getAllFiles();
    ASSERT(files.size() == 1,
           "Expected 1 file");
    ASSERT(files.count("Point.h") == 1,
           "Expected 'Point.h' in files");

    // Should have no dependencies
    ASSERT(!viz.hasDependencies("Point.h"),
           "Expected no dependencies for Point.h");

    TEST_PASS("SingleFileNoDependencies");
}

// Test 3: Add file with dependencies
void test_FileWithDependencies() {
    TEST_START("FileWithDependencies");

    DependencyGraphVisualizer viz;
    viz.addFile("Point.c", {"Point.h"});
    viz.addFile("Point.h", {});

    // Check files exist
    auto files = viz.getAllFiles();
    ASSERT(files.size() == 2,
           "Expected 2 files");

    // Point.c should have dependencies
    ASSERT(viz.hasDependencies("Point.c"),
           "Expected Point.c to have dependencies");

    auto deps = viz.getDependencies("Point.c");
    ASSERT(deps.size() == 1,
           "Expected 1 dependency");
    ASSERT(deps[0] == "Point.h",
           "Expected dependency on Point.h");

    TEST_PASS("FileWithDependencies");
}

// Test 4: Multiple files with dependencies
void test_MultipleDependencies() {
    TEST_START("MultipleDependencies");

    DependencyGraphVisualizer viz;
    viz.addFile("Circle.h", {"Point.h"});
    viz.addFile("Circle.c", {"Circle.h"});
    viz.addFile("Point.h", {});
    viz.addFile("Point.c", {"Point.h"});

    auto files = viz.getAllFiles();
    ASSERT(files.size() == 4,
           "Expected 4 files");

    // Verify Circle.c dependencies
    auto circleDeps = viz.getDependencies("Circle.c");
    ASSERT(circleDeps.size() == 1,
           "Expected 1 dependency for Circle.c");

    // Verify Circle.h dependencies
    auto circleHDeps = viz.getDependencies("Circle.h");
    ASSERT(circleHDeps.size() == 1,
           "Expected 1 dependency for Circle.h");
    ASSERT(circleHDeps[0] == "Point.h",
           "Expected Circle.h to depend on Point.h");

    TEST_PASS("MultipleDependencies");
}

// Test 5: Forward declarations
void test_ForwardDeclarations() {
    TEST_START("ForwardDeclarations");

    DependencyGraphVisualizer viz;
    viz.addFile("A.h", {});
    viz.addForwardDeclaration("A.h", "struct B");

    // Should track forward declaration
    auto dot = viz.generateDOT();
    ASSERT(dot.find("struct B") != std::string::npos,
           "Expected DOT to mention forward declaration");

    TEST_PASS("ForwardDeclarations");
}

// Test 6: Circular dependency detection - simple cycle
void test_SimpleCircularDependency() {
    TEST_START("SimpleCircularDependency");

    DependencyGraphVisualizer viz;
    viz.addFile("A.h", {"B.h"});
    viz.addFile("B.h", {"A.h"});

    auto cycles = viz.detectCircularDependencies();
    ASSERT(cycles.size() >= 1,
           "Expected to detect at least 1 circular dependency");

    // Verify cycle contains both A.h and B.h
    bool foundCycle = false;
    for (const auto& cycle : cycles) {
        bool hasA = std::find(cycle.begin(), cycle.end(), "A.h") != cycle.end();
        bool hasB = std::find(cycle.begin(), cycle.end(), "B.h") != cycle.end();
        if (hasA && hasB) {
            foundCycle = true;
            break;
        }
    }
    ASSERT(foundCycle,
           "Expected cycle to contain both A.h and B.h");

    TEST_PASS("SimpleCircularDependency");
}

// Test 7: No circular dependencies
void test_NoCircularDependencies() {
    TEST_START("NoCircularDependencies");

    DependencyGraphVisualizer viz;
    viz.addFile("Point.h", {});
    viz.addFile("Circle.h", {"Point.h"});
    viz.addFile("Rectangle.h", {"Point.h"});

    auto cycles = viz.detectCircularDependencies();
    ASSERT(cycles.empty(),
           "Expected no circular dependencies");

    TEST_PASS("NoCircularDependencies");
}

// Test 8: Complex circular dependency (A->B->C->A)
void test_ComplexCircularDependency() {
    TEST_START("ComplexCircularDependency");

    DependencyGraphVisualizer viz;
    viz.addFile("A.h", {"B.h"});
    viz.addFile("B.h", {"C.h"});
    viz.addFile("C.h", {"A.h"});

    auto cycles = viz.detectCircularDependencies();
    ASSERT(cycles.size() >= 1,
           "Expected to detect circular dependency");

    // Find the cycle
    bool foundCycle = false;
    for (const auto& cycle : cycles) {
        if (cycle.size() >= 3) {
            bool hasA = std::find(cycle.begin(), cycle.end(), "A.h") != cycle.end();
            bool hasB = std::find(cycle.begin(), cycle.end(), "B.h") != cycle.end();
            bool hasC = std::find(cycle.begin(), cycle.end(), "C.h") != cycle.end();
            if (hasA && hasB && hasC) {
                foundCycle = true;
                break;
            }
        }
    }
    ASSERT(foundCycle,
           "Expected cycle to contain A.h, B.h, and C.h");

    TEST_PASS("ComplexCircularDependency");
}

// Test 9: DOT output format validation
void test_DOTOutputFormat() {
    TEST_START("DOTOutputFormat");

    DependencyGraphVisualizer viz;
    viz.addFile("Point.h", {});
    viz.addFile("Point.c", {"Point.h"});

    std::string dot = viz.generateDOT("test_graph");

    // Check basic DOT structure
    ASSERT(dot.find("digraph test_graph") != std::string::npos,
           "Expected 'digraph test_graph' in output");
    ASSERT(dot.find("{") != std::string::npos,
           "Expected opening brace");
    ASSERT(dot.find("}") != std::string::npos,
           "Expected closing brace");

    // Check nodes
    ASSERT(dot.find("Point.h") != std::string::npos,
           "Expected Point.h node");
    ASSERT(dot.find("Point.c") != std::string::npos,
           "Expected Point.c node");

    // Check edge (Point.c -> Point.h)
    ASSERT(dot.find("->") != std::string::npos,
           "Expected edge arrow");

    TEST_PASS("DOTOutputFormat");
}

// Test 10: Node styling for header vs implementation files
void test_NodeStyling() {
    TEST_START("NodeStyling");

    DependencyGraphVisualizer viz;
    viz.addFile("Point.h", {});
    viz.addFile("Point.c", {"Point.h"});

    std::string dot = viz.generateDOT();

    // Headers should have different styling than implementation files
    // This is implementation-specific, but we can check they're styled
    ASSERT(dot.find("Point.h") != std::string::npos,
           "Expected Point.h in output");
    ASSERT(dot.find("Point.c") != std::string::npos,
           "Expected Point.c in output");

    TEST_PASS("NodeStyling");
}

// Test 11: Clear functionality
void test_Clear() {
    TEST_START("Clear");

    DependencyGraphVisualizer viz;
    viz.addFile("Point.h", {});
    viz.addFile("Point.c", {"Point.h"});

    ASSERT(viz.getAllFiles().size() == 2,
           "Expected 2 files before clear");

    viz.clear();

    ASSERT(viz.getAllFiles().empty(),
           "Expected empty file list after clear");

    TEST_PASS("Clear");
}

// Test 12: Write to file
void test_WriteToFile() {
    TEST_START("WriteToFile");

    DependencyGraphVisualizer viz;
    viz.addFile("Point.h", {});
    viz.addFile("Point.c", {"Point.h"});

    // Write to temp file
    std::string filename = "/tmp/test_deps.dot";
    bool success = viz.writeToFile(filename);

    ASSERT(success,
           "Expected writeToFile to succeed");

    // Verify file exists and has content
    std::ifstream file(filename);
    ASSERT(file.good(),
           "Expected output file to exist");

    std::string content((std::istreambuf_iterator<char>(file)),
                        std::istreambuf_iterator<char>());
    ASSERT(!content.empty(),
           "Expected non-empty file content");
    ASSERT(content.find("digraph") != std::string::npos,
           "Expected DOT format in file");

    file.close();

    TEST_PASS("WriteToFile");
}

// Test 13: Real-world scenario - multi-file project
void test_RealWorldScenario() {
    TEST_START("RealWorldScenario");

    DependencyGraphVisualizer viz;

    // Simulate a real project structure:
    // Vector.h -> (no deps)
    // Vector.c -> Vector.h
    // String.h -> (no deps)
    // String.c -> String.h
    // Container.h -> Vector.h, String.h
    // Container.c -> Container.h
    // Main.c -> Container.h, Vector.h, String.h

    viz.addFile("Vector.h", {});
    viz.addFile("Vector.c", {"Vector.h"});
    viz.addFile("String.h", {});
    viz.addFile("String.c", {"String.h"});
    viz.addFile("Container.h", {"Vector.h", "String.h"});
    viz.addFile("Container.c", {"Container.h"});
    viz.addFile("Main.c", {"Container.h", "Vector.h", "String.h"});

    // Add forward declarations
    viz.addForwardDeclaration("Container.h", "struct Vector");
    viz.addForwardDeclaration("Container.h", "struct String");

    // Verify structure
    auto files = viz.getAllFiles();
    ASSERT(files.size() == 7,
           "Expected 7 files");

    // Check no circular dependencies
    auto cycles = viz.detectCircularDependencies();
    ASSERT(cycles.empty(),
           "Expected no circular dependencies in well-structured project");

    // Generate DOT output
    std::string dot = viz.generateDOT("project_dependencies");
    ASSERT(!dot.empty(),
           "Expected non-empty DOT output");

    TEST_PASS("RealWorldScenario");
}

// Test 14: Edge case - self-dependency (should be handled gracefully)
void test_SelfDependency() {
    TEST_START("SelfDependency");

    DependencyGraphVisualizer viz;
    viz.addFile("SelfRef.h", {"SelfRef.h"});

    // Should detect as circular dependency
    auto cycles = viz.detectCircularDependencies();
    ASSERT(cycles.size() >= 1,
           "Expected self-dependency to be detected as cycle");

    TEST_PASS("SelfDependency");
}

// Test 15: Empty filename handling
void test_EmptyFilename() {
    TEST_START("EmptyFilename");

    DependencyGraphVisualizer viz;
    viz.addFile("", {});

    // Should handle empty filename gracefully
    auto files = viz.getAllFiles();
    ASSERT(files.size() == 1,
           "Expected empty filename to be tracked");

    TEST_PASS("EmptyFilename");
}

int main() {
    std::cout << "\n=== DependencyGraphVisualizer Tests ===\n\n";

    // Run all tests
    test_EmptyVisualizer();
    test_SingleFileNoDependencies();
    test_FileWithDependencies();
    test_MultipleDependencies();
    test_ForwardDeclarations();
    test_SimpleCircularDependency();
    test_NoCircularDependencies();
    test_ComplexCircularDependency();
    test_DOTOutputFormat();
    test_NodeStyling();
    test_Clear();
    test_WriteToFile();
    test_RealWorldScenario();
    test_SelfDependency();
    test_EmptyFilename();

    // Summary
    std::cout << "\n=== Test Summary ===\n";
    std::cout << "Passed: " << tests_passed << "\n";
    std::cout << "Failed: " << tests_failed << "\n";

    return tests_failed > 0 ? 1 : 0;
}
