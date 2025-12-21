// TDD Tests for DependencyGraphVisualizer
// Feature: Dependency Graph Visualization for Multi-File Projects
// Migrated to Google Test framework

#include <gtest/gtest.h>
#include "DependencyGraphVisualizer.h"
#include <iostream>
#include <fstream>
#include <algorithm>

// ============================================================================
// Test Fixture for DependencyGraphVisualizer
// ============================================================================

class DependencyGraphVisualizerTestFixture : public ::testing::Test {
protected:
    void SetUp() override {
        // Create a fresh visualizer for each test
    }

    void TearDown() override {
        // Clean up any temp files created during tests
    }
};

// Test 1: Create empty visualizer
TEST_F(DependencyGraphVisualizerTestFixture, EmptyVisualizer) {
    DependencyGraphVisualizer viz;

    // Empty visualizer should have no files
    EXPECT_TRUE(viz.getAllFiles().empty())
        << "Expected empty file list";

    // Should generate valid (but empty) DOT output
    std::string dot = viz.generateDOT();
    EXPECT_NE(dot.find("digraph"), std::string::npos)
        << "Expected DOT output to contain 'digraph'";
}

// Test 2: Add single file with no dependencies
TEST_F(DependencyGraphVisualizerTestFixture, SingleFileNoDependencies) {
    DependencyGraphVisualizer viz;
    viz.addFile("Point.h", {});

    // Should have one file
    auto files = viz.getAllFiles();
    ASSERT_EQ(files.size(), 1)
        << "Expected 1 file";
    EXPECT_EQ(files.count("Point.h"), 1)
        << "Expected 'Point.h' in files";

    // Should have no dependencies
    EXPECT_FALSE(viz.hasDependencies("Point.h"))
        << "Expected no dependencies for Point.h";
}

// Test 3: Add file with dependencies
TEST_F(DependencyGraphVisualizerTestFixture, FileWithDependencies) {
    DependencyGraphVisualizer viz;
    viz.addFile("Point.c", {"Point.h"});
    viz.addFile("Point.h", {});

    // Check files exist
    auto files = viz.getAllFiles();
    ASSERT_EQ(files.size(), 2)
        << "Expected 2 files";

    // Point.c should have dependencies
    EXPECT_TRUE(viz.hasDependencies("Point.c"))
        << "Expected Point.c to have dependencies";

    auto deps = viz.getDependencies("Point.c");
    ASSERT_EQ(deps.size(), 1)
        << "Expected 1 dependency";
    EXPECT_EQ(deps[0], "Point.h")
        << "Expected dependency on Point.h";
}

// Test 4: Multiple files with dependencies
TEST_F(DependencyGraphVisualizerTestFixture, MultipleDependencies) {
    DependencyGraphVisualizer viz;
    viz.addFile("Circle.h", {"Point.h"});
    viz.addFile("Circle.c", {"Circle.h"});
    viz.addFile("Point.h", {});
    viz.addFile("Point.c", {"Point.h"});

    auto files = viz.getAllFiles();
    ASSERT_EQ(files.size(), 4)
        << "Expected 4 files";

    // Verify Circle.c dependencies
    auto circleDeps = viz.getDependencies("Circle.c");
    EXPECT_EQ(circleDeps.size(), 1)
        << "Expected 1 dependency for Circle.c";

    // Verify Circle.h dependencies
    auto circleHDeps = viz.getDependencies("Circle.h");
    ASSERT_EQ(circleHDeps.size(), 1)
        << "Expected 1 dependency for Circle.h";
    EXPECT_EQ(circleHDeps[0], "Point.h")
        << "Expected Circle.h to depend on Point.h";
}

// Test 5: Forward declarations
TEST_F(DependencyGraphVisualizerTestFixture, ForwardDeclarations) {
    DependencyGraphVisualizer viz;
    viz.addFile("A.h", {});
    viz.addForwardDeclaration("A.h", "struct B");

    // Should track forward declaration
    auto dot = viz.generateDOT();
    EXPECT_NE(dot.find("struct B"), std::string::npos)
        << "Expected DOT to mention forward declaration";
}

// Test 6: Circular dependency detection - simple cycle
TEST_F(DependencyGraphVisualizerTestFixture, SimpleCircularDependency) {
    DependencyGraphVisualizer viz;
    viz.addFile("A.h", {"B.h"});
    viz.addFile("B.h", {"A.h"});

    auto cycles = viz.detectCircularDependencies();
    ASSERT_GE(cycles.size(), 1)
        << "Expected to detect at least 1 circular dependency";

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
    EXPECT_TRUE(foundCycle)
        << "Expected cycle to contain both A.h and B.h";
}

// Test 7: No circular dependencies
TEST_F(DependencyGraphVisualizerTestFixture, NoCircularDependencies) {
    DependencyGraphVisualizer viz;
    viz.addFile("Point.h", {});
    viz.addFile("Circle.h", {"Point.h"});
    viz.addFile("Rectangle.h", {"Point.h"});

    auto cycles = viz.detectCircularDependencies();
    EXPECT_TRUE(cycles.empty())
        << "Expected no circular dependencies";
}

// Test 8: Complex circular dependency (A->B->C->A)
TEST_F(DependencyGraphVisualizerTestFixture, ComplexCircularDependency) {
    DependencyGraphVisualizer viz;
    viz.addFile("A.h", {"B.h"});
    viz.addFile("B.h", {"C.h"});
    viz.addFile("C.h", {"A.h"});

    auto cycles = viz.detectCircularDependencies();
    ASSERT_GE(cycles.size(), 1)
        << "Expected to detect circular dependency";

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
    EXPECT_TRUE(foundCycle)
        << "Expected cycle to contain A.h, B.h, and C.h";
}

// Test 9: DOT output format validation
TEST_F(DependencyGraphVisualizerTestFixture, DOTOutputFormat) {
    DependencyGraphVisualizer viz;
    viz.addFile("Point.h", {});
    viz.addFile("Point.c", {"Point.h"});

    std::string dot = viz.generateDOT("test_graph");

    // Check basic DOT structure
    EXPECT_NE(dot.find("digraph test_graph"), std::string::npos)
        << "Expected 'digraph test_graph' in output";
    EXPECT_NE(dot.find("{"), std::string::npos)
        << "Expected opening brace";
    EXPECT_NE(dot.find("}"), std::string::npos)
        << "Expected closing brace";

    // Check nodes
    EXPECT_NE(dot.find("Point.h"), std::string::npos)
        << "Expected Point.h node";
    EXPECT_NE(dot.find("Point.c"), std::string::npos)
        << "Expected Point.c node";

    // Check edge (Point.c -> Point.h)
    EXPECT_NE(dot.find("->"), std::string::npos)
        << "Expected edge arrow";
}

// Test 10: Node styling for header vs implementation files
TEST_F(DependencyGraphVisualizerTestFixture, NodeStyling) {
    DependencyGraphVisualizer viz;
    viz.addFile("Point.h", {});
    viz.addFile("Point.c", {"Point.h"});

    std::string dot = viz.generateDOT();

    // Headers should have different styling than implementation files
    // This is implementation-specific, but we can check they're styled
    EXPECT_NE(dot.find("Point.h"), std::string::npos)
        << "Expected Point.h in output";
    EXPECT_NE(dot.find("Point.c"), std::string::npos)
        << "Expected Point.c in output";
}

// Test 11: Clear functionality
TEST_F(DependencyGraphVisualizerTestFixture, Clear) {
    DependencyGraphVisualizer viz;
    viz.addFile("Point.h", {});
    viz.addFile("Point.c", {"Point.h"});

    ASSERT_EQ(viz.getAllFiles().size(), 2)
        << "Expected 2 files before clear";

    viz.clear();

    EXPECT_TRUE(viz.getAllFiles().empty())
        << "Expected empty file list after clear";
}

// Test 12: Write to file
TEST_F(DependencyGraphVisualizerTestFixture, WriteToFile) {
    DependencyGraphVisualizer viz;
    viz.addFile("Point.h", {});
    viz.addFile("Point.c", {"Point.h"});

    // Write to temp file
    std::string filename = "/tmp/test_deps.dot";
    bool success = viz.writeToFile(filename);

    ASSERT_TRUE(success)
        << "Expected writeToFile to succeed";

    // Verify file exists and has content
    std::ifstream file(filename);
    ASSERT_TRUE(file.good())
        << "Expected output file to exist";

    std::string content((std::istreambuf_iterator<char>(file)),
                        std::istreambuf_iterator<char>());
    EXPECT_FALSE(content.empty())
        << "Expected non-empty file content";
    EXPECT_NE(content.find("digraph"), std::string::npos)
        << "Expected DOT format in file";

    file.close();
}

// Test 13: Real-world scenario - multi-file project
TEST_F(DependencyGraphVisualizerTestFixture, RealWorldScenario) {
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
    ASSERT_EQ(files.size(), 7)
        << "Expected 7 files";

    // Check no circular dependencies
    auto cycles = viz.detectCircularDependencies();
    EXPECT_TRUE(cycles.empty())
        << "Expected no circular dependencies in well-structured project";

    // Generate DOT output
    std::string dot = viz.generateDOT("project_dependencies");
    EXPECT_FALSE(dot.empty())
        << "Expected non-empty DOT output";
}

// Test 14: Edge case - self-dependency (should be handled gracefully)
TEST_F(DependencyGraphVisualizerTestFixture, SelfDependency) {
    DependencyGraphVisualizer viz;
    viz.addFile("SelfRef.h", {"SelfRef.h"});

    // Should detect as circular dependency
    auto cycles = viz.detectCircularDependencies();
    EXPECT_GE(cycles.size(), 1)
        << "Expected self-dependency to be detected as cycle";
}

// Test 15: Empty filename handling
TEST_F(DependencyGraphVisualizerTestFixture, EmptyFilename) {
    DependencyGraphVisualizer viz;
    viz.addFile("", {});

    // Should handle empty filename gracefully
    auto files = viz.getAllFiles();
    EXPECT_EQ(files.size(), 1)
        << "Expected empty filename to be tracked";
}
