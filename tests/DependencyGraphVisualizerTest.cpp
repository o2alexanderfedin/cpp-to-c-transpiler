// TDD Tests for DependencyGraphVisualizer
// Feature: Dependency Graph Visualization for Multi-File Projects
// Simple test counter

#include <gtest/gtest.h>
#include "DependencyGraphVisualizer.h"
#include <fstream>
#include <cassert>
#include <algorithm>


TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;

        // Empty visualizer should have no files
        ASSERT_TRUE(viz.getAllFiles().empty()) << "Expected empty file list";

        // Should generate valid (but empty) DOT output
        std::string dot = viz.generateDOT();
        ASSERT_TRUE(dot.find("digraph") != std::string::npos) << "Expected DOT output to contain 'digraph'";
}

TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;
        viz.addFile("Point.h", {});

        // Should have one file
        auto files = viz.getAllFiles();
        ASSERT_TRUE(files.size() == 1) << "Expected 1 file";
        ASSERT_TRUE(files.count("Point.h") == 1) << "Expected 'Point.h' in files";

        // Should have no dependencies
        ASSERT_TRUE(!viz.hasDependencies("Point.h")) << "Expected no dependencies for Point.h";
}

TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;
        viz.addFile("Point.c", {"Point.h"});
        viz.addFile("Point.h", {});

        // Check files exist
        auto files = viz.getAllFiles();
        ASSERT_TRUE(files.size() == 2) << "Expected 2 files";

        // Point.c should have dependencies
        ASSERT_TRUE(viz.hasDependencies("Point.c")) << "Expected Point.c to have dependencies";

        auto deps = viz.getDependencies("Point.c");
        ASSERT_TRUE(deps.size() == 1) << "Expected 1 dependency";
        ASSERT_TRUE(deps[0] == "Point.h") << "Expected dependency on Point.h";
}

TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;
        viz.addFile("Circle.h", {"Point.h"});
        viz.addFile("Circle.c", {"Circle.h"});
        viz.addFile("Point.h", {});
        viz.addFile("Point.c", {"Point.h"});

        auto files = viz.getAllFiles();
        ASSERT_TRUE(files.size() == 4) << "Expected 4 files";

        // Verify Circle.c dependencies
        auto circleDeps = viz.getDependencies("Circle.c");
        ASSERT_TRUE(circleDeps.size() == 1) << "Expected 1 dependency for Circle.c";

        // Verify Circle.h dependencies
        auto circleHDeps = viz.getDependencies("Circle.h");
        ASSERT_TRUE(circleHDeps.size() == 1) << "Expected 1 dependency for Circle.h";
        ASSERT_TRUE(circleHDeps[0] == "Point.h") << "Expected Circle.h to depend on Point.h";
}

TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;
        viz.addFile("A.h", {});
        viz.addForwardDeclaration("A.h", "struct B");

        // Should track forward declaration
        auto dot = viz.generateDOT();
        ASSERT_TRUE(dot.find("struct B") != std::string::npos) << "Expected DOT to mention forward declaration";
}

TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;
        viz.addFile("A.h", {"B.h"});
        viz.addFile("B.h", {"A.h"});

        auto cycles = viz.detectCircularDependencies();
        ASSERT_TRUE(cycles.size() >= 1) << "Expected to detect at least 1 circular dependency";

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
        ASSERT_TRUE(foundCycle) << "Expected cycle to contain both A.h and B.h";
}

TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;
        viz.addFile("Point.h", {});
        viz.addFile("Circle.h", {"Point.h"});
        viz.addFile("Rectangle.h", {"Point.h"});

        auto cycles = viz.detectCircularDependencies();
        ASSERT_TRUE(cycles.empty()) << "Expected no circular dependencies";
}

TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;
        viz.addFile("Point.h", {});
        viz.addFile("Point.c", {"Point.h"});

        std::string dot = viz.generateDOT("test_graph");

        // Check basic DOT structure
        ASSERT_TRUE(dot.find("digraph test_graph") != std::string::npos) << "Expected 'digraph test_graph' in output";
        ASSERT_TRUE(dot.find("{") != std::string::npos) << "Expected opening brace";
        ASSERT_TRUE(dot.find("}") != std::string::npos) << "Expected closing brace";

        // Check nodes
        ASSERT_TRUE(dot.find("Point.h") != std::string::npos) << "Expected Point.h node";
        ASSERT_TRUE(dot.find("Point.c") != std::string::npos) << "Expected Point.c node";

        // Check edge (Point.c -> Point.h)
        ASSERT_TRUE(dot.find("->") != std::string::npos) << "Expected edge arrow";
}

TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;
        viz.addFile("Point.h", {});
        viz.addFile("Point.c", {"Point.h"});

        std::string dot = viz.generateDOT();

        // Headers should have different styling than implementation files
        // This is implementation-specific, but we can check they're styled
        ASSERT_TRUE(dot.find("Point.h") != std::string::npos) << "Expected Point.h in output";
        ASSERT_TRUE(dot.find("Point.c") != std::string::npos) << "Expected Point.c in output";
}

TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;
        viz.addFile("Point.h", {});
        viz.addFile("Point.c", {"Point.h"});

        ASSERT_TRUE(viz.getAllFiles().size() == 2) << "Expected 2 files before clear";

        viz.clear();

        ASSERT_TRUE(viz.getAllFiles().empty()) << "Expected empty file list after clear";
}

TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;
        viz.addFile("Point.h", {});
        viz.addFile("Point.c", {"Point.h"});

        // Write to temp file
        std::string filename = "/tmp/test_deps.dot";
        bool success = viz.writeToFile(filename);

        ASSERT_TRUE(success) << "Expected writeToFile to succeed";

        // Verify file exists and has content
        std::ifstream file(filename);
        ASSERT_TRUE(file.good()) << "Expected output file to exist";

        std::string content((std::istreambuf_iterator<char>(file)),
                            std::istreambuf_iterator<char>());
        ASSERT_TRUE(!content.empty()) << "Expected non-empty file content";
        ASSERT_TRUE(content.find("digraph") != std::string::npos) << "Expected DOT format in file";

        file.close();
}

TEST(TEST, DependencyGraphVisualizer) {
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
        ASSERT_TRUE(files.size() == 7) << "Expected 7 files";

        // Check no circular dependencies
        auto cycles = viz.detectCircularDependencies();
        ASSERT_TRUE(cycles.empty()) << "Expected no circular dependencies in well-structured project";

        // Generate DOT output
        std::string dot = viz.generateDOT("project_dependencies");
        ASSERT_TRUE(!dot.empty()) << "Expected non-empty DOT output";
}

TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;
        viz.addFile("SelfRef.h", {"SelfRef.h"});

        // Should detect as circular dependency
        auto cycles = viz.detectCircularDependencies();
        ASSERT_TRUE(cycles.size() >= 1) << "Expected self-dependency to be detected as cycle";
}

TEST(TEST, DependencyGraphVisualizer) {
    DependencyGraphVisualizer viz;
        viz.addFile("", {});

        // Should handle empty filename gracefully
        auto files = viz.getAllFiles();
        ASSERT_TRUE(files.size() == 1) << "Expected empty filename to be tracked";
}
