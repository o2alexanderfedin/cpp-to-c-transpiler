// TDD Tests for FileOutputManager - Epic #19 Implementation
// Story #141: File Output System

#include "FileOutputManager.h"
#include <iostream>
#include <fstream>
#include <cstdio>  // For remove()

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Helper to check if file exists
bool fileExists(const std::string& filename) {
    std::ifstream f(filename);
    return f.good();
}

// Test 1: Default filenames from input
void test_DefaultFilenames() {
    TEST_START("DefaultFilenames");

    FileOutputManager manager;
    manager.setInputFilename("Point.cpp");

    ASSERT(manager.getHeaderFilename() == "Point.h",
           "Expected 'Point.h' for header");
    ASSERT(manager.getImplFilename() == "Point.c",
           "Expected 'Point.c' for implementation");

    TEST_PASS("DefaultFilenames");
}

// Test 2: Custom header filename
void test_CustomHeaderFilename() {
    TEST_START("CustomHeaderFilename");

    FileOutputManager manager;
    manager.setInputFilename("MyClass.cpp");
    manager.setOutputHeader("custom.h");

    ASSERT(manager.getHeaderFilename() == "custom.h",
           "Expected custom header filename");
    ASSERT(manager.getImplFilename() == "MyClass.c",
           "Expected default impl filename");

    TEST_PASS("CustomHeaderFilename");
}

// Test 3: Custom impl filename
void test_CustomImplFilename() {
    TEST_START("CustomImplFilename");

    FileOutputManager manager;
    manager.setInputFilename("Test.cpp");
    manager.setOutputImpl("custom.c");

    ASSERT(manager.getHeaderFilename() == "Test.h",
           "Expected default header filename");
    ASSERT(manager.getImplFilename() == "custom.c",
           "Expected custom impl filename");

    TEST_PASS("CustomImplFilename");
}

// Test 4: Write to files
void test_WriteToFiles() {
    TEST_START("WriteToFiles");

    FileOutputManager manager;
    manager.setInputFilename("TestWrite.cpp");

    std::string headerContent = "#ifndef TEST_H\n#define TEST_H\n#endif\n";
    std::string implContent = "#include \"TestWrite.h\"\n";

    bool success = manager.writeFiles(headerContent, implContent);

    ASSERT(success, "Expected writeFiles to succeed");
    ASSERT(fileExists("TestWrite.h"), "Expected TestWrite.h to exist");
    ASSERT(fileExists("TestWrite.c"), "Expected TestWrite.c to exist");

    // Cleanup
    std::remove("TestWrite.h");
    std::remove("TestWrite.c");

    TEST_PASS("WriteToFiles");
}

// Test 5: Error handling - invalid path
void test_ErrorHandlingInvalidPath() {
    TEST_START("ErrorHandlingInvalidPath");

    FileOutputManager manager;
    manager.setInputFilename("Test.cpp");
    manager.setOutputHeader("/nonexistent/path/test.h");

    std::string content = "test";

    bool success = manager.writeFiles(content, content);

    // Should fail gracefully
    ASSERT(!success, "Expected writeFiles to fail for invalid path");

    TEST_PASS("ErrorHandlingInvalidPath");
}

int main() {
    std::cout << "\n=== FileOutputManager Tests (Story #141) ===\n\n";

    // Run all tests
    test_DefaultFilenames();
    test_CustomHeaderFilename();
    test_CustomImplFilename();
    test_WriteToFiles();
    test_ErrorHandlingInvalidPath();

    // Summary
    std::cout << "\n=== Test Summary ===\n";
    std::cout << "Passed: " << tests_passed << "\n";
    std::cout << "Failed: " << tests_failed << "\n";

    return tests_failed > 0 ? 1 : 0;
}
