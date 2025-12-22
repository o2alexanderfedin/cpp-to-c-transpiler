// TDD Tests for FileOutputManager - Epic #19 Implementation
// Story #141: File Output System
// Simple test counter

#include <gtest/gtest.h>
#include "FileOutputManager.h"
#include <fstream>
#include <cstdio>  // For remove()


// Helper to check if file exists
bool fileExists(const std::string& filename) {
    std::ifstream f(filename);
    return f.good();
}

// Test 1: Default filenames from input

TEST(TEST, FileOutputManager) {
    FileOutputManager manager;
        manager.setInputFilename("Point.cpp");

        ASSERT_TRUE(manager.getHeaderFilename() == "Point.h") << "Expected 'Point.h' for header";
        ASSERT_TRUE(manager.getImplFilename() == "Point.c") << "Expected 'Point.c' for implementation";
}

TEST(TEST, FileOutputManager) {
    FileOutputManager manager;
        manager.setInputFilename("MyClass.cpp");
        manager.setOutputHeader("custom.h");

        ASSERT_TRUE(manager.getHeaderFilename() == "custom.h") << "Expected custom header filename";
        ASSERT_TRUE(manager.getImplFilename() == "MyClass.c") << "Expected default impl filename";
}

TEST(TEST, FileOutputManager) {
    FileOutputManager manager;
        manager.setInputFilename("Test.cpp");
        manager.setOutputImpl("custom.c");

        ASSERT_TRUE(manager.getHeaderFilename() == "Test.h") << "Expected default header filename";
        ASSERT_TRUE(manager.getImplFilename() == "custom.c") << "Expected custom impl filename";
}

TEST(TEST, FileOutputManager) {
    FileOutputManager manager;
        manager.setInputFilename("TestWrite.cpp");

        std::string headerContent = "#ifndef TEST_H\n#define TEST_H\n#endif\n";
        std::string implContent = "#include \"TestWrite.h\"\n";

        bool success = manager.writeFiles(headerContent, implContent);

        ASSERT_TRUE(success) << "Expected writeFiles to succeed";
        ASSERT_TRUE(fileExists("TestWrite.h")) << "Expected TestWrite.h to exist";
        ASSERT_TRUE(fileExists("TestWrite.c")) << "Expected TestWrite.c to exist";

        // Cleanup
        std::remove("TestWrite.h");
        std::remove("TestWrite.c");
}

TEST(TEST, FileOutputManager) {
    FileOutputManager manager;
        manager.setInputFilename("Test.cpp");
        manager.setOutputHeader("/nonexistent/path/test.h");

        std::string content = "test";

        bool success = manager.writeFiles(content, content);

        // Should fail gracefully
        ASSERT_TRUE(!success) << "Expected writeFiles to fail for invalid path";
}
