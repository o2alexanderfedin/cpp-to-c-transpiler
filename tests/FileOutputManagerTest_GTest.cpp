// tests/FileOutputManagerTest_GTest.cpp
// Migrated from FileOutputManagerTest.cpp to Google Test framework
// Story #141: File Output System

#include <gtest/gtest.h>
#include "../include/FileOutputManager.h"
#include <fstream>
#include <cstdio>

// Test fixture for FileOutputManager tests
class FileOutputManagerTestFixture : public ::testing::Test {
protected:
    // Helper to check if file exists
    bool fileExists(const std::string& filename) {
        std::ifstream f(filename);
        return f.good();
    }

    // Cleanup files created during tests
    void TearDown() override {
        std::remove("TestWrite.h");
        std::remove("TestWrite.c");
    }
};

// Test 1: Default filenames from input
TEST_F(FileOutputManagerTestFixture, DefaultFilenames) {
    FileOutputManager manager;
    manager.setInputFilename("Point.cpp");

    ASSERT_EQ(manager.getHeaderFilename(), "Point.h")
           << "Expected 'Point.h' for header";
    ASSERT_EQ(manager.getImplFilename(), "Point.c")
           << "Expected 'Point.c' for implementation";
}

// Test 2: Custom header filename
TEST_F(FileOutputManagerTestFixture, CustomHeaderFilename) {
    FileOutputManager manager;
    manager.setInputFilename("MyClass.cpp");
    manager.setOutputHeader("custom.h");

    ASSERT_EQ(manager.getHeaderFilename(), "custom.h")
           << "Expected custom header filename";
    ASSERT_EQ(manager.getImplFilename(), "MyClass.c")
           << "Expected default impl filename";
}

// Test 3: Custom impl filename
TEST_F(FileOutputManagerTestFixture, CustomImplFilename) {
    FileOutputManager manager;
    manager.setInputFilename("Test.cpp");
    manager.setOutputImpl("custom.c");

    ASSERT_EQ(manager.getHeaderFilename(), "Test.h")
           << "Expected default header filename";
    ASSERT_EQ(manager.getImplFilename(), "custom.c")
           << "Expected custom impl filename";
}

// Test 4: Write to files
TEST_F(FileOutputManagerTestFixture, WriteToFiles) {
    FileOutputManager manager;
    manager.setInputFilename("TestWrite.cpp");

    std::string headerContent = "#ifndef TEST_H\n#define TEST_H\n#endif\n";
    std::string implContent = "#include \"TestWrite.h\"\n";

    bool success = manager.writeFiles(headerContent, implContent);

    ASSERT_TRUE(success) << "Expected writeFiles to succeed";
    ASSERT_TRUE(fileExists("TestWrite.h")) << "Expected TestWrite.h to exist";
    ASSERT_TRUE(fileExists("TestWrite.c")) << "Expected TestWrite.c to exist";
}

// Test 5: Error handling - invalid path
TEST_F(FileOutputManagerTestFixture, ErrorHandlingInvalidPath) {
    FileOutputManager manager;
    manager.setInputFilename("Test.cpp");
    manager.setOutputHeader("/nonexistent/path/test.h");

    std::string content = "test";

    bool success = manager.writeFiles(content, content);

    // Should fail gracefully
    ASSERT_FALSE(success) << "Expected writeFiles to fail for invalid path";
}
