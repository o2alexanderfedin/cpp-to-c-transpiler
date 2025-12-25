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

TEST(FileOutputManager, DefaultFilenamesFromInput) {
    FileOutputManager manager;
        manager.setInputFilename("Point.cpp");

        ASSERT_TRUE(manager.getHeaderFilename() == "Point.h") << "Expected 'Point.h' for header";
        ASSERT_TRUE(manager.getImplFilename() == "Point.c") << "Expected 'Point.c' for implementation";
}

TEST(FileOutputManager, CustomHeaderFilename) {
    FileOutputManager manager;
        manager.setInputFilename("MyClass.cpp");
        manager.setOutputHeader("custom.h");

        ASSERT_TRUE(manager.getHeaderFilename() == "custom.h") << "Expected custom header filename";
        ASSERT_TRUE(manager.getImplFilename() == "MyClass.c") << "Expected default impl filename";
}

TEST(FileOutputManager, CustomImplFilename) {
    FileOutputManager manager;
        manager.setInputFilename("Test.cpp");
        manager.setOutputImpl("custom.c");

        ASSERT_TRUE(manager.getHeaderFilename() == "Test.h") << "Expected default header filename";
        ASSERT_TRUE(manager.getImplFilename() == "custom.c") << "Expected custom impl filename";
}

TEST(FileOutputManager, WriteFilesSuccess) {
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

TEST(FileOutputManager, WriteFilesFailureInvalidPath) {
    FileOutputManager manager;
        manager.setInputFilename("Test.cpp");
        manager.setOutputHeader("/nonexistent/path/test.h");

        std::string content = "test";

        bool success = manager.writeFiles(content, content);

        // Should fail gracefully
        ASSERT_TRUE(!success) << "Expected writeFiles to fail for invalid path";
}

// Phase 34-04: Multi-file output API tests (TDD)

TEST(FileOutputManager, WritesMultipleOutputFilePairs) {
    // TDD RED PHASE: Write failing test for multi-file output
    //
    // Given: Multiple FileContent entries for Point.h, Point.cpp, main.cpp
    // When: writeMultiFileOutput() called
    // Then:
    //   - Point.h → Point_transpiled.h + Point_transpiled.c
    //   - Point.cpp → Point_transpiled.h + Point_transpiled.c (merged with Point.h)
    //   - main.cpp → main_transpiled.h + main_transpiled.c
    //   - Total: 2 .h files, 2 .c files (Point.h + Point.cpp merged)

    FileOutputManager manager;
    manager.setOutputDir("test_output/");

    std::vector<FileOutputManager::FileContent> files;

    // Point.h content
    FileOutputManager::FileContent pointHeader;
    pointHeader.originFile = "Point.h";
    pointHeader.headerContent = "// Point class declaration\ntypedef struct Point_t Point_t;\n";
    pointHeader.implContent = "";  // Headers typically don't have impl content
    files.push_back(pointHeader);

    // Point.cpp content
    FileOutputManager::FileContent pointImpl;
    pointImpl.originFile = "Point.cpp";
    pointImpl.headerContent = "";  // .cpp files don't add to header
    pointImpl.implContent = "#include \"Point_transpiled.h\"\n// Point implementation\n";
    files.push_back(pointImpl);

    // main.cpp content
    FileOutputManager::FileContent mainFile;
    mainFile.originFile = "main.cpp";
    mainFile.headerContent = "";  // main typically has no header content
    mainFile.implContent = "#include \"Point_transpiled.h\"\nint main() { return 0; }\n";
    files.push_back(mainFile);

    // Execute multi-file write
    bool success = manager.writeMultiFileOutput(files);

    // Verify success
    ASSERT_TRUE(success) << "Expected writeMultiFileOutput to succeed";

    // Verify Point files (merged from Point.h + Point.cpp)
    ASSERT_TRUE(fileExists("test_output/Point_transpiled.h"))
        << "Expected Point_transpiled.h to exist";
    ASSERT_TRUE(fileExists("test_output/Point_transpiled.c"))
        << "Expected Point_transpiled.c to exist";

    // Verify main files
    ASSERT_TRUE(fileExists("test_output/main_transpiled.h"))
        << "Expected main_transpiled.h to exist";
    ASSERT_TRUE(fileExists("test_output/main_transpiled.c"))
        << "Expected main_transpiled.c to exist";

    // Verify Point.h content is in Point_transpiled.h
    std::ifstream pointH("test_output/Point_transpiled.h");
    std::string pointHContent((std::istreambuf_iterator<char>(pointH)),
                               std::istreambuf_iterator<char>());
    ASSERT_NE(pointHContent.find("Point class declaration"), std::string::npos)
        << "Expected Point_transpiled.h to contain Point.h content";

    // Verify Point.cpp content is in Point_transpiled.c
    std::ifstream pointC("test_output/Point_transpiled.c");
    std::string pointCContent((std::istreambuf_iterator<char>(pointC)),
                               std::istreambuf_iterator<char>());
    ASSERT_NE(pointCContent.find("Point implementation"), std::string::npos)
        << "Expected Point_transpiled.c to contain Point.cpp content";

    // Cleanup
    std::remove("test_output/Point_transpiled.h");
    std::remove("test_output/Point_transpiled.c");
    std::remove("test_output/main_transpiled.h");
    std::remove("test_output/main_transpiled.c");
    std::remove("test_output");
}

TEST(FileOutputManager, CalculateOutputPathForFileWithoutSourceDir) {
    // Test calculateOutputPathForFile without source directory preservation
    FileOutputManager manager;
    manager.setOutputDir("output/");

    // Point.h → output/Point_transpiled.h
    std::string pointHeader = manager.calculateOutputPathForFile("Point.h", true);
    ASSERT_EQ(pointHeader, "output/Point_transpiled.h")
        << "Expected Point.h → output/Point_transpiled.h";

    // Point.cpp → output/Point_transpiled.c
    std::string pointImpl = manager.calculateOutputPathForFile("Point.cpp", false);
    ASSERT_EQ(pointImpl, "output/Point_transpiled.c")
        << "Expected Point.cpp → output/Point_transpiled.c";

    // main.cpp → output/main_transpiled.c
    std::string mainImpl = manager.calculateOutputPathForFile("main.cpp", false);
    ASSERT_EQ(mainImpl, "output/main_transpiled.c")
        << "Expected main.cpp → output/main_transpiled.c";
}

TEST(FileOutputManager, CalculateOutputPathForFileWithSourceDir) {
    // Test calculateOutputPathForFile WITH source directory preservation
    FileOutputManager manager;
    manager.setOutputDir("build/");
    manager.setSourceDir("src/");

    // src/geometry/Point.h → build/geometry/Point_transpiled.h
    std::string pointHeader = manager.calculateOutputPathForFile("src/geometry/Point.h", true);
    ASSERT_EQ(pointHeader, "build/geometry/Point_transpiled.h")
        << "Expected structure preservation: src/geometry/Point.h → build/geometry/Point_transpiled.h";

    // src/geometry/Point.cpp → build/geometry/Point_transpiled.c
    std::string pointImpl = manager.calculateOutputPathForFile("src/geometry/Point.cpp", false);
    ASSERT_EQ(pointImpl, "build/geometry/Point_transpiled.c")
        << "Expected structure preservation: src/geometry/Point.cpp → build/geometry/Point_transpiled.c";
}
