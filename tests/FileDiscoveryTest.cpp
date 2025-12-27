// Unit Tests for Recursive File Discovery Feature
// Tests discoverSourceFiles() function for auto-discovering .cpp files

#include <gtest/gtest.h>
#include <filesystem>
#include <fstream>
#include <vector>
#include <string>
#include <algorithm>

namespace fs = std::filesystem;

// Forward declarations of functions from main.cpp
// Note: In production, these would be moved to a header file
extern std::vector<std::string> discoverSourceFiles(const std::string& sourceDir);

class FileDiscoveryTest : public ::testing::Test {
protected:
    fs::path testDir;

    void SetUp() override {
        // Create unique test directory in temp
        testDir = fs::temp_directory_path() / ("cpptoc-discovery-test-" +
                  std::to_string(std::chrono::system_clock::now().time_since_epoch().count()));
        fs::create_directories(testDir);
    }

    void TearDown() override {
        // Clean up test directory
        if (fs::exists(testDir)) {
            fs::remove_all(testDir);
        }
    }

    // Helper to create a test file
    void createFile(const fs::path& path, const std::string& content = "// test file\n") {
        fs::create_directories(path.parent_path());
        std::ofstream file(path);
        file << content;
        file.close();
    }

    // Helper to count files with specific extension in results
    size_t countFilesWithExtension(const std::vector<std::string>& files, const std::string& ext) {
        return std::count_if(files.begin(), files.end(), [&ext](const std::string& file) {
            return fs::path(file).extension() == ext;
        });
    }
};

// Test 1: Basic discovery of .cpp files
TEST_F(FileDiscoveryTest, DiscoversCppFiles) {
    createFile(testDir / "main.cpp");
    createFile(testDir / "module.cpp");

    auto files = discoverSourceFiles(testDir.string());
    EXPECT_EQ(files.size(), 2) << "Should discover 2 .cpp files";
}

// Test 2: Support for multiple C++ extensions
TEST_F(FileDiscoveryTest, SupportsMultipleExtensions) {
    createFile(testDir / "a.cpp");
    createFile(testDir / "b.cxx");
    createFile(testDir / "c.cc");

    auto files = discoverSourceFiles(testDir.string());
    EXPECT_EQ(files.size(), 3) << "Should discover .cpp, .cxx, and .cc files";
    EXPECT_EQ(countFilesWithExtension(files, ".cpp"), 1);
    EXPECT_EQ(countFilesWithExtension(files, ".cxx"), 1);
    EXPECT_EQ(countFilesWithExtension(files, ".cc"), 1);
}

// Test 3: Recursive directory traversal
TEST_F(FileDiscoveryTest, RecursiveTraversal) {
    createFile(testDir / "main.cpp");
    createFile(testDir / "src/module.cpp");
    createFile(testDir / "src/subdir/helper.cxx");
    createFile(testDir / "include/nested/deep/file.cc");

    auto files = discoverSourceFiles(testDir.string());
    EXPECT_EQ(files.size(), 4) << "Should discover files in nested directories";
}

// Test 4: Exclude .git directory
TEST_F(FileDiscoveryTest, ExcludesGitDirectory) {
    createFile(testDir / "main.cpp");
    createFile(testDir / ".git/hooks.cpp");
    createFile(testDir / ".git/objects/abc123.cpp");

    auto files = discoverSourceFiles(testDir.string());
    EXPECT_EQ(files.size(), 1) << ".git directory should be excluded";

    // Verify the discovered file is main.cpp
    ASSERT_EQ(files.size(), 1);
    EXPECT_TRUE(files[0].find("main.cpp") != std::string::npos);
}

// Test 5: Exclude build directories
TEST_F(FileDiscoveryTest, ExcludesBuildDirectories) {
    createFile(testDir / "main.cpp");
    createFile(testDir / "build/generated.cpp");
    createFile(testDir / "build-debug/test.cpp");
    createFile(testDir / "build-release/release.cpp");
    createFile(testDir / "cmake-build-debug/cmake.cpp");

    auto files = discoverSourceFiles(testDir.string());
    EXPECT_EQ(files.size(), 1) << "All build directories should be excluded";
    EXPECT_TRUE(files[0].find("main.cpp") != std::string::npos);
}

// Test 6: Exclude hidden directories
TEST_F(FileDiscoveryTest, ExcludesHiddenDirectories) {
    createFile(testDir / "main.cpp");
    createFile(testDir / ".hidden/file.cpp");
    createFile(testDir / ".cache/cache.cpp");
    createFile(testDir / ".vscode/settings.cpp");

    auto files = discoverSourceFiles(testDir.string());
    EXPECT_EQ(files.size(), 1) << "Hidden directories should be excluded";
}

// Test 7: Exclude node_modules and vendor
TEST_F(FileDiscoveryTest, ExcludesNodeModulesAndVendor) {
    createFile(testDir / "main.cpp");
    createFile(testDir / "node_modules/package/index.cpp");
    createFile(testDir / "vendor/library/lib.cpp");

    auto files = discoverSourceFiles(testDir.string());
    EXPECT_EQ(files.size(), 1) << "node_modules and vendor should be excluded";
}

// Test 8: Handle empty directory
TEST_F(FileDiscoveryTest, HandlesEmptyDirectory) {
    auto files = discoverSourceFiles(testDir.string());
    EXPECT_TRUE(files.empty()) << "Empty directory should return empty vector";
}

// Test 9: Handle non-existent directory
TEST_F(FileDiscoveryTest, HandlesNonExistentDirectory) {
    auto files = discoverSourceFiles("/nonexistent/path/to/nowhere");
    EXPECT_TRUE(files.empty()) << "Non-existent directory should return empty vector";
}

// Test 10: Return absolute paths
TEST_F(FileDiscoveryTest, ReturnsAbsolutePaths) {
    createFile(testDir / "main.cpp");

    auto files = discoverSourceFiles(testDir.string());
    ASSERT_EQ(files.size(), 1);

    fs::path filePath(files[0]);
    EXPECT_TRUE(filePath.is_absolute()) << "Returned paths should be absolute";
}

// Test 11: Ignore non-C++ files
TEST_F(FileDiscoveryTest, IgnoresNonCppFiles) {
    createFile(testDir / "main.cpp");
    createFile(testDir / "header.h");
    createFile(testDir / "readme.txt");
    createFile(testDir / "build.sh");
    createFile(testDir / "data.json");
    createFile(testDir / "Makefile");

    auto files = discoverSourceFiles(testDir.string());
    EXPECT_EQ(files.size(), 1) << "Only .cpp files should be discovered";
}

// Test 12: Exclude .svn and .hg directories
TEST_F(FileDiscoveryTest, ExcludesSvnAndHgDirectories) {
    createFile(testDir / "main.cpp");
    createFile(testDir / ".svn/entries.cpp");
    createFile(testDir / ".hg/store.cpp");

    auto files = discoverSourceFiles(testDir.string());
    EXPECT_EQ(files.size(), 1) << ".svn and .hg directories should be excluded";
}

// Test 13: Multiple files in same directory
TEST_F(FileDiscoveryTest, MultipleFilesInSameDirectory) {
    createFile(testDir / "file1.cpp");
    createFile(testDir / "file2.cpp");
    createFile(testDir / "file3.cpp");
    createFile(testDir / "file4.cxx");
    createFile(testDir / "file5.cc");

    auto files = discoverSourceFiles(testDir.string());
    EXPECT_EQ(files.size(), 5) << "Should discover all C++ files in directory";
}

// Test 14: Mixed valid and excluded directories
TEST_F(FileDiscoveryTest, MixedValidAndExcludedDirectories) {
    // Valid files
    createFile(testDir / "src/main.cpp");
    createFile(testDir / "lib/helper.cpp");

    // Excluded files
    createFile(testDir / "build/generated.cpp");
    createFile(testDir / ".git/hook.cpp");
    createFile(testDir / "node_modules/dep.cpp");

    auto files = discoverSourceFiles(testDir.string());
    EXPECT_EQ(files.size(), 2) << "Should only discover files from valid directories";
}

// Test 15: Deeply nested structure
TEST_F(FileDiscoveryTest, DeeplyNestedStructure) {
    createFile(testDir / "a/b/c/d/e/f/deep.cpp");
    createFile(testDir / "a/b/file.cpp");
    createFile(testDir / "a/file.cxx");

    auto files = discoverSourceFiles(testDir.string());
    EXPECT_EQ(files.size(), 3) << "Should handle deeply nested directories";
}

// Test 16: Directory that is a file (error case)
TEST_F(FileDiscoveryTest, HandlesFileAsDirectory) {
    auto filePath = testDir / "notadir.txt";
    createFile(filePath);

    auto files = discoverSourceFiles(filePath.string());
    EXPECT_TRUE(files.empty()) << "Should handle file path gracefully";
}
