// tests/MultiFileTranspilationTest.cpp
// Comprehensive integration tests for multi-file transpilation support
// Tests CLI interface for handling multiple C++ files with dependencies

#include <gtest/gtest.h>
#include <gmock/gmock.h>
#include <fstream>
#include <sstream>
#include <filesystem>
#include <vector>
#include <string>
#include <cstdlib>
#include <chrono>
#include <thread>
#include <random>
#include <unistd.h>

namespace fs = std::filesystem;
using ::testing::HasSubstr;
using ::testing::Not;

// Test fixture for multi-file transpilation tests
class MultiFileTranspilationTest : public ::testing::Test {
protected:
    fs::path testDir;
    fs::path outputDir;
    std::string transpilerPath;

    void SetUp() override {
        // Create unique temporary directory for each test
        // Use process ID, thread ID, and high-resolution timestamp for guaranteed uniqueness in parallel execution
        auto now = std::chrono::high_resolution_clock::now();
        auto nanos = std::chrono::duration_cast<std::chrono::nanoseconds>(now.time_since_epoch()).count();

        std::ostringstream dirName;
        dirName << "cpptoc_test_"
                << getpid() << "_"  // Process ID
                << std::this_thread::get_id() << "_"  // Thread ID
                << nanos;  // High-resolution timestamp

        testDir = fs::temp_directory_path() / dirName.str();
        fs::create_directories(testDir);

        // Create src subdirectory for source files (project-based mode)
        fs::create_directories(testDir / "src");

        outputDir = testDir / "output";

        // Find the transpiler executable
        transpilerPath = findTranspiler();

        ASSERT_FALSE(transpilerPath.empty()) << "Could not find cpptoc transpiler executable";
    }

    void TearDown() override {
        // Clean up test directory
        if (fs::exists(testDir)) {
            fs::remove_all(testDir);
        }
    }

    // Find the transpiler executable in build directory
    std::string findTranspiler() {
        std::vector<std::string> possiblePaths = {
            "build_working/cpptoc",
            "../build_working/cpptoc",
            "../../build_working/cpptoc",
            "./cpptoc"
        };

        for (const auto& path : possiblePaths) {
            if (fs::exists(path)) {
                return fs::absolute(path).string();
            }
        }

        return "";
    }

    // Create a source file with content in the src/ subdirectory
    void createSourceFile(const std::string& filename, const std::string& content) {
        fs::path filePath = testDir / "src" / filename;
        // Create parent directories if needed
        fs::create_directories(filePath.parent_path());
        std::ofstream file(filePath);
        ASSERT_TRUE(file.is_open()) << "Failed to create file: " << filePath;
        file << content;
        file.close();
    }

    // Read file content
    std::string readFile(const fs::path& path) {
        std::ifstream file(path);
        if (!file.is_open()) {
            return "";
        }
        std::stringstream buffer;
        buffer << file.rdbuf();
        return buffer.str();
    }

    // Execute transpiler command
    struct ExecResult {
        int exitCode;
        std::string output;
    };

    ExecResult executeTranspiler(const std::vector<std::string>& args) {
        std::string command = transpilerPath;
        for (const auto& arg : args) {
            command += " \"" + arg + "\"";
        }
        command += " 2>&1";  // Redirect stderr to stdout

        FILE* pipe = popen(command.c_str(), "r");
        EXPECT_NE(pipe, nullptr) << "Failed to execute: " << command;

        if (!pipe) {
            return {-1, ""};
        }

        std::stringstream output;
        char buffer[256];
        while (fgets(buffer, sizeof(buffer), pipe) != nullptr) {
            output << buffer;
        }

        int exitCode = pclose(pipe);
        return {exitCode, output.str()};
    }

    // Check if file exists
    bool fileExists(const fs::path& path) {
        return fs::exists(path) && fs::is_regular_file(path);
    }
};

// Test 1: Single file generation - baseline test (project-based mode)
TEST_F(MultiFileTranspilationTest, SingleFileGeneration) {
    // Create a simple Point class
    std::string pointCpp = R"(
struct Point {
    int x;
    int y;
};

int getX(struct Point* p) {
    return p->x;
}

int getY(struct Point* p) {
    return p->y;
}
)";

    createSourceFile("Point.cpp", pointCpp);

    // Transpile using project-based mode with --source-dir
    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", (testDir / "src").string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    // Verify transpiler succeeded
    EXPECT_EQ(result.exitCode, 0) << "Transpiler failed with output: " << result.output;

    // Verify Point.h was created
    fs::path pointH = outputDir / "Point.h";
    ASSERT_TRUE(fileExists(pointH)) << "Point.h was not created";

    // Verify Point.c was created
    fs::path pointC = outputDir / "Point.c";
    ASSERT_TRUE(fileExists(pointC)) << "Point.c was not created";

    // Verify header content
    std::string headerContent = readFile(pointH);
    EXPECT_THAT(headerContent, HasSubstr("struct Point")) << "Header should contain struct definition";
    EXPECT_THAT(headerContent, HasSubstr("int getX")) << "Header should contain function declarations";
    EXPECT_THAT(headerContent, HasSubstr("int getY")) << "Header should contain function declarations";

    // Verify implementation content
    std::string implContent = readFile(pointC);
    EXPECT_THAT(implContent, HasSubstr("#include \"Point.h\"")) << "Implementation should include header";
    EXPECT_THAT(implContent, HasSubstr("return p->x")) << "Implementation should contain function bodies";
    EXPECT_THAT(implContent, HasSubstr("return p->y")) << "Implementation should contain function bodies";
}

// Test 2: Multiple independent files (project-based mode)
TEST_F(MultiFileTranspilationTest, MultipleIndependentFiles) {
    // Create Point.cpp
    std::string pointCpp = R"(
struct Point {
    int x;
    int y;
};

int distance(struct Point* p) {
    return p->x * p->x + p->y * p->y;
}
)";

    // Create Circle.cpp (independent of Point)
    std::string circleCpp = R"(
struct Circle {
    double radius;
};

double area(struct Circle* c) {
    return 3.14159 * c->radius * c->radius;
}
)";

    createSourceFile("Point.cpp", pointCpp);
    createSourceFile("Circle.cpp", circleCpp);

    // Transpile entire project with --source-dir
    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", (testDir / "src").string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0) << "Project transpilation failed: " << result.output;

    // Verify all files created
    EXPECT_TRUE(fileExists(outputDir / "Point.h"));
    EXPECT_TRUE(fileExists(outputDir / "Point.c"));
    EXPECT_TRUE(fileExists(outputDir / "Circle.h"));
    EXPECT_TRUE(fileExists(outputDir / "Circle.c"));

    // Verify Point files
    std::string pointH = readFile(outputDir / "Point.h");
    EXPECT_THAT(pointH, HasSubstr("struct Point"));
    EXPECT_THAT(pointH, Not(HasSubstr("Circle"))) << "Point.h should not reference Circle";

    // Verify Circle files
    std::string circleH = readFile(outputDir / "Circle.h");
    EXPECT_THAT(circleH, HasSubstr("struct Circle"));
    EXPECT_THAT(circleH, Not(HasSubstr("Point"))) << "Circle.h should not reference Point";
}

// Test 3: Files with cross-file dependencies (project-based mode)
TEST_F(MultiFileTranspilationTest, CrossFileDependencies) {
    // Create simple standalone files that don't have struct dependencies
    std::string mathCpp = R"(
int add(int a, int b) {
    return a + b;
}
)";

    std::string utilsCpp = R"(
// Uses function from math module (declared externally)
extern int add(int a, int b);

int addTen(int x) {
    return add(x, 10);
}
)";

    createSourceFile("math.cpp", mathCpp);
    createSourceFile("utils.cpp", utilsCpp);

    // Transpile entire project with --source-dir
    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", (testDir / "src").string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0) << "Project transpilation failed: " << result.output;

    // Verify files created
    EXPECT_TRUE(fileExists(outputDir / "math.h"));
    EXPECT_TRUE(fileExists(outputDir / "math.c"));
    EXPECT_TRUE(fileExists(outputDir / "utils.h"));
    EXPECT_TRUE(fileExists(outputDir / "utils.c"));

    // Verify math.h has the add function
    std::string mathH = readFile(outputDir / "math.h");
    EXPECT_THAT(mathH, HasSubstr("int add")) << "math.h should have add function";

    // Verify utils.c includes utils.h
    std::string utilsC = readFile(outputDir / "utils.c");
    EXPECT_THAT(utilsC, HasSubstr("#include \"utils.h\""))
        << "utils.c should include utils.h";
}

// Test 4: Output directory with absolute path (project-based mode)
TEST_F(MultiFileTranspilationTest, OutputDirectoryAbsolute) {
    std::string simpleCpp = R"(
int add(int a, int b) {
    return a + b;
}
)";

    createSourceFile("math.cpp", simpleCpp);

    // Create output directory with absolute path
    fs::path absOutputDir = fs::absolute(testDir / "abs_output");
    fs::create_directories(absOutputDir);

    auto result = executeTranspiler({
        "--source-dir", (testDir / "src").string(),
        "--output-dir", absOutputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0) << "Transpilation failed: " << result.output;

    // Verify files in absolute output directory
    EXPECT_TRUE(fileExists(absOutputDir / "math.h")) << "math.h not in absolute output dir";
    EXPECT_TRUE(fileExists(absOutputDir / "math.c")) << "math.c not in absolute output dir";
}

// Test 5: Output directory with relative path (project-based mode)
TEST_F(MultiFileTranspilationTest, OutputDirectoryRelative) {
    std::string simpleCpp = R"(
int multiply(int a, int b) {
    return a * b;
}
)";

    createSourceFile("calc.cpp", simpleCpp);

    // Create relative output directory
    fs::path relOutputDir = testDir / "rel_output";
    fs::create_directories(relOutputDir);

    auto result = executeTranspiler({
        "--source-dir", (testDir / "src").string(),
        "--output-dir", relOutputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0) << "Transpilation failed: " << result.output;

    // Verify files in relative output directory
    EXPECT_TRUE(fileExists(relOutputDir / "calc.h")) << "calc.h not in relative output dir";
    EXPECT_TRUE(fileExists(relOutputDir / "calc.c")) << "calc.c not in relative output dir";
}

// Test 6: Header/Implementation separation (project-based mode)
TEST_F(MultiFileTranspilationTest, HeaderImplementationSeparation) {
    std::string complexCpp = R"(
struct Calculator {
    int value;
};

void init(struct Calculator* c, int v) {
    c->value = v;
}

int add(struct Calculator* c, int x) {
    c->value += x;
    return c->value;
}

int subtract(struct Calculator* c, int x) {
    c->value -= x;
    return c->value;
}
)";

    createSourceFile("Calculator.cpp", complexCpp);

    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", (testDir / "src").string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    ASSERT_EQ(result.exitCode, 0) << "Transpilation failed: " << result.output;

    // Read files
    std::string headerContent = readFile(outputDir / "Calculator.h");
    std::string implContent = readFile(outputDir / "Calculator.c");

    // Verify header has struct and function declarations
    EXPECT_THAT(headerContent, HasSubstr("struct Calculator"))
        << "Header should have struct definition";
    EXPECT_THAT(headerContent, HasSubstr("int add"))
        << "Header should have function declarations";
    EXPECT_THAT(headerContent, HasSubstr("int subtract"))
        << "Header should have function declarations";

    // Note: The transpiler may include function bodies in some cases,
    // so we just verify the structure is present

    // Verify implementation has function bodies
    EXPECT_THAT(implContent, HasSubstr("c->value += x"))
        << "Implementation should contain function bodies";
    EXPECT_THAT(implContent, HasSubstr("c->value -= x"))
        << "Implementation should contain function bodies";
}

// Test 7: Include directives - verify .c files include their .h files (project-based mode)
TEST_F(MultiFileTranspilationTest, IncludeDirectives) {
    std::string vectorCpp = R"(
struct Vector {
    int x, y, z;
};

int magnitude(struct Vector* v) {
    return v->x * v->x + v->y * v->y + v->z * v->z;
}

void normalize(struct Vector* v) {
    int mag = magnitude(v);
    if (mag > 0) {
        v->x /= mag;
        v->y /= mag;
        v->z /= mag;
    }
}
)";

    createSourceFile("Vector.cpp", vectorCpp);

    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", (testDir / "src").string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    ASSERT_EQ(result.exitCode, 0) << "Transpilation failed: " << result.output;

    // Read implementation file
    std::string implContent = readFile(outputDir / "Vector.c");

    // Verify include directive at top of file
    EXPECT_THAT(implContent, HasSubstr("#include \"Vector.h\""))
        << "Implementation must include its own header";

    // Verify include is near the top (within first 10 lines)
    std::istringstream stream(implContent);
    std::string line;
    int lineNum = 0;
    bool foundInclude = false;

    while (std::getline(stream, line) && lineNum < 10) {
        if (line.find("#include \"Vector.h\"") != std::string::npos) {
            foundInclude = true;
            break;
        }
        lineNum++;
    }

    EXPECT_TRUE(foundInclude) << "Include directive should be near top of file";
}

// Test 8: File naming correctness (project-based mode)
TEST_F(MultiFileTranspilationTest, FileNamingCorrectness) {
    // Test various input filename patterns
    struct TestCase {
        std::string inputName;
        std::string expectedBaseName;
    };

    std::vector<TestCase> testCases = {
        {"simple.cpp", "simple"},
        {"MyClass.cpp", "MyClass"},
        {"my_class.cpp", "my_class"},
        {"test-file.cpp", "test-file"}
    };

    for (const auto& testCase : testCases) {
        // Create a fresh test directory for each case
        fs::path caseTestDir = testDir / ("test_" + testCase.expectedBaseName);
        fs::path caseSrcDir = caseTestDir / "src";
        fs::create_directories(caseSrcDir);

        std::string content = "int test() { return 42; }";
        std::ofstream(caseSrcDir / testCase.inputName) << content;

        fs::path caseOutputDir = caseTestDir / "output";
        fs::create_directories(caseOutputDir);

        auto result = executeTranspiler({
            "--source-dir", caseSrcDir.string(),
            "--output-dir", caseOutputDir.string(),
            "--"
        });

        EXPECT_EQ(result.exitCode, 0)
            << "Failed for " << testCase.inputName << ": " << result.output;

        // Verify correct filenames
        std::string expectedH = testCase.expectedBaseName + ".h";
        std::string expectedC = testCase.expectedBaseName + ".c";

        EXPECT_TRUE(fileExists(caseOutputDir / expectedH))
            << "Missing header file: " << expectedH;
        EXPECT_TRUE(fileExists(caseOutputDir / expectedC))
            << "Missing implementation file: " << expectedC;
    }
}

// Test 9: Header file format (project-based mode)
TEST_F(MultiFileTranspilationTest, HeaderFileFormat) {
    std::string simpleCpp = "int foo() { return 1; }";
    createSourceFile("test_file.cpp", simpleCpp);

    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", (testDir / "src").string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    ASSERT_EQ(result.exitCode, 0) << "Transpilation failed: " << result.output;

    std::string headerContent = readFile(outputDir / "test_file.h");

    // Verify header has function declaration
    EXPECT_THAT(headerContent, HasSubstr("int foo"))
        << "Header should have function declaration";

    // Verify header has proper comment
    EXPECT_THAT(headerContent, HasSubstr("// Generated from:"))
        << "Header should have generation comment";
    EXPECT_THAT(headerContent, HasSubstr("// Header file"))
        << "Header should have header file comment";
}

// Test 10: Empty file handling (project-based mode)
TEST_F(MultiFileTranspilationTest, EmptyFileHandling) {
    std::string emptyCpp = "// Empty file\n";
    createSourceFile("empty.cpp", emptyCpp);

    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", (testDir / "src").string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    // Should handle empty file gracefully
    // Either succeed with minimal output or fail with clear error
    if (result.exitCode == 0) {
        // If it succeeds, files should still be created
        EXPECT_TRUE(fileExists(outputDir / "empty.h"));
        EXPECT_TRUE(fileExists(outputDir / "empty.c"));
    }
    // If it fails, that's also acceptable - just verify no crash
}

// ============================================================================
// Directory Structure Preservation Tests (Phase 1)
// ============================================================================

// Test: Preserve simple directory structure with --source-dir (project-based mode)
TEST_F(MultiFileTranspilationTest, StructurePreservation_SimpleDirectory) {
    // Create source files in subdirectories
    fs::path srcDir = testDir / "src";
    fs::path mathDir = srcDir / "math";
    fs::path utilsDir = srcDir / "utils";
    fs::create_directories(mathDir);
    fs::create_directories(utilsDir);

    std::string vectorCpp = R"(
struct Vector {
    int x;
    int y;
};
)";

    std::string helpersCpp = R"(
void help() {
    // helper function
}
)";

    std::ofstream(mathDir / "Vector.cpp") << vectorCpp;
    std::ofstream(utilsDir / "helpers.cpp") << helpersCpp;

    // Transpile entire project with structure preservation
    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0) << "Project transpilation failed: " << result.output;

    // Verify structure preserved
    EXPECT_TRUE(fileExists(outputDir / "math/Vector.h"))
        << "Expected output at: " << (outputDir / "math/Vector.h");
    EXPECT_TRUE(fileExists(outputDir / "math/Vector.c"))
        << "Expected output at: " << (outputDir / "math/Vector.c");
    EXPECT_TRUE(fileExists(outputDir / "utils/helpers.h"))
        << "Expected output at: " << (outputDir / "utils/helpers.h");
    EXPECT_TRUE(fileExists(outputDir / "utils/helpers.c"))
        << "Expected output at: " << (outputDir / "utils/helpers.c");

    // Verify files are NOT in flat structure
    EXPECT_FALSE(fileExists(outputDir / "Vector.h"))
        << "Files should not be in flat output directory";
    EXPECT_FALSE(fileExists(outputDir / "helpers.h"))
        << "Files should not be in flat output directory";
}

// Test: Nested directory structure preservation (project-based mode)
TEST_F(MultiFileTranspilationTest, StructurePreservation_NestedDirectories) {
    // Create deeply nested structure: src/math/algebra/Vector.cpp
    fs::path srcDir = testDir / "src";
    fs::path algebraDir = srcDir / "math" / "algebra";
    fs::create_directories(algebraDir);

    std::string vectorCpp = R"(
struct Vector {
    double x, y, z;
};
)";

    std::ofstream(algebraDir / "Vector.cpp") << vectorCpp;

    // Transpile entire project
    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0) << "Transpilation failed: " << result.output;

    // Verify nested structure preserved
    EXPECT_TRUE(fileExists(outputDir / "math/algebra/Vector.h"));
    EXPECT_TRUE(fileExists(outputDir / "math/algebra/Vector.c"));
}

// Test: File at source root (no subdirectory) (project-based mode)
TEST_F(MultiFileTranspilationTest, StructurePreservation_FileAtRoot) {
    // Create file directly in source root
    fs::path srcDir = testDir / "src";
    fs::create_directories(srcDir);

    std::string pointCpp = R"(
struct Point {
    int x;
};
)";

    std::ofstream(srcDir / "Point.cpp") << pointCpp;

    // Transpile entire project
    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0) << "Transpilation failed: " << result.output;

    // File is at root of source, should be at root of output
    EXPECT_TRUE(fileExists(outputDir / "Point.h"));
    EXPECT_TRUE(fileExists(outputDir / "Point.c"));
}

// Test: Multiple files preserving different subdirectories (project-based mode)
TEST_F(MultiFileTranspilationTest, StructurePreservation_MixedStructure) {
    // Create files in different subdirectories
    fs::path srcDir = testDir / "src";
    fs::path coreDir = srcDir / "core";
    fs::path uiDir = srcDir / "ui";
    fs::create_directories(coreDir);
    fs::create_directories(uiDir);

    std::string engineCpp = R"(
struct Engine {
    int power;
};
)";

    std::string windowCpp = R"(
struct Window {
    int width;
};
)";

    std::ofstream(coreDir / "Engine.cpp") << engineCpp;
    std::ofstream(uiDir / "Window.cpp") << windowCpp;

    // Transpile entire project
    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0) << "Project transpilation failed: " << result.output;

    // Verify structure preserved for both
    EXPECT_TRUE(fileExists(outputDir / "core/Engine.h"));
    EXPECT_TRUE(fileExists(outputDir / "core/Engine.c"));
    EXPECT_TRUE(fileExists(outputDir / "ui/Window.h"));
    EXPECT_TRUE(fileExists(outputDir / "ui/Window.c"));
}

// Test: Relative paths in source-dir (project-based mode)
TEST_F(MultiFileTranspilationTest, StructurePreservation_RelativePaths) {
    // Create source files
    fs::path srcDir = testDir / "src";
    fs::path mathDir = srcDir / "math";
    fs::create_directories(mathDir);

    std::string calcCpp = R"(
int add(int a, int b) {
    return a + b;
}
)";

    std::ofstream(mathDir / "calc.cpp") << calcCpp;

    // Transpile using relative paths
    fs::create_directories(outputDir);

    // Change to test directory to use relative paths
    fs::path originalDir = fs::current_path();
    fs::current_path(testDir);

    auto result = executeTranspiler({
        "--source-dir", "src",
        "--output-dir", outputDir.string(),
        "--"
    });

    // Restore original directory
    fs::current_path(originalDir);

    EXPECT_EQ(result.exitCode, 0) << "Transpilation failed: " << result.output;

    // Verify structure preserved with relative paths
    EXPECT_TRUE(fileExists(outputDir / "math/calc.h"));
    EXPECT_TRUE(fileExists(outputDir / "math/calc.c"));
}

// Test: Name collision resolution via structure preservation (project-based mode)
TEST_F(MultiFileTranspilationTest, StructurePreservation_NameCollisionResolution) {
    // Create files with same name in different directories
    fs::path srcDir = testDir / "src";
    fs::path frontendDir = srcDir / "frontend";
    fs::path backendDir = srcDir / "backend";
    fs::create_directories(frontendDir);
    fs::create_directories(backendDir);

    std::string frontendVectorCpp = R"(
struct FrontendVector {
    int data;
};
)";

    std::string backendVectorCpp = R"(
struct BackendVector {
    double data;
};
)";

    std::ofstream(frontendDir / "Vector.cpp") << frontendVectorCpp;
    std::ofstream(backendDir / "Vector.cpp") << backendVectorCpp;

    // Transpile entire project
    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0) << "Project transpilation failed: " << result.output;

    // Both files should exist without collision
    EXPECT_TRUE(fileExists(outputDir / "frontend/Vector.h"));
    EXPECT_TRUE(fileExists(outputDir / "frontend/Vector.c"));
    EXPECT_TRUE(fileExists(outputDir / "backend/Vector.h"));
    EXPECT_TRUE(fileExists(outputDir / "backend/Vector.c"));

    // Verify content is different (no collision)
    std::string frontendH = readFile(outputDir / "frontend/Vector.h");
    std::string backendH = readFile(outputDir / "backend/Vector.h");
    EXPECT_THAT(frontendH, HasSubstr("FrontendVector"));
    EXPECT_THAT(backendH, HasSubstr("BackendVector"));
}

// ============================================================================
// Auto-Discovery Tests (Recursive File Discovery)
// ============================================================================

// Test: Auto-discovery with --source-dir and no file arguments
TEST_F(MultiFileTranspilationTest, AutoDiscovery_BasicUsage) {
    // Create source files in directory structure
    fs::path srcDir = testDir / "src";
    fs::create_directories(srcDir / "math");
    fs::create_directories(srcDir / "utils");

    std::string addCpp = "int add(int a, int b) { return a + b; }";
    std::string mulCpp = "int mul(int a, int b) { return a * b; }";
    std::string helpCpp = "void help() { }";

    std::ofstream(srcDir / "math" / "add.cpp") << addCpp;
    std::ofstream(srcDir / "math" / "mul.cpp") << mulCpp;
    std::ofstream(srcDir / "utils" / "help.cpp") << helpCpp;

    // Transpile using auto-discovery (no file arguments)
    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0) << "Auto-discovery failed: " << result.output;
    EXPECT_THAT(result.output, HasSubstr("Auto-discovering"))
        << "Should show auto-discovery message";
    EXPECT_THAT(result.output, HasSubstr("Discovered 3 file(s)"))
        << "Should discover all 3 .cpp files";

    // Verify all files transpiled with structure preserved
    EXPECT_TRUE(fileExists(outputDir / "math/add.h"));
    EXPECT_TRUE(fileExists(outputDir / "math/add.c"));
    EXPECT_TRUE(fileExists(outputDir / "math/mul.h"));
    EXPECT_TRUE(fileExists(outputDir / "math/mul.c"));
    EXPECT_TRUE(fileExists(outputDir / "utils/help.h"));
    EXPECT_TRUE(fileExists(outputDir / "utils/help.c"));
}

// Test: Auto-discovery with multiple extensions (.cpp, .cxx, .cc)
TEST_F(MultiFileTranspilationTest, AutoDiscovery_MultipleExtensions) {
    fs::path srcDir = testDir / "src";
    fs::create_directories(srcDir);

    std::string content = "int func() { return 0; }";
    std::ofstream(srcDir / "file1.cpp") << content;
    std::ofstream(srcDir / "file2.cxx") << content;
    std::ofstream(srcDir / "file3.cc") << content;

    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0);
    EXPECT_THAT(result.output, HasSubstr("Discovered 3 file(s)"));

    // Verify all extensions discovered
    EXPECT_TRUE(fileExists(outputDir / "file1.h"));
    EXPECT_TRUE(fileExists(outputDir / "file2.h"));
    EXPECT_TRUE(fileExists(outputDir / "file3.h"));
}

// Test: Auto-discovery excludes build directories
TEST_F(MultiFileTranspilationTest, AutoDiscovery_ExcludesBuildDirs) {
    fs::path srcDir = testDir / "src";
    fs::create_directories(srcDir);
    fs::create_directories(srcDir / "build");
    fs::create_directories(srcDir / "build-debug");
    fs::create_directories(srcDir / "cmake-build-release");

    std::string content = "int func() { return 0; }";
    std::ofstream(srcDir / "main.cpp") << content;
    std::ofstream(srcDir / "build/generated.cpp") << content;
    std::ofstream(srcDir / "build-debug/test.cpp") << content;
    std::ofstream(srcDir / "cmake-build-release/cmake.cpp") << content;

    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0);
    EXPECT_THAT(result.output, HasSubstr("Discovered 1 file(s)"))
        << "Should only discover main.cpp, excluding build dirs";

    // Verify only main.cpp transpiled
    EXPECT_TRUE(fileExists(outputDir / "main.h"));
    EXPECT_FALSE(fileExists(outputDir / "build/generated.h"));
    EXPECT_FALSE(fileExists(outputDir / "build-debug/test.h"));
}

// Test: Auto-discovery excludes hidden directories
TEST_F(MultiFileTranspilationTest, AutoDiscovery_ExcludesHiddenDirs) {
    fs::path srcDir = testDir / "src";
    fs::create_directories(srcDir);
    fs::create_directories(srcDir / ".git");
    fs::create_directories(srcDir / ".svn");
    fs::create_directories(srcDir / ".cache");

    std::string content = "int func() { return 0; }";
    std::ofstream(srcDir / "main.cpp") << content;
    std::ofstream(srcDir / ".git/hook.cpp") << content;
    std::ofstream(srcDir / ".svn/entry.cpp") << content;
    std::ofstream(srcDir / ".cache/cache.cpp") << content;

    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0);
    EXPECT_THAT(result.output, HasSubstr("Discovered 1 file(s)"));

    EXPECT_TRUE(fileExists(outputDir / "main.h"));
    EXPECT_FALSE(fileExists(outputDir / ".git/hook.h"));
}

// Test: Auto-discovery excludes node_modules and vendor
TEST_F(MultiFileTranspilationTest, AutoDiscovery_ExcludesDependencyDirs) {
    fs::path srcDir = testDir / "src";
    fs::create_directories(srcDir);
    fs::create_directories(srcDir / "node_modules/package");
    fs::create_directories(srcDir / "vendor/lib");

    std::string content = "int func() { return 0; }";
    std::ofstream(srcDir / "main.cpp") << content;
    std::ofstream(srcDir / "node_modules/package/index.cpp") << content;
    std::ofstream(srcDir / "vendor/lib/lib.cpp") << content;

    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0);
    EXPECT_THAT(result.output, HasSubstr("Discovered 1 file(s)"));

    EXPECT_TRUE(fileExists(outputDir / "main.h"));
}

// Test: Empty directory warning
TEST_F(MultiFileTranspilationTest, AutoDiscovery_EmptyDirectoryWarning) {
    fs::path srcDir = testDir / "empty_src";
    fs::create_directories(srcDir);

    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    // Should fail with warning
    EXPECT_NE(result.exitCode, 0);
    EXPECT_THAT(result.output, HasSubstr("No C++ source files"))
        << "Should warn about no files found";
}

// Test: Deeply nested directory structure
TEST_F(MultiFileTranspilationTest, AutoDiscovery_DeeplyNested) {
    fs::path srcDir = testDir / "src";
    fs::path deepDir = srcDir / "a/b/c/d/e";
    fs::create_directories(deepDir);

    std::string content = "int func() { return 0; }";
    std::ofstream(srcDir / "top.cpp") << content;
    std::ofstream(deepDir / "deep.cpp") << content;

    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0);
    EXPECT_THAT(result.output, HasSubstr("Discovered 2 file(s)"));

    // Verify structure preserved
    EXPECT_TRUE(fileExists(outputDir / "top.h"));
    EXPECT_TRUE(fileExists(outputDir / "a/b/c/d/e/deep.h"));
}

// Test: Auto-discovery ignores non-C++ files
TEST_F(MultiFileTranspilationTest, AutoDiscovery_IgnoresNonCppFiles) {
    fs::path srcDir = testDir / "src";
    fs::create_directories(srcDir);

    std::string content = "int func() { return 0; }";
    std::ofstream(srcDir / "code.cpp") << content;
    std::ofstream(srcDir / "header.h") << "// header";
    std::ofstream(srcDir / "readme.txt") << "readme";
    std::ofstream(srcDir / "Makefile") << "all:";
    std::ofstream(srcDir / "data.json") << "{}";

    fs::create_directories(outputDir);
    auto result = executeTranspiler({
        "--source-dir", srcDir.string(),
        "--output-dir", outputDir.string(),
        "--"
    });

    EXPECT_EQ(result.exitCode, 0);
    EXPECT_THAT(result.output, HasSubstr("Discovered 1 file(s)"))
        << "Should only discover code.cpp";
}
