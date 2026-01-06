#ifndef RUNTIME_TEST_HARNESS_H
#define RUNTIME_TEST_HARNESS_H

#include <string>
#include <vector>
#include <memory>

// RuntimeTestHarness: Helper class for runtime integration testing
// Provides full pipeline: C++ -> transpile -> C -> compile -> execute
//
// Purpose: Systematic framework for verifying transpiled C code actually works
// - Transpiles C++ to C using the transpiler
// - Compiles C code with gcc/clang
// - Executes compiled binaries
// - Captures stdout, stderr, exit codes, execution time
//
// Usage:
//   RuntimeTestHarness harness;
//   auto result = harness.transpileCompileExecute("int main() { return 0; }");
//   ASSERT_TRUE(result.success);
//   EXPECT_EQ(result.exit_code, 0);
//
// Features:
// - Automatic temporary file management
// - Configurable C standard (c99, c11, c17)
// - Support for gcc and clang compilers
// - Execution time measurement
// - Automatic cleanup on destruction
class RuntimeTestHarness {
public:
    // Compilation result structure
    struct CompilationResult {
        bool success;
        std::string stdout_output;
        std::string stderr_output;
        int exit_code;
        std::string binary_path;  // Path to compiled executable
    };

    // Execution result structure
    struct ExecutionResult {
        bool success;
        std::string stdout_output;
        std::string stderr_output;
        int exit_code;
        double execution_time_ms;
    };

    // Constructor: Initialize temporary directory
    RuntimeTestHarness();

    // Destructor: Cleanup temporary files
    ~RuntimeTestHarness();

    // Transpile C++ code to C using the transpiler
    // @param cpp_code: C++ source code
    // @param clang_args: Additional Clang compiler arguments
    // @return: Generated C code, or empty string on failure
    std::string transpile(const std::string& cpp_code,
                         const std::vector<std::string>& clang_args = {});

    // Compile C code with gcc/clang
    // @param c_code: C source code
    // @param compiler: Compiler to use (default: "gcc")
    // @param std_version: C standard version (default: "c99")
    // @param extra_flags: Additional compiler flags
    // @return: CompilationResult with success status and outputs
    CompilationResult compileC(const std::string& c_code,
                               const std::string& compiler = "gcc",
                               const std::string& std_version = "c99",
                               const std::vector<std::string>& extra_flags = {});

    // Execute compiled binary
    // @param binary_path: Path to executable
    // @param args: Command line arguments
    // @param stdin_data: Data to pipe to stdin
    // @return: ExecutionResult with success status and outputs
    ExecutionResult execute(const std::string& binary_path,
                           const std::vector<std::string>& args = {},
                           const std::string& stdin_data = "");

    // Full pipeline: transpile -> compile -> execute
    // @param cpp_code: C++ source code
    // @param clang_args: Additional Clang compiler arguments for transpilation
    // @param runtime_args: Command line arguments for execution
    // @param stdin_data: Data to pipe to stdin
    // @return: ExecutionResult with success status and outputs
    ExecutionResult transpileCompileExecute(
        const std::string& cpp_code,
        const std::vector<std::string>& clang_args = {},
        const std::vector<std::string>& runtime_args = {},
        const std::string& stdin_data = "");

    // Get temporary directory path
    const std::string& getTempDir() const { return temp_dir_; }

    // Get temporary file path with given filename
    // @param filename: Name of the temporary file
    // @return: Full path to temporary file
    std::string getTempPath(const std::string& filename) const {
        return temp_dir_ + "/" + filename;
    }

    // Create temporary header file with given content
    // @param content: Header file content
    // @param filename: Header filename (e.g., "point.h")
    // @return: Path to created header file
    std::string createTempHeaderFile(const std::string& content,
                                     const std::string& filename = "custom.h");

    // Create temporary file with given content (public for test use)
    // @param content: File content
    // @param extension: File extension (e.g., ".c", ".cpp", ".txt")
    // @return: Path to created file
    std::string createTempFile(const std::string& content, const std::string& extension);

private:
    std::string temp_dir_;
    std::vector<std::string> temp_files_;

    // Cleanup temporary files and directory
    void cleanup();

    // Execute shell command and capture output
    // @param command: Shell command to execute
    // @param stdout_file: File to capture stdout
    // @param stderr_file: File to capture stderr
    // @return: Exit code
    int executeCommand(const std::string& command,
                      const std::string& stdout_file,
                      const std::string& stderr_file);

    // Read file content
    // @param file_path: Path to file
    // @return: File content, or empty string on error
    std::string readFile(const std::string& file_path);

    // Write file content
    // @param file_path: Path to file
    // @param content: Content to write
    // @return: True on success
    bool writeFile(const std::string& file_path, const std::string& content);
};

#endif // RUNTIME_TEST_HARNESS_H
