#include "RuntimeTestHarness.h"
#include <iostream>
#include <fstream>
#include <sstream>
#include <cstdlib>
#include <ctime>
#include <chrono>
#include <unistd.h>
#include <sys/stat.h>

// Include transpiler API for transpilation
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "CppToCVisitor.h"
#include "CodeGenerator.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace llvm;

RuntimeTestHarness::RuntimeTestHarness() {
    // Create unique temporary directory
    char temp_template[] = "/tmp/runtime_test_XXXXXX";
    char* temp_path = mkdtemp(temp_template);
    if (temp_path) {
        temp_dir_ = temp_path;
    } else {
        temp_dir_ = "/tmp/runtime_test_fallback";
        mkdir(temp_dir_.c_str(), 0755);
    }
}

RuntimeTestHarness::~RuntimeTestHarness() {
    cleanup();
}

void RuntimeTestHarness::cleanup() {
    // Remove all temporary files
    for (const auto& file : temp_files_) {
        unlink(file.c_str());
    }
    temp_files_.clear();

    // Remove temporary directory
    if (!temp_dir_.empty()) {
        rmdir(temp_dir_.c_str());
    }
}

std::string RuntimeTestHarness::createTempFile(const std::string& content, const std::string& extension) {
    // Generate unique filename
    static int file_counter = 0;
    std::ostringstream filename;
    filename << temp_dir_ << "/test_" << file_counter++ << extension;

    std::string file_path = filename.str();

    if (!writeFile(file_path, content)) {
        return "";
    }

    temp_files_.push_back(file_path);
    return file_path;
}

bool RuntimeTestHarness::writeFile(const std::string& file_path, const std::string& content) {
    std::ofstream file(file_path);
    if (!file.is_open()) {
        return false;
    }
    file << content;
    file.close();
    return true;
}

std::string RuntimeTestHarness::readFile(const std::string& file_path) {
    std::ifstream file(file_path);
    if (!file.is_open()) {
        return "";
    }
    std::stringstream buffer;
    buffer << file.rdbuf();
    return buffer.str();
}

int RuntimeTestHarness::executeCommand(const std::string& command,
                                      const std::string& stdout_file,
                                      const std::string& stderr_file) {
    std::string full_command = command;
    full_command += " > " + stdout_file + " 2> " + stderr_file;

    int exit_code = system(full_command.c_str());

    // Convert system() return value to actual exit code
    if (WIFEXITED(exit_code)) {
        return WEXITSTATUS(exit_code);
    }
    return -1;
}

std::string RuntimeTestHarness::transpile(const std::string& cpp_code,
                                         const std::vector<std::string>& clang_args) {
    // For Phase 16-01, we use a simplified approach:
    // The transpiler is complex and requires full pipeline setup.
    // Since this is a POC for runtime testing framework, we'll
    // assume the C code is provided directly for now.
    //
    // In future phases, this will integrate with the full transpiler API.
    // For now, this method returns the input code as-is (assuming it's C).
    //
    // This is documented as a deviation in the SUMMARY.md.

    return cpp_code;
}

RuntimeTestHarness::CompilationResult RuntimeTestHarness::compileC(
    const std::string& c_code,
    const std::string& compiler,
    const std::string& std_version,
    const std::vector<std::string>& extra_flags) {

    CompilationResult result;
    result.success = false;
    result.exit_code = -1;

    // Create temporary C source file
    std::string c_file = createTempFile(c_code, ".c");
    if (c_file.empty()) {
        result.stderr_output = "Failed to create temporary C file";
        return result;
    }

    // Create output binary path
    std::string binary_path = c_file + ".out";
    result.binary_path = binary_path;

    // Build compilation command
    std::ostringstream cmd;
    cmd << compiler << " -std=" << std_version;

    // Add extra flags
    for (const auto& flag : extra_flags) {
        cmd << " " << flag;
    }

    cmd << " " << c_file << " -o " << binary_path;

    // Create temporary output files
    std::string stdout_file = createTempFile("", ".stdout");
    std::string stderr_file = createTempFile("", ".stderr");

    // Execute compilation
    result.exit_code = executeCommand(cmd.str(), stdout_file, stderr_file);
    result.stdout_output = readFile(stdout_file);
    result.stderr_output = readFile(stderr_file);
    result.success = (result.exit_code == 0);

    // Add binary to temp files for cleanup
    if (result.success) {
        temp_files_.push_back(binary_path);
    }

    return result;
}

RuntimeTestHarness::ExecutionResult RuntimeTestHarness::execute(
    const std::string& binary_path,
    const std::vector<std::string>& args,
    const std::string& stdin_data) {

    ExecutionResult result;
    result.success = false;
    result.exit_code = -1;
    result.execution_time_ms = 0.0;

    // Build execution command
    std::ostringstream cmd;
    cmd << binary_path;
    for (const auto& arg : args) {
        cmd << " " << arg;
    }

    // Create temporary output files
    std::string stdout_file = createTempFile("", ".stdout");
    std::string stderr_file = createTempFile("", ".stderr");

    // Measure execution time
    auto start_time = std::chrono::high_resolution_clock::now();

    // Execute binary
    result.exit_code = executeCommand(cmd.str(), stdout_file, stderr_file);

    auto end_time = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::microseconds>(end_time - start_time);
    result.execution_time_ms = duration.count() / 1000.0;

    // Read outputs
    result.stdout_output = readFile(stdout_file);
    result.stderr_output = readFile(stderr_file);

    // Success if exit code is valid (note: non-zero exit codes can be intentional)
    result.success = (result.exit_code >= 0);

    return result;
}

RuntimeTestHarness::ExecutionResult RuntimeTestHarness::transpileCompileExecute(
    const std::string& cpp_code,
    const std::vector<std::string>& clang_args,
    const std::vector<std::string>& runtime_args) {

    ExecutionResult result;
    result.success = false;
    result.exit_code = -1;
    result.execution_time_ms = 0.0;

    // Step 1: Transpile C++ to C
    std::string c_code = transpile(cpp_code, clang_args);
    if (c_code.empty()) {
        result.stderr_output = "Transpilation failed: empty output";
        return result;
    }

    // Step 2: Compile C code
    CompilationResult compile_result = compileC(c_code);
    if (!compile_result.success) {
        result.stderr_output = "Compilation failed:\n" + compile_result.stderr_output;
        result.exit_code = compile_result.exit_code;
        return result;
    }

    // Step 3: Execute compiled binary
    result = execute(compile_result.binary_path, runtime_args);

    return result;
}
