// transpiler-api-cli: Simple CLI wrapper for TranspilerAPI
// This tool wraps the TranspilerAPI library and outputs JSON for use by the Node.js API
//
// Usage: transpiler-api-cli <input.cpp> [--json]
//
// This is a minimal CLI that:
// 1. Reads C++ source from a file
// 2. Calls cpptoc::transpile()
// 3. Outputs the result as JSON to stdout
//
// This is used by the Node.js API server to transpile C++ code.

#include "TranspilerAPI.h"
#include <fstream>
#include <iostream>
#include <sstream>
#include <string>
#include <unistd.h>  // For dup, dup2, close, STDOUT_FILENO, STDERR_FILENO

// Simple JSON escaping for strings
std::string escapeJSON(const std::string& str) {
    std::string result;
    result.reserve(str.length());

    for (char c : str) {
        switch (c) {
            case '"':  result += "\\\""; break;
            case '\\': result += "\\\\"; break;
            case '\b': result += "\\b"; break;
            case '\f': result += "\\f"; break;
            case '\n': result += "\\n"; break;
            case '\r': result += "\\r"; break;
            case '\t': result += "\\t"; break;
            default:
                if (c < 32) {
                    // Control character: escape as \uXXXX
                    char buf[7];
                    snprintf(buf, sizeof(buf), "\\u%04x", (unsigned char)c);
                    result += buf;
                } else {
                    result += c;
                }
        }
    }
    return result;
}

// Output result as JSON
void outputJSON(const cpptoc::TranspileResult& result) {
    std::cout << "{\n";
    std::cout << "  \"success\": " << (result.success ? "true" : "false") << ",\n";
    std::cout << "  \"c\": \"" << escapeJSON(result.c) << "\",\n";
    std::cout << "  \"h\": \"" << escapeJSON(result.h) << "\",\n";
    std::cout << "  \"acsl\": \"" << escapeJSON(result.acsl) << "\",\n";
    std::cout << "  \"diagnostics\": [\n";

    for (size_t i = 0; i < result.diagnostics.size(); ++i) {
        const auto& diag = result.diagnostics[i];
        std::cout << "    {\n";
        std::cout << "      \"line\": " << diag.line << ",\n";
        std::cout << "      \"column\": " << diag.column << ",\n";
        std::cout << "      \"severity\": \"" << escapeJSON(diag.severity) << "\",\n";
        std::cout << "      \"message\": \"" << escapeJSON(diag.message) << "\"\n";
        std::cout << "    }";
        if (i < result.diagnostics.size() - 1) {
            std::cout << ",";
        }
        std::cout << "\n";
    }

    std::cout << "  ]\n";
    std::cout << "}\n";
}

int main(int argc, char** argv) {
    if (argc < 2) {
        std::cerr << "Usage: " << argv[0] << " <input.cpp> [--json]\n";
        return 1;
    }

    std::string inputFile = argv[1];
    bool jsonOutput = (argc > 2 && std::string(argv[2]) == "--json");

    // Read input file
    std::ifstream file(inputFile);
    if (!file) {
        std::cerr << "Error: Cannot open file: " << inputFile << "\n";
        return 1;
    }

    std::stringstream buffer;
    buffer << file.rdbuf();
    std::string cppSource = buffer.str();

    // Set up options (default options for now)
    cpptoc::TranspileOptions options;
    options.cppStandard = 17;

    // Redirect stdout to stderr to capture all debug output
    // Save original stdout
    int stdout_fd = dup(STDOUT_FILENO);
    int stderr_fd = dup(STDERR_FILENO);

    // Redirect stdout to stderr temporarily
    dup2(stderr_fd, STDOUT_FILENO);

    // Transpile
    auto result = cpptoc::transpile(cppSource, inputFile, options);

    // Restore stdout
    dup2(stdout_fd, STDOUT_FILENO);
    close(stdout_fd);
    close(stderr_fd);

    // Output result
    if (jsonOutput) {
        outputJSON(result);
    } else {
        // Plain text output
        if (result.success) {
            std::cout << "// C implementation:\n";
            std::cout << result.c << "\n";

            if (!result.h.empty()) {
                std::cout << "\n// C header:\n";
                std::cout << result.h << "\n";
            }

            if (!result.acsl.empty()) {
                std::cout << "\n// ACSL annotations:\n";
                std::cout << result.acsl << "\n";
            }
        } else {
            std::cerr << "Transpilation failed:\n";
            for (const auto& diag : result.diagnostics) {
                std::cerr << inputFile << ":" << diag.line << ":" << diag.column
                          << ": " << diag.severity << ": " << diag.message << "\n";
            }
            return 1;
        }
    }

    return result.success ? 0 : 1;
}
