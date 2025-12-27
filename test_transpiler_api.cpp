// Test program for TranspilerAPI
#include "TranspilerAPI.h"
#include <iostream>

int main() {
    // Simple C++ code to transpile
    std::string cppCode = R"(
int add(int a, int b) {
    return a + b;
}

int main() {
    int result = add(5, 3);
    return 0;
}
)";

    // Configure transpiler options
    cpptoc::TranspileOptions options;
    options.cppStandard = 17;
    options.enableExceptions = false;
    options.enableRTTI = false;

    // Transpile the code
    std::cout << "Transpiling C++ code...\n";
    cpptoc::TranspileResult result = cpptoc::transpile(cppCode, "test.cpp", options);

    // Display results
    if (result.success) {
        std::cout << "\n=== Transpilation successful! ===\n\n";
        std::cout << "Generated C code:\n";
        std::cout << "=================\n";
        std::cout << result.c;
        std::cout << "\n=================\n";

        if (!result.h.empty()) {
            std::cout << "\nGenerated header:\n";
            std::cout << "=================\n";
            std::cout << result.h;
            std::cout << "\n=================\n";
        }
    } else {
        std::cout << "\n=== Transpilation failed! ===\n";
    }

    // Display diagnostics
    if (!result.diagnostics.empty()) {
        std::cout << "\nDiagnostics:\n";
        for (const auto& diag : result.diagnostics) {
            std::cout << "[" << diag.severity << "] ";
            if (diag.line > 0) {
                std::cout << diag.line << ":" << diag.column << ": ";
            }
            std::cout << diag.message << "\n";
        }
    }

    return result.success ? 0 : 1;
}
