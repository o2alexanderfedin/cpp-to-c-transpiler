#include "TranspilerAPI.h"
#include <iostream>

int main() {
    std::string cppCode = R"(
class Point {
public:
    int x, y;

    int getX() {
        return x;
    }

    void setX(int newX) {
        x = newX;
    }
};

int add(int a, int b) {
    return a + b;
}
)";

    cpptoc::TranspileOptions opts;
    opts.acsl.statements = true;

    auto result = cpptoc::transpile(cppCode, "test-point.cpp", opts);

    if (result.success) {
        std::cout << "=== Generated C Header (.h) ===" << std::endl;
        std::cout << result.h << std::endl;
        std::cout << "\n=== Generated C Implementation (.c) ===" << std::endl;
        std::cout << result.c << std::endl;
        std::cout << "\n=== ACSL Annotations ===" << std::endl;
        std::cout << result.acsl << std::endl;
    } else {
        std::cerr << "Transpilation failed!" << std::endl;
        for (const auto& diag : result.diagnostics) {
            std::cerr << diag.severity << ": " << diag.message << std::endl;
        }
        return 1;
    }

    return 0;
}
