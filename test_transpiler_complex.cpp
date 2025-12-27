// Test program for TranspilerAPI with complex C++ features
#include "TranspilerAPI.h"
#include <iostream>

int main() {
    // Test 1: Simple function
    std::cout << "\n=== Test 1: Simple Function ===\n";
    {
        std::string cppCode = R"(
int add(int a, int b) {
    return a + b;
}
)";
        cpptoc::TranspileOptions options;
        auto result = cpptoc::transpile(cppCode, "test1.cpp", options);
        if (result.success) {
            std::cout << "SUCCESS\n" << result.c << "\n";
        } else {
            std::cout << "FAILED\n";
        }
    }

    // Test 2: Class with methods
    std::cout << "\n=== Test 2: Class with Methods ===\n";
    {
        std::string cppCode = R"(
class Point {
    int x, y;
public:
    Point(int x, int y) : x(x), y(y) {}
    int getX() { return x; }
    int getY() { return y; }
};
)";
        cpptoc::TranspileOptions options;
        auto result = cpptoc::transpile(cppCode, "test2.cpp", options);
        if (result.success) {
            std::cout << "SUCCESS\n" << result.c << "\n";
        } else {
            std::cout << "FAILED\n";
        }
    }

    // Test 3: Control flow
    std::cout << "\n=== Test 3: Control Flow ===\n";
    {
        std::string cppCode = R"(
int factorial(int n) {
    if (n <= 1) return 1;
    int result = 1;
    for (int i = 2; i <= n; i++) {
        result *= i;
    }
    return result;
}
)";
        cpptoc::TranspileOptions options;
        auto result = cpptoc::transpile(cppCode, "test3.cpp", options);
        if (result.success) {
            std::cout << "SUCCESS\n" << result.c << "\n";
        } else {
            std::cout << "FAILED\n";
        }
    }

    // Test 4: Pointers and references
    std::cout << "\n=== Test 4: Pointers and References ===\n";
    {
        std::string cppCode = R"(
void swap(int* a, int* b) {
    int temp = *a;
    *a = *b;
    *b = temp;
}
)";
        cpptoc::TranspileOptions options;
        auto result = cpptoc::transpile(cppCode, "test4.cpp", options);
        if (result.success) {
            std::cout << "SUCCESS\n" << result.c << "\n";
        } else {
            std::cout << "FAILED\n";
        }
    }

    std::cout << "\n=== All Tests Complete ===\n";
    return 0;
}
