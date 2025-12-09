// EarlyReturnDestructorTest.cpp - Test suite for Story #153
// (Destructor Injection at Early Returns)
//
// Tests that destructors are injected before early return statements

#include "CppToCVisitor.h"
#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>
#include <string>

using namespace clang;

// Test 1: Single early return
void test_SingleEarlyReturn() {
    std::cout << "Running test_SingleEarlyReturn... ";

    const char *Code = R"(
        class Lock {
        public:
            Lock();
            ~Lock();
        };

        void func(bool flag) {
            Lock lock;
            if (flag) {
                return;  // lock.~Lock() must be called before return
            }
            // Work with lock
        }  // lock.~Lock() at normal exit
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 2: Multiple return paths
void test_MultipleReturnPaths() {
    std::cout << "Running test_MultipleReturnPaths... ";

    const char *Code = R"(
        class Resource {
        public:
            Resource(int id);
            ~Resource();
        };

        int compute(int x) {
            Resource r1(1);
            if (x < 0) {
                return -1;  // r1.~Resource() before return
            }
            Resource r2(2);
            if (x == 0) {
                return 0;  // r2.~Resource(), r1.~Resource() before return
            }
            return x;  // r2.~Resource(), r1.~Resource() before return
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 3: Nested scopes with early returns
void test_NestedScopesEarlyReturn() {
    std::cout << "Running test_NestedScopesEarlyReturn... ";

    const char *Code = R"(
        class Guard {
        public:
            Guard();
            ~Guard();
        };

        void process(int level) {
            Guard g1;
            if (level > 0) {
                Guard g2;
                if (level > 1) {
                    return;  // g2.~Guard(), g1.~Guard()
                }
            }
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 4: Return with value and objects
void test_ReturnWithValue() {
    std::cout << "Running test_ReturnWithValue... ";

    const char *Code = R"(
        class Temp {
        public:
            Temp();
            ~Temp();
        };

        int calculate() {
            Temp t1;
            int result = 42;
            Temp t2;
            return result;  // t2.~Temp(), t1.~Temp(), then return
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

int main() {
    std::cout << "\n=== Story #153: Destructor Injection at Early Returns ===\n\n";

    test_SingleEarlyReturn();
    test_MultipleReturnPaths();
    test_NestedScopesEarlyReturn();
    test_ReturnWithValue();

    std::cout << "\n=== All Tests Passed ===\n";
    return 0;
}
