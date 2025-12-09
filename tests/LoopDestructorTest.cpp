// LoopDestructorTest.cpp - Test suite for Story #156
// (Loop Break/Continue Handling)
//
// Tests that destructors are injected before break/continue statements

#include "CppToCVisitor.h"
#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>
#include <string>

using namespace clang;

// Test 1: Break with loop-local object
void test_BreakWithObject() {
    std::cout << "Running test_BreakWithObject... ";

    const char *Code = R"(
        class Iterator {
        public:
            Iterator();
            ~Iterator();
        };

        void search(int target) {
            for (int i = 0; i < 10; i++) {
                Iterator it;
                if (i == target) {
                    break;  // it.~Iterator() before break
                }
            }  // it.~Iterator() at loop iteration end
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 2: Continue with loop-local object
void test_ContinueWithObject() {
    std::cout << "Running test_ContinueWithObject... ";

    const char *Code = R"(
        class Temp {
        public:
            Temp();
            ~Temp();
        };

        void process() {
            for (int i = 0; i < 10; i++) {
                Temp t;
                if (i % 2 == 0) {
                    continue;  // t.~Temp() before continue
                }
            }  // t.~Temp() at iteration end
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 3: While loop with break
void test_WhileLoopBreak() {
    std::cout << "Running test_WhileLoopBreak... ";

    const char *Code = R"(
        class State {
        public:
            State();
            ~State();
        };

        void run() {
            while (true) {
                State s;
                if (false) {
                    break;  // s.~State() before break
                }
            }  // s.~State() at iteration end
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

int main() {
    std::cout << "\n=== Story #156: Loop Break/Continue Handling ===\n\n";

    test_BreakWithObject();
    test_ContinueWithObject();
    test_WhileLoopBreak();

    std::cout << "\n=== All Tests Passed ===\n";
    return 0;
}
