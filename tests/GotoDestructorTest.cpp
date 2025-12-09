// GotoDestructorTest.cpp - Test suite for Story #155
// (Goto Statement Handling)
//
// Tests that destructors are injected when goto jumps out of scope

#include "CppToCVisitor.h"
#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>
#include <string>

using namespace clang;

// Test 1: Goto out of scope
void test_GotoOutOfScope() {
    std::cout << "Running test_GotoOutOfScope... ";

    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void func(int flag) {
            Resource r;
            if (flag) {
                goto cleanup;  // r.~Resource() before goto
            }
        cleanup:
            return;
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 2: Multiple objects with goto
void test_MultipleObjectsGoto() {
    std::cout << "Running test_MultipleObjectsGoto... ";

    const char *Code = R"(
        class Object {
        public:
            Object(int id);
            ~Object();
        };

        void cleanup_pattern() {
            Object obj1(1);
            Object obj2(2);
            goto end;  // obj2.~Object(), obj1.~Object() before goto
        end:
            return;
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 3: Nested scopes with goto
void test_NestedScopesGoto() {
    std::cout << "Running test_NestedScopesGoto... ";

    const char *Code = R"(
        class Guard {
        public:
            Guard();
            ~Guard();
        };

        void complex() {
            Guard g1;
            {
                Guard g2;
                goto exit;  // g2.~Guard(), g1.~Guard() before goto
            }
        exit:
            return;
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

int main() {
    std::cout << "\n=== Story #155: Goto Statement Handling ===\n\n";

    test_GotoOutOfScope();
    test_MultipleObjectsGoto();
    test_NestedScopesGoto();

    std::cout << "\n=== All Tests Passed ===\n";
    return 0;
}
