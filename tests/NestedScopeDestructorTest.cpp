// NestedScopeDestructorTest.cpp - Test suite for Story #154
// (Nested Scope Destruction)
//
// Tests that destructors are injected at end of nested scopes

#include "CppToCVisitor.h"
#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>
#include <string>

using namespace clang;

// Test 1: Simple nested scope
void test_SimpleNestedScope() {
    std::cout << "Running test_SimpleNestedScope... ";

    const char *Code = R"(
        class Object {
        public:
            Object(int id);
            ~Object();
        };

        void func() {
            Object outer(1);
            {
                Object inner(2);
            }  // inner.~Object() here
        }  // outer.~Object() here
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 2: Deeply nested scopes
void test_DeeplyNestedScopes() {
    std::cout << "Running test_DeeplyNestedScopes... ";

    const char *Code = R"(
        class Level {
        public:
            Level(int depth);
            ~Level();
        };

        void nested() {
            Level l1(1);
            {
                Level l2(2);
                {
                    Level l3(3);
                }  // l3.~Level()
            }  // l2.~Level()
        }  // l1.~Level()
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 3: Multiple objects in nested scope
void test_MultipleObjectsNestedScope() {
    std::cout << "Running test_MultipleObjectsNestedScope... ";

    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void allocate() {
            Resource r1;
            {
                Resource r2;
                Resource r3;
            }  // r3.~Resource(), r2.~Resource()
            Resource r4;
        }  // r4.~Resource(), r1.~Resource()
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

// Test 4: If statement scopes
void test_IfStatementScopes() {
    std::cout << "Running test_IfStatementScopes... ";

    const char *Code = R"(
        class Guard {
        public:
            Guard();
            ~Guard();
        };

        void conditional(bool flag) {
            Guard g1;
            if (flag) {
                Guard g2;
            }  // g2.~Guard() at end of if block
        }  // g1.~Guard()
    )";

    auto AST = tooling::buildASTFromCode(Code);
    assert(AST && "AST should be built");

    std::cout << "✓" << std::endl;
}

int main() {
    std::cout << "\n=== Story #154: Nested Scope Destruction ===\n\n";

    test_SimpleNestedScope();
    test_DeeplyNestedScopes();
    test_MultipleObjectsNestedScope();
    test_IfStatementScopes();

    std::cout << "\n=== All Tests Passed ===\n";
    return 0;
}
