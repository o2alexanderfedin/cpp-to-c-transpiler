/**
 * @file VirtualCallTranslatorTest.cpp
 * @brief Tests for Story #172: Virtual Call Translation
 *
 * Tests core virtual call detection and method name resolution.
 */

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/VirtualCallTranslator.h"
#include <iostream>
#include <vector>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

// Helper visitor to find method calls
class CallFinder : public RecursiveASTVisitor<CallFinder> {
public:
    std::vector<CXXMemberCallExpr*> Calls;

    bool VisitCXXMemberCallExpr(CXXMemberCallExpr *E) {
        Calls.push_back(E);
        return true;
    }
};

// Test 1: Detect virtual call
void test_DetectVirtualCall() {
    TEST_START("DetectVirtualCall");

    const char *code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };

        void test(Shape* s) {
            s->draw();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualCallTranslator translator(Context, analyzer);

    // Find all method calls
    CallFinder finder;
    finder.TraverseDecl(Context.getTranslationUnitDecl());

    ASSERT(!finder.Calls.empty(), "Should find method call");

    // Check if it's virtual
    bool foundVirtualCall = false;
    for (auto* call : finder.Calls) {
        if (translator.isVirtualCall(call)) {
            foundVirtualCall = true;
            break;
        }
    }

    ASSERT(foundVirtualCall, "Should detect virtual call");

    TEST_PASS("DetectVirtualCall");
}

// Test 2: Non-virtual call should not be detected as virtual
void test_NonVirtualCallNotDetected() {
    TEST_START("NonVirtualCallNotDetected");

    const char *code = R"(
        class Point {
        public:
            void move() {}  // Non-virtual
        };

        void test(Point* p) {
            p->move();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualCallTranslator translator(Context, analyzer);

    CallFinder finder;
    finder.TraverseDecl(Context.getTranslationUnitDecl());

    ASSERT(!finder.Calls.empty(), "Should find method call");

    // Check that it's NOT virtual
    for (auto* call : finder.Calls) {
        ASSERT(!translator.isVirtualCall(call),
               "Non-virtual call should not be detected as virtual");
    }

    TEST_PASS("NonVirtualCallNotDetected");
}

// Test 3: Get vtable method name
void test_GetVtableMethodName() {
    TEST_START("GetVtableMethodName");

    const char *code = R"(
        class Shape {
        public:
            virtual void draw() {}
            virtual void setColor(int r) {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualCallTranslator translator(Context, analyzer);

    // Find the Shape class
    CXXRecordDecl* Shape = nullptr;
    for (auto *D : Context.getTranslationUnitDecl()->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Shape" && RD->isCompleteDefinition()) {
                Shape = RD;
                break;
            }
        }
    }

    ASSERT(Shape, "Shape class not found");

    // Check method names
    for (auto* method : Shape->methods()) {
        if (!method->isVirtual()) continue;

        std::string name = translator.getVtableMethodName(method);
        std::string methodName = method->getNameAsString();

        ASSERT(name == methodName,
               "Vtable method name should match: expected " + methodName + ", got " + name);
    }

    TEST_PASS("GetVtableMethodName");
}

int main() {
    std::cout << "=== VirtualCallTranslator Tests (Story #172) ===" << std::endl;

    test_DetectVirtualCall();
    test_NonVirtualCallNotDetected();
    test_GetVtableMethodName();

    std::cout << "\n=== All VirtualCallTranslator tests passed! ===" << std::endl;
    return 0;
}
