/**
 * @file VirtualCallTranslatorTest.cpp
 * @brief Tests for Story #172: Virtual Call Translation
 *
 * Tests core virtual call detection and method name resolution.
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/VirtualCallTranslator.h"
#include <vector>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

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

// Test fixture
class VirtualCallTranslatorTest : public ::testing::Test {
protected:
};

TEST_F(VirtualCallTranslatorTest, DetectVirtualCall) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        VirtualCallTranslator translator(Context, analyzer);

        // Find all method calls
        CallFinder finder;
        finder.TraverseDecl(Context.getTranslationUnitDecl());

        ASSERT_TRUE(!finder.Calls.empty()) << "Should find method call";

        // Check if it's virtual
        bool foundVirtualCall = false;
        for (auto* call : finder.Calls) {
            if (translator.isVirtualCall(call)) {
                foundVirtualCall = true;
                break;
            }
        }

        ASSERT_TRUE(foundVirtualCall) << "Should detect virtual call";
}

TEST_F(VirtualCallTranslatorTest, NonVirtualCallNotDetected) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        VirtualCallTranslator translator(Context, analyzer);

        CallFinder finder;
        finder.TraverseDecl(Context.getTranslationUnitDecl());

        ASSERT_TRUE(!finder.Calls.empty()) << "Should find method call";

        // Check that it's NOT virtual
        for (auto* call : finder.Calls) {
            ASSERT_TRUE(!translator.isVirtualCall(call)) << "Non-virtual call should not be detected as virtual";
        }
}
