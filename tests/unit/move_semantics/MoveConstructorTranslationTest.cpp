/**
 * @file MoveConstructorTranslationTest.cpp
 * @brief Tests for move constructor detection and translation to C code (Story #130)
 *
 * Test Strategy:
 * - Following TDD: Tests written first, implementation follows
 * - Tests cover detection using existing MoveSemanticTranslatorTest patterns
 * - Tests verify C code generation with proper pointer nullification
 * - Integration with existing constructor system
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "../../../include/MoveConstructorTranslator.h"
#include <cassert>
#include <string>
#include <vector>

using namespace clang;

// Test helper to build AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const char *code) {
    return tooling::buildASTFromCode(code);
}

// Test helper macros
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

// Helper visitor to find move constructors
class MoveConstructorFinder : public RecursiveASTVisitor<MoveConstructorFinder> {
public:
    std::vector<CXXConstructorDecl*> moveConstructors;

    bool VisitCXXConstructorDecl(CXXConstructorDecl *D) {
        if (D->isMoveConstructor()) {
            moveConstructors.push_back(D);
        }
        return true;
    }
};

// ============================================================================
// Test 1: Simple move constructor generates correct C function
// ============================================================================

// Test fixture
class MoveConstructorTranslationTest : public ::testing::Test {
protected:
};

TEST_F(MoveConstructorTranslationTest, simple_move_constructor_c_generation) {
    const char *code = R"(
            class Widget {
                int* data;
            public:
                Widget(Widget&& other) : data(other.data) {
                    other.data = nullptr;
                }
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        MoveConstructorFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(finder.moveConstructors.size() == 1) << "Expected exactly one move constructor";

        CXXConstructorDecl *MoveCtor = finder.moveConstructors[0];
        MoveConstructorTranslator translator(AST->getASTContext());

        // Test detection
        ASSERT_TRUE(translator.isMoveConstructor(MoveCtor)) << "Should detect move constructor";

        // Test C code generation
        std::string cCode = translator.generateMoveConstructor(MoveCtor);
        ASSERT_TRUE(!cCode.empty()) << "Should generate non-empty C code";

        // Verify signature: void Widget_move_construct(struct Widget *dest, struct Widget *src)
        ASSERT_TRUE(cCode.find("Widget_move_construct") != std::string::npos) << "Should contain move constructor function name";
        ASSERT_TRUE(cCode.find("struct Widget *dest") != std::string::npos) << "Should have dest parameter";
        ASSERT_TRUE(cCode.find("struct Widget *src") != std::string::npos) << "Should have src parameter";

        // Verify pointer nullification
        ASSERT_TRUE(cCode.find("src->data = NULL") != std::string::npos ||
               cCode.find("src->data = nullptr") != std::string::npos ||
               cCode.find("src->data = 0") != std::string::npos) << "Should nullify pointer member in source";
}

TEST_F(MoveConstructorTranslationTest, move_multiple_pointers_nullification) {
    const char *code = R"(
            class Resource {
                int* buffer;
                char* name;
                double* metrics;
            public:
                Resource(Resource&& other)
                    : buffer(other.buffer), name(other.name), metrics(other.metrics) {
                    other.buffer = nullptr;
                    other.name = nullptr;
                    other.metrics = nullptr;
                }
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        MoveConstructorFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(finder.moveConstructors.size() == 1) << "Expected exactly one move constructor";

        CXXConstructorDecl *MoveCtor = finder.moveConstructors[0];
        MoveConstructorTranslator translator(AST->getASTContext());

        std::string cCode = translator.generateMoveConstructor(MoveCtor);
        ASSERT_TRUE(!cCode.empty()) << "Should generate non-empty C code";

        // Verify all three pointer members are copied and then nullified
        ASSERT_TRUE(cCode.find("dest->buffer = src->buffer") != std::string::npos) << "Should copy buffer pointer";
        ASSERT_TRUE(cCode.find("dest->name = src->name") != std::string::npos) << "Should copy name pointer";
        ASSERT_TRUE(cCode.find("dest->metrics = src->metrics") != std::string::npos) << "Should copy metrics pointer";

        // Verify nullification of all pointers
        int nullifications = 0;
        size_t pos = 0;
        while ((pos = cCode.find("= NULL", pos)) != std::string::npos ||
               (pos = cCode.find("= nullptr", pos)) != std::string::npos ||
               (pos = cCode.find("= 0", pos)) != std::string::npos) {
            nullifications++;
            pos++;
        }
        ASSERT_TRUE(nullifications >= 3) << "Should nullify at least 3 pointer members";
}

TEST_F(MoveConstructorTranslationTest, move_non_pointer_members_copied) {
    const char *code = R"(
            class Data {
                int* ptr;
                int size;
                bool valid;
            public:
                Data(Data&& other)
                    : ptr(other.ptr), size(other.size), valid(other.valid) {
                    other.ptr = nullptr;
                    other.size = 0;
                    other.valid = false;
                }
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        MoveConstructorFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(finder.moveConstructors.size() == 1) << "Expected exactly one move constructor";

        CXXConstructorDecl *MoveCtor = finder.moveConstructors[0];
        MoveConstructorTranslator translator(AST->getASTContext());

        std::string cCode = translator.generateMoveConstructor(MoveCtor);
        ASSERT_TRUE(!cCode.empty()) << "Should generate non-empty C code";

        // Verify pointer copied and nullified
        ASSERT_TRUE(cCode.find("dest->ptr = src->ptr") != std::string::npos) << "Should copy ptr";
        ASSERT_TRUE(cCode.find("src->ptr") != std::string::npos &&
               (cCode.find("NULL") != std::string::npos || cCode.find("nullptr") != std::string::npos)) << "Should nullify ptr";

        // Verify non-pointer members copied
        ASSERT_TRUE(cCode.find("dest->size = src->size") != std::string::npos) << "Should copy size member";
        ASSERT_TRUE(cCode.find("dest->valid = src->valid") != std::string::npos) << "Should copy valid member";
}

TEST_F(MoveConstructorTranslationTest, move_with_member_initializer_list) {
    const char *code = R"(
            class Container {
                int* data;
                int capacity;
            public:
                Container(Container&& other) noexcept
                    : data(other.data), capacity(other.capacity) {
                    other.data = nullptr;
                    other.capacity = 0;
                }
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        MoveConstructorFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(finder.moveConstructors.size() == 1) << "Expected exactly one move constructor";

        CXXConstructorDecl *MoveCtor = finder.moveConstructors[0];
        MoveConstructorTranslator translator(AST->getASTContext());

        std::string cCode = translator.generateMoveConstructor(MoveCtor);
        ASSERT_TRUE(!cCode.empty()) << "Should generate non-empty C code";

        // Verify member initialization translated to assignment
        ASSERT_TRUE(cCode.find("dest->data = src->data") != std::string::npos) << "Should translate data initialization";
        ASSERT_TRUE(cCode.find("dest->capacity = src->capacity") != std::string::npos) << "Should translate capacity initialization";

        // Verify source reset
        ASSERT_TRUE(cCode.find("src->data") != std::string::npos &&
               (cCode.find("NULL") != std::string::npos || cCode.find("nullptr") != std::string::npos)) << "Should reset src->data";
        ASSERT_TRUE(cCode.find("src->capacity = 0") != std::string::npos) << "Should reset src->capacity";
}

TEST_F(MoveConstructorTranslationTest, integration_with_constructor_system) {
    const char *code = R"(
            class Widget {
                int* data;
            public:
                Widget() : data(new int(0)) {}
                Widget(const Widget& other) : data(new int(*other.data)) {}
                Widget(Widget&& other) : data(other.data) {
                    other.data = nullptr;
                }
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        MoveConstructorFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(finder.moveConstructors.size() == 1) << "Expected exactly one move constructor";

        CXXConstructorDecl *MoveCtor = finder.moveConstructors[0];
        MoveConstructorTranslator translator(AST->getASTContext());

        // Should detect and translate without affecting other constructors
        ASSERT_TRUE(translator.isMoveConstructor(MoveCtor)) << "Should detect move constructor";

        std::string cCode = translator.generateMoveConstructor(MoveCtor);
        ASSERT_TRUE(!cCode.empty()) << "Should generate C code";

        // Should follow existing naming convention
        ASSERT_TRUE(cCode.find("Widget_") != std::string::npos) << "Should follow class name prefix convention";
}

TEST_F(MoveConstructorTranslationTest, move_not_copy_constructor) {
    const char *code = R"(
            class Widget {
                int* data;
            public:
                Widget(const Widget& other) : data(new int(*other.data)) {}  // Copy
                Widget(Widget&& other) : data(other.data) {                  // Move
                    other.data = nullptr;
                }
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        MoveConstructorFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Should find only the move constructor, not the copy constructor
        ASSERT_TRUE(finder.moveConstructors.size() == 1) << "Should find exactly one move constructor";

        CXXConstructorDecl *MoveCtor = finder.moveConstructors[0];
        MoveConstructorTranslator translator(AST->getASTContext());

        ASSERT_TRUE(translator.isMoveConstructor(MoveCtor)) << "Should be a move constructor";

        // Verify it's the move, not copy
        ASSERT_TRUE(MoveCtor->getNumParams() == 1) << "Move constructor has 1 parameter";
        QualType paramType = MoveCtor->getParamDecl(0)->getType();
        ASSERT_TRUE(paramType->isRValueReferenceType()) << "Parameter should be rvalue reference";
}

TEST_F(MoveConstructorTranslationTest, valid_function_signature) {
    const char *code = R"(
            class MyClass {
                int* ptr;
            public:
                MyClass(MyClass&& other) noexcept : ptr(other.ptr) {
                    other.ptr = nullptr;
                }
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        MoveConstructorFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(finder.moveConstructors.size() == 1) << "Expected move constructor";

        CXXConstructorDecl *MoveCtor = finder.moveConstructors[0];
        MoveConstructorTranslator translator(AST->getASTContext());

        std::string cCode = translator.generateMoveConstructor(MoveCtor);
        ASSERT_TRUE(!cCode.empty()) << "Should generate C code";

        // Verify function signature components
        ASSERT_TRUE(cCode.find("void") != std::string::npos) << "Should return void";
        ASSERT_TRUE(cCode.find("MyClass_") != std::string::npos) << "Should have class name prefix";
        ASSERT_TRUE(cCode.find("struct MyClass *dest") != std::string::npos) << "Should have dest param";
        ASSERT_TRUE(cCode.find("struct MyClass *src") != std::string::npos) << "Should have src param";
        ASSERT_TRUE(cCode.find("{") != std::string::npos) << "Should have function body";
        ASSERT_TRUE(cCode.find("}") != std::string::npos) << "Should close function body";
}
