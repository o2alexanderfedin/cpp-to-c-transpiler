/**
 * @file DestructorHandlerTest.cpp
 * @brief TDD tests for DestructorHandler
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (10 tests):
 * 1. EmptyDestructor - ~Counter() {}
 * 2. DestructorWithCleanupCode - ~Counter() { count = 0; }
 * 3. DestructorCallingMethods - ~Counter() { reset(); }
 * 4. DestructorAccessingMemberVariables - ~Counter() { this->count = 0; }
 * 5. DestructorWithResourceCleanup - ~FileHandle() { close(fd); }
 * 6. VirtualDestructor - virtual ~Base() {}
 * 7. DestructorWithMultipleOperations - Complex cleanup
 * 8. DestructorInMultipleClasses - Different destructors
 * 9. DestructorNaming - Verify ClassName_destroy naming
 * 10. DestructorThisParameter - Verify this parameter added
 */

#include "handlers/DestructorHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/DeclCXX.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class DestructorHandlerTest
 * @brief Test fixture for DestructorHandler
 *
 * Uses clang::tooling::buildASTFromCode for real AST contexts.
 */
class DestructorHandlerTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;
    DestructorHandler handler;

    void SetUp() override {
        // Create real AST contexts using minimal code
        cppAST = clang::tooling::buildASTFromCode("int dummy;");
        cAST = clang::tooling::buildASTFromCode("int dummy2;");

        ASSERT_NE(cppAST, nullptr) << "Failed to create C++ AST";
        ASSERT_NE(cAST, nullptr) << "Failed to create C AST";

        // Create builder and context
        builder = std::make_unique<clang::CNodeBuilder>(cAST->getASTContext());
        context = std::make_unique<HandlerContext>(
            cppAST->getASTContext(),
            cAST->getASTContext(),
            *builder
        );
    }

    void TearDown() override {
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Helper to parse C++ code and extract CXXDestructorDecl
     */
    clang::CXXDestructorDecl* getDestructorFromCode(const std::string& code) {
        // Parse the code
        auto ast = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(ast, nullptr) << "Failed to parse code";
        if (!ast) return nullptr;

        // Find the CXXDestructorDecl
        clang::CXXDestructorDecl* destructor = nullptr;
        auto& ctx = ast->getASTContext();
        auto* TU = ctx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                destructor = cxxRecord->getDestructor();
                if (destructor) break;
            }
        }

        EXPECT_NE(destructor, nullptr) << "No destructor found in code";
        return destructor;
    }
};

/**
 * Test 1: canHandle returns true for CXXDestructorDecl
 */
TEST_F(DestructorHandlerTest, CanHandleDestructor) {
    const char* code = R"(
        class Counter {
        public:
            ~Counter() {}
        };
    )";

    auto* destructor = getDestructorFromCode(code);
    ASSERT_NE(destructor, nullptr);

    EXPECT_TRUE(handler.canHandle(static_cast<const clang::Decl*>(destructor)));
}

/**
 * Test 2: canHandle returns false for non-destructor
 */
TEST_F(DestructorHandlerTest, CannotHandleNonDestructor) {
    const char* code = R"(
        void foo() {}
    )";

    auto ast = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(ast, nullptr);

    clang::FunctionDecl* func = nullptr;
    for (auto* decl : ast->getASTContext().getTranslationUnitDecl()->decls()) {
        if (auto* fd = llvm::dyn_cast<clang::FunctionDecl>(decl)) {
            func = fd;
            break;
        }
    }
    ASSERT_NE(func, nullptr);

    EXPECT_FALSE(handler.canHandle(static_cast<const clang::Decl*>(func)));
}

/**
 * Test 3: Empty destructor translates to ClassName_destroy with void body
 */
TEST_F(DestructorHandlerTest, EmptyDestructor) {
    const char* code = R"(
        class Counter {
        public:
            ~Counter() {}
        };
    )";

    auto* cppDestructor = getDestructorFromCode(code);
    ASSERT_NE(cppDestructor, nullptr);

    // Translate destructor
    clang::Decl* cDecl = handler.handleDecl(cppDestructor, *context);
    ASSERT_NE(cDecl, nullptr);

    // Verify it's a FunctionDecl
    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(cDecl);
    ASSERT_NE(cFunc, nullptr);

    // Verify name is Counter_destroy
    EXPECT_EQ(cFunc->getNameAsString(), "Counter_destroy");

    // Verify return type is void
    EXPECT_TRUE(cFunc->getReturnType()->isVoidType());

    // Verify has 1 parameter (this)
    EXPECT_EQ(cFunc->param_size(), 1u);

    // Verify parameter is struct Counter* this
    auto* thisParam = cFunc->getParamDecl(0);
    EXPECT_EQ(thisParam->getNameAsString(), "this");
    EXPECT_TRUE(thisParam->getType()->isPointerType());
}

/**
 * Test 4: Destructor with cleanup code
 */
TEST_F(DestructorHandlerTest, DestructorWithCleanupCode) {
    const char* code = R"(
        class Counter {
            int count;
        public:
            ~Counter() {
                count = 0;
            }
        };
    )";

    auto* cppDestructor = getDestructorFromCode(code);
    ASSERT_NE(cppDestructor, nullptr);

    // Translate destructor
    clang::Decl* cDecl = handler.handleDecl(cppDestructor, *context);
    ASSERT_NE(cDecl, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(cDecl);
    ASSERT_NE(cFunc, nullptr);

    // Verify name
    EXPECT_EQ(cFunc->getNameAsString(), "Counter_destroy");

    // Note: Body translation would be verified in integration tests
    // Unit test focuses on function signature
}

/**
 * Test 5: Destructor calling methods
 */
TEST_F(DestructorHandlerTest, DestructorCallingMethods) {
    const char* code = R"(
        class Counter {
            void reset();
        public:
            ~Counter() {
                reset();
            }
        };
    )";

    auto* cppDestructor = getDestructorFromCode(code);
    ASSERT_NE(cppDestructor, nullptr);

    clang::Decl* cDecl = handler.handleDecl(cppDestructor, *context);
    ASSERT_NE(cDecl, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(cDecl);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "Counter_destroy");
    EXPECT_EQ(cFunc->param_size(), 1u);
}

/**
 * Test 6: Destructor accessing member variables with this
 */
TEST_F(DestructorHandlerTest, DestructorAccessingMemberVariablesWithThis) {
    const char* code = R"(
        class Counter {
            int count;
        public:
            ~Counter() {
                this->count = 0;
            }
        };
    )";

    auto* cppDestructor = getDestructorFromCode(code);
    ASSERT_NE(cppDestructor, nullptr);

    clang::Decl* cDecl = handler.handleDecl(cppDestructor, *context);
    ASSERT_NE(cDecl, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(cDecl);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "Counter_destroy");
}

/**
 * Test 7: Virtual destructor (ignore virtual keyword)
 */
TEST_F(DestructorHandlerTest, VirtualDestructor) {
    const char* code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };
    )";

    auto* cppDestructor = getDestructorFromCode(code);
    ASSERT_NE(cppDestructor, nullptr);

    // Verify it's virtual in C++
    EXPECT_TRUE(cppDestructor->isVirtual());

    clang::Decl* cDecl = handler.handleDecl(cppDestructor, *context);
    ASSERT_NE(cDecl, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(cDecl);
    ASSERT_NE(cFunc, nullptr);

    // Virtual keyword is ignored - still translates to regular function
    EXPECT_EQ(cFunc->getNameAsString(), "Base_destroy");
    EXPECT_TRUE(cFunc->getReturnType()->isVoidType());
}

/**
 * Test 8: Destructor with multiple cleanup operations
 */
TEST_F(DestructorHandlerTest, DestructorWithMultipleOperations) {
    const char* code = R"(
        class FileHandle {
            int fd;
            char* buffer;
        public:
            ~FileHandle() {
                if (buffer) {
                    buffer = 0;
                }
                if (fd > 0) {
                    fd = -1;
                }
            }
        };
    )";

    auto* cppDestructor = getDestructorFromCode(code);
    ASSERT_NE(cppDestructor, nullptr);

    clang::Decl* cDecl = handler.handleDecl(cppDestructor, *context);
    ASSERT_NE(cDecl, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(cDecl);
    ASSERT_NE(cFunc, nullptr);

    EXPECT_EQ(cFunc->getNameAsString(), "FileHandle_destroy");
}

/**
 * Test 9: Multiple classes with different destructors
 */
TEST_F(DestructorHandlerTest, MultipleClassDestructors) {
    const char* code = R"(
        class Counter {
        public:
            ~Counter() {}
        };
        class Manager {
        public:
            ~Manager() {}
        };
    )";

    // Parse the code with both classes
    auto ast = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(ast, nullptr);

    // Find both destructors
    clang::CXXDestructorDecl* destructor1 = nullptr;
    clang::CXXDestructorDecl* destructor2 = nullptr;
    auto* TU = ast->getASTContext().getTranslationUnitDecl();

    for (auto* decl : TU->decls()) {
        if (auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
            if (cxxRecord->getNameAsString() == "Counter") {
                destructor1 = cxxRecord->getDestructor();
            } else if (cxxRecord->getNameAsString() == "Manager") {
                destructor2 = cxxRecord->getDestructor();
            }
        }
    }

    ASSERT_NE(destructor1, nullptr);
    ASSERT_NE(destructor2, nullptr);

    clang::Decl* cDecl1 = handler.handleDecl(destructor1, *context);
    clang::Decl* cDecl2 = handler.handleDecl(destructor2, *context);

    auto* cFunc1 = llvm::dyn_cast<clang::FunctionDecl>(cDecl1);
    auto* cFunc2 = llvm::dyn_cast<clang::FunctionDecl>(cDecl2);

    ASSERT_NE(cFunc1, nullptr);
    ASSERT_NE(cFunc2, nullptr);

    // Verify different names
    EXPECT_EQ(cFunc1->getNameAsString(), "Counter_destroy");
    EXPECT_EQ(cFunc2->getNameAsString(), "Manager_destroy");
}

/**
 * Test 10: Verify this parameter type is correct
 */
TEST_F(DestructorHandlerTest, ThisParameterType) {
    const char* code = R"(
        class MyClass {
        public:
            ~MyClass() {}
        };
    )";

    auto* cppDestructor = getDestructorFromCode(code);
    ASSERT_NE(cppDestructor, nullptr);

    clang::Decl* cDecl = handler.handleDecl(cppDestructor, *context);
    ASSERT_NE(cDecl, nullptr);

    auto* cFunc = llvm::dyn_cast<clang::FunctionDecl>(cDecl);
    ASSERT_NE(cFunc, nullptr);

    // Verify this parameter
    ASSERT_EQ(cFunc->param_size(), 1u);
    auto* thisParam = cFunc->getParamDecl(0);

    // Verify parameter name
    EXPECT_EQ(thisParam->getNameAsString(), "this");

    // Verify parameter type is pointer
    EXPECT_TRUE(thisParam->getType()->isPointerType());

    // Verify pointee type is struct
    auto ptrType = thisParam->getType()->getAs<clang::PointerType>();
    ASSERT_NE(ptrType, nullptr);

    // Note: Full struct type checking would be in integration tests
}
