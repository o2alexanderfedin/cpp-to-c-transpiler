/**
 * @file ExpressionHandlerTest_This.cpp
 * @brief TDD tests for ExpressionHandler - CXXThisExpr translation
 *
 * Phase 44 Task 6: This Expression Handler
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (10 tests):
 * 1. ThisInMethodBody - Basic 'this' usage in method body
 * 2. ThisFieldAccess - this->field access
 * 3. ThisMethodCall - this->method() call
 * 4. ReturnThis - Return 'this' from method (for chaining)
 * 5. ThisInConstructor - 'this' in constructor body
 * 6. ThisInDestructor - 'this' in destructor body
 * 7. ThisInConstMethod - 'this' in const method
 * 8. ThisPointerArithmetic - Pointer arithmetic with 'this'
 * 9. ThisComparison - Compare 'this' with another pointer
 * 10. MultipleThisUsages - Multiple uses of 'this' in same method
 */

#include "helpers/UnitTestHelper.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ExpressionHandlerThisTest
 * @brief Test fixture for CXXThisExpr translation
 *
 * Uses real AST contexts to test translation of C++ 'this' keyword
 * to C DeclRefExpr referring to the 'this' parameter.
 */
class ExpressionHandlerThisTest : public ::testing::Test {
protected:
    UnitTestContext ctx;

    void SetUp() override {
        ctx = createUnitTestContext();
    }
/**
     * @brief Extract CXXThisExpr from C++ code
     * @param code C++ code containing 'this'
     * @return Extracted CXXThisExpr
     */
    const clang::CXXThisExpr* extractThisExpr(const std::string& code) {
        class ThisExprVisitor : public clang::RecursiveASTVisitor<ThisExprVisitor> {
        public:
            const clang::CXXThisExpr* foundThis = nullptr;

            bool VisitCXXThisExpr(clang::CXXThisExpr* E) {
                if (!foundThis) {
                    foundThis = E;
                }
                return true;
            }
        };

        cppAST = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(cppAST, nullptr) << "Failed to parse code: " << code;

        ThisExprVisitor visitor;
        visitor.TraverseDecl(cppAST->getASTContext().getTranslationUnitDecl());

        EXPECT_NE(visitor.foundThis, nullptr) << "No CXXThisExpr found in code: " << code;
        return visitor.foundThis;
    }

    /**
     * @brief Create a C function with 'this' parameter
     * @param className Name of the class (for type)
     * @param funcName Name of the function
     * @return FunctionDecl with 'this' as first parameter
     */
    clang::FunctionDecl* createFunctionWithThis(
        const std::string& className,
        const std::string& funcName
    ) {
        clang::ASTContext& cCtx = cAST->getASTContext();

        // Create identifier for class name
        clang::IdentifierInfo& classII = cCtx.Idents.get(className);

        // Create forward declaration for struct
        clang::RecordDecl* classRecord = clang::RecordDecl::Create(
            cCtx,
            clang::TagTypeKind::Struct,
            cCtx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            &classII
        );

        // Create struct type
        clang::QualType structType = cCtx.getRecordType(classRecord);

        // Create pointer to struct type
        clang::QualType pointerType = cCtx.getPointerType(structType);

        // Create 'this' parameter declaration
        clang::IdentifierInfo& thisII = cCtx.Idents.get("this");

        clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
            cCtx,
            nullptr,
            clang::SourceLocation(),
            clang::SourceLocation(),
            &thisII,
            pointerType,
            cCtx.getTrivialTypeSourceInfo(pointerType),
            clang::SC_None,
            nullptr
        );

        // Create function declaration
        clang::IdentifierInfo& funcII = cCtx.Idents.get(funcName);
        clang::DeclarationName funcDeclName(&funcII);

        // Create function type (void return, one parameter: this)
        llvm::SmallVector<clang::QualType, 1> paramTypes;
        paramTypes.push_back(pointerType);

        clang::FunctionProtoType::ExtProtoInfo EPI;
        clang::QualType funcType = cCtx.getFunctionType(
            cCtx.VoidTy,
            paramTypes,
            EPI
        );

        clang::FunctionDecl* funcDecl = clang::FunctionDecl::Create(
            cCtx,
            cCtx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            funcDeclName,
            funcType,
            cCtx.getTrivialTypeSourceInfo(funcType),
            clang::SC_None
        );

        // Set 'this' parameter
        funcDecl->setParams({thisParam});

        return funcDecl;
    }
};

// ============================================================================
// Test 1: ThisInMethodBody
// ============================================================================

TEST_F(ExpressionHandlerThisTest, ThisInMethodBody) {
    // C++ code with 'this' in method body
    const char* cppCode = R"(
        class Counter {
        public:
            void* getThis() {
                return this;
            }
        };
    )";

    const clang::CXXThisExpr* cppThis = extractThisExpr(cppCode);
    ASSERT_NE(cppThis, nullptr);

    // Create C function with 'this' parameter
    clang::FunctionDecl* funcDecl = createFunctionWithThis("Counter", "Counter_getThis");

    // Set current function in context
    context->setCurrentFunction(funcDecl);

    // Translate using ExpressionHandler
    ExpressionHandler handler;
    clang::Expr* cExpr = handler.handleExpr(cppThis, ctx);

    // Verify translation
    ASSERT_NE(cExpr, nullptr) << "Translation should succeed";

    // Should be DeclRefExpr
    auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(cExpr);
    ASSERT_NE(DRE, nullptr) << "Should translate to DeclRefExpr";

    // Should refer to 'this' parameter
    const clang::ValueDecl* decl = DRE->getDecl();
    ASSERT_NE(decl, nullptr);
    EXPECT_EQ(decl->getNameAsString(), "this");

    // Should have pointer type
    EXPECT_TRUE(DRE->getType()->isPointerType());
}

// ============================================================================
// Test 2: ThisFieldAccess
// ============================================================================

TEST_F(ExpressionHandlerThisTest, ThisFieldAccess) {
    // C++ code with this->field access
    const char* cppCode = R"(
        class Counter {
        public:
            int count;
            int getCount() {
                return this->count;
            }
        };
    )";

    const clang::CXXThisExpr* cppThis = extractThisExpr(cppCode);
    ASSERT_NE(cppThis, nullptr);

    // Create C function with 'this' parameter
    clang::FunctionDecl* funcDecl = createFunctionWithThis("Counter", "Counter_method");

    // Set current function in context
    context->setCurrentFunction(funcDecl);

    // Translate
    ExpressionHandler handler;
    clang::Expr* cExpr = handler.handleExpr(cppThis, ctx);

    // Verify
    ASSERT_NE(cExpr, nullptr);
    auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(cExpr);
    ASSERT_NE(DRE, nullptr);
    EXPECT_EQ(DRE->getDecl()->getNameAsString(), "this");
}

// ============================================================================
// Test 3: ThisMethodCall
// ============================================================================

TEST_F(ExpressionHandlerThisTest, ThisMethodCall) {
    // C++ code with this->method() call
    const char* cppCode = R"(
        class Counter {
        public:
            void increment();
            void reset() {
                this->increment();
            }
        };
    )";

    const clang::CXXThisExpr* cppThis = extractThisExpr(cppCode);
    ASSERT_NE(cppThis, nullptr);

    // Create C function with 'this' parameter
    clang::FunctionDecl* funcDecl = createFunctionWithThis("Counter", "Counter_method");

    // Set current function in context
    context->setCurrentFunction(funcDecl);

    // Translate
    ExpressionHandler handler;
    clang::Expr* cExpr = handler.handleExpr(cppThis, ctx);

    // Verify
    ASSERT_NE(cExpr, nullptr);
    auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(cExpr);
    ASSERT_NE(DRE, nullptr);
    EXPECT_EQ(DRE->getDecl()->getNameAsString(), "this");
}

// ============================================================================
// Test 4: ReturnThis
// ============================================================================

TEST_F(ExpressionHandlerThisTest, ReturnThis) {
    // C++ code returning 'this' for method chaining
    const char* cppCode = R"(
        class Counter {
        public:
            Counter* chain() {
                return this;
            }
        };
    )";

    const clang::CXXThisExpr* cppThis = extractThisExpr(cppCode);
    ASSERT_NE(cppThis, nullptr);

    // Create C function with 'this' parameter
    clang::FunctionDecl* funcDecl = createFunctionWithThis("Counter", "Counter_method");

    // Set current function in context
    context->setCurrentFunction(funcDecl);

    // Translate
    ExpressionHandler handler;
    clang::Expr* cExpr = handler.handleExpr(cppThis, ctx);

    // Verify
    ASSERT_NE(cExpr, nullptr);
    auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(cExpr);
    ASSERT_NE(DRE, nullptr);
    EXPECT_EQ(DRE->getDecl()->getNameAsString(), "this");
    EXPECT_TRUE(DRE->getType()->isPointerType());
}

// ============================================================================
// Test 5: ThisInConstructor
// ============================================================================

TEST_F(ExpressionHandlerThisTest, ThisInConstructor) {
    // C++ code with 'this' in constructor
    const char* cppCode = R"(
        class Counter {
        public:
            int* ptr;
            Counter() {
                ptr = reinterpret_cast<int*>(this);
            }
        };
    )";

    const clang::CXXThisExpr* cppThis = extractThisExpr(cppCode);
    ASSERT_NE(cppThis, nullptr);

    // Create C function with 'this' parameter
    clang::FunctionDecl* funcDecl = createFunctionWithThis("Counter", "Counter_method");

    // Set current function in context
    context->setCurrentFunction(funcDecl);

    // Translate
    ExpressionHandler handler;
    clang::Expr* cExpr = handler.handleExpr(cppThis, ctx);

    // Verify
    ASSERT_NE(cExpr, nullptr);
    auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(cExpr);
    ASSERT_NE(DRE, nullptr);
    EXPECT_EQ(DRE->getDecl()->getNameAsString(), "this");
}

// ============================================================================
// Test 6: ThisInDestructor
// ============================================================================

TEST_F(ExpressionHandlerThisTest, ThisInDestructor) {
    // C++ code with 'this' in destructor
    const char* cppCode = R"(
        class Counter {
        public:
            ~Counter() {
                void* ptr = this;
            }
        };
    )";

    const clang::CXXThisExpr* cppThis = extractThisExpr(cppCode);
    ASSERT_NE(cppThis, nullptr);

    // Create C function with 'this' parameter
    clang::FunctionDecl* funcDecl = createFunctionWithThis("Counter", "Counter_method");

    // Set current function in context
    context->setCurrentFunction(funcDecl);

    // Translate
    ExpressionHandler handler;
    clang::Expr* cExpr = handler.handleExpr(cppThis, ctx);

    // Verify
    ASSERT_NE(cExpr, nullptr);
    auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(cExpr);
    ASSERT_NE(DRE, nullptr);
    EXPECT_EQ(DRE->getDecl()->getNameAsString(), "this");
}

// ============================================================================
// Test 7: ThisInConstMethod
// ============================================================================

TEST_F(ExpressionHandlerThisTest, ThisInConstMethod) {
    // C++ code with 'this' in const method
    const char* cppCode = R"(
        class Counter {
        public:
            const Counter* getConstThis() const {
                return this;
            }
        };
    )";

    const clang::CXXThisExpr* cppThis = extractThisExpr(cppCode);
    ASSERT_NE(cppThis, nullptr);

    // Create C function with 'this' parameter (for const method, type should be const)
    clang::FunctionDecl* funcDecl = createFunctionWithThis("Counter", "Counter_getConstThis");

    // Set current function in context
    context->setCurrentFunction(funcDecl);

    // Translate
    ExpressionHandler handler;
    clang::Expr* cExpr = handler.handleExpr(cppThis, ctx);

    // Verify
    ASSERT_NE(cExpr, nullptr);
    auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(cExpr);
    ASSERT_NE(DRE, nullptr);
    EXPECT_EQ(DRE->getDecl()->getNameAsString(), "this");
    EXPECT_TRUE(DRE->getType()->isPointerType());
}

// ============================================================================
// Test 8: ThisPointerArithmetic
// ============================================================================

TEST_F(ExpressionHandlerThisTest, ThisPointerArithmetic) {
    // C++ code with pointer arithmetic on 'this'
    const char* cppCode = R"(
        class Counter {
        public:
            Counter* getNext() {
                return this + 1;
            }
        };
    )";

    const clang::CXXThisExpr* cppThis = extractThisExpr(cppCode);
    ASSERT_NE(cppThis, nullptr);

    // Create C function with 'this' parameter
    clang::FunctionDecl* funcDecl = createFunctionWithThis("Counter", "Counter_method");

    // Set current function in context
    context->setCurrentFunction(funcDecl);

    // Translate
    ExpressionHandler handler;
    clang::Expr* cExpr = handler.handleExpr(cppThis, ctx);

    // Verify
    ASSERT_NE(cExpr, nullptr);
    auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(cExpr);
    ASSERT_NE(DRE, nullptr);
    EXPECT_EQ(DRE->getDecl()->getNameAsString(), "this");
}

// ============================================================================
// Test 9: ThisComparison
// ============================================================================

TEST_F(ExpressionHandlerThisTest, ThisComparison) {
    // C++ code comparing 'this' with another pointer
    const char* cppCode = R"(
        class Counter {
        public:
            bool isSame(Counter* other) {
                return this == other;
            }
        };
    )";

    const clang::CXXThisExpr* cppThis = extractThisExpr(cppCode);
    ASSERT_NE(cppThis, nullptr);

    // Create C function with 'this' parameter
    clang::FunctionDecl* funcDecl = createFunctionWithThis("Counter", "Counter_method");

    // Set current function in context
    context->setCurrentFunction(funcDecl);

    // Translate
    ExpressionHandler handler;
    clang::Expr* cExpr = handler.handleExpr(cppThis, ctx);

    // Verify
    ASSERT_NE(cExpr, nullptr);
    auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(cExpr);
    ASSERT_NE(DRE, nullptr);
    EXPECT_EQ(DRE->getDecl()->getNameAsString(), "this");
}

// ============================================================================
// Test 10: MultipleThisUsages
// ============================================================================

TEST_F(ExpressionHandlerThisTest, MultipleThisUsages) {
    // C++ code with multiple uses of 'this' in same method
    const char* cppCode = R"(
        class Counter {
        public:
            int value;
            bool compare() {
                return this->value == this->value;
            }
        };
    )";

    // Extract first 'this' expression
    const clang::CXXThisExpr* cppThis = extractThisExpr(cppCode);
    ASSERT_NE(cppThis, nullptr);

    // Create C function with 'this' parameter
    clang::FunctionDecl* funcDecl = createFunctionWithThis("Counter", "Counter_method");

    // Set current function in context
    context->setCurrentFunction(funcDecl);

    // Translate
    ExpressionHandler handler;
    clang::Expr* cExpr = handler.handleExpr(cppThis, ctx);

    // Verify
    ASSERT_NE(cExpr, nullptr);
    auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(cExpr);
    ASSERT_NE(DRE, nullptr);
    EXPECT_EQ(DRE->getDecl()->getNameAsString(), "this");
}

// ============================================================================
// Test 11: ThisTypeVerification
// ============================================================================

TEST_F(ExpressionHandlerThisTest, ThisTypeVerification) {
    // Verify that translated 'this' has correct type
    const char* cppCode = R"(
        class MyClass {
        public:
            void method() {
                MyClass* ptr = this;
            }
        };
    )";

    const clang::CXXThisExpr* cppThis = extractThisExpr(cppCode);
    ASSERT_NE(cppThis, nullptr);

    // Create C function with 'this' parameter
    clang::FunctionDecl* funcDecl = createFunctionWithThis("MyClass", "MyClass_method");

    // Set current function in context
    context->setCurrentFunction(funcDecl);

    // Translate
    ExpressionHandler handler;
    clang::Expr* cExpr = handler.handleExpr(cppThis, ctx);

    // Verify
    ASSERT_NE(cExpr, nullptr);
    auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(cExpr);
    ASSERT_NE(DRE, nullptr);

    // Check type is pointer
    clang::QualType type = DRE->getType();
    EXPECT_TRUE(type->isPointerType());

    // Check pointee is struct
    if (type->isPointerType()) {
        clang::QualType pointeeType = type->getPointeeType();
        EXPECT_TRUE(pointeeType->isStructureType());
    }
}
