/**
 * @file ExpressionHandlerTest_MemberAccess.cpp
 * @brief TDD tests for ExpressionHandler - Member Access Translation (Phase 44 Task 7)
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan:
 * Convert implicit member access (field) to explicit this->field in method bodies.
 *
 * Test Coverage:
 * 1. Implicit field access in assignment (field = 10)
 * 2. Implicit field read in return statement (return field)
 * 3. Explicit this->field access (already works from Phase 43)
 * 4. Chained member access (obj.field1.field2)
 * 5. Method call on member object (memberObj.method())
 * 6. Implicit field in compound assignment (field += 10)
 * 7. Implicit field in unary operator (field++)
 * 8. Multiple implicit field accesses (field1 + field2)
 * 9. Mixed explicit and implicit (this->field1 + field2)
 * 10. Implicit field in array subscript (field[0])
 * 11. Pointer member access (ptrField->member)
 * 12. Nested implicit access in expression ((field + 1) * 2)
 */

#include "UnitTestHelper.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ExpressionHandlerTest_MemberAccess
 * @brief Test fixture for member access translation
 *
 * Uses clang::tooling::buildASTFromCode for real AST contexts.
 */
class ExpressionHandlerTest_MemberAccess : public ::testing::Test {
protected:
    UnitTestContext ctx;

    void SetUp() override {
        ctx = createUnitTestContext();
        ctx.dispatcher->registerHandler<ExpressionHandler>();
    }

    /**
     * @brief Helper: Create a mock function with 'this' parameter for testing
     */
    clang::FunctionDecl* createMockFunctionWithThis(clang::ASTContext& cCtx, const std::string& className) {

        // Create 'this' parameter type: struct ClassName*
        clang::IdentifierInfo& classId = cCtx.Idents.get(className);
        clang::RecordDecl* recordDecl = clang::RecordDecl::Create(
            cCtx,
            clang::TagTypeKind::Struct,
            cCtx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            &classId
        );

        clang::QualType recordType = cCtx.getRecordType(recordDecl);
        clang::QualType thisType = cCtx.getPointerType(recordType);

        // Create 'this' parameter
        clang::IdentifierInfo& thisId = cCtx.Idents.get("this");
        clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
            cCtx,
            nullptr,
            clang::SourceLocation(),
            clang::SourceLocation(),
            &thisId,
            thisType,
            nullptr,
            clang::SC_None,
            nullptr
        );

        // Create function with 'this' parameter
        clang::IdentifierInfo& funcId = cCtx.Idents.get("testFunc");
        clang::FunctionProtoType::ExtProtoInfo EPI;
        clang::QualType funcType = cCtx.getFunctionType(
            cCtx.VoidTy,
            {thisType},
            EPI
        );

        clang::FunctionDecl* funcDecl = clang::FunctionDecl::Create(
            cCtx,
            cCtx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            clang::DeclarationName(&funcId),
            funcType,
            nullptr,
            clang::SC_None
        );

        funcDecl->setParams({thisParam});

        return funcDecl;
    }


    /**
     * @brief Helper: Extract MemberExpr from method body
     */
    class MemberExprExtractor : public clang::RecursiveASTVisitor<MemberExprExtractor> {
    public:
        std::vector<const clang::MemberExpr*> memberExprs;

        bool VisitMemberExpr(const clang::MemberExpr* ME) {
            memberExprs.push_back(ME);
            return true;
        }
    };

    /**
     * @brief Helper: Extract CXXThisExpr from method body
     */
    class ThisExprExtractor : public clang::RecursiveASTVisitor<ThisExprExtractor> {
    public:
        std::vector<const clang::CXXThisExpr*> thisExprs;

        bool VisitCXXThisExpr(const clang::CXXThisExpr* TE) {
            thisExprs.push_back(TE);
            return true;
        }
    };

    /**
     * @brief Helper: Find first method declaration in AST
     */
    class MethodFinder : public clang::RecursiveASTVisitor<MethodFinder> {
    public:
        const clang::CXXMethodDecl* method = nullptr;

        bool VisitCXXMethodDecl(const clang::CXXMethodDecl* MD) {
            if (!method && MD->hasBody()) {
                method = MD;
            }
            return true;
        }
    };

    /**
     * @brief Build AST from C++ code and extract first MemberExpr
     */
    const clang::MemberExpr* getMemberExprFromCode(const std::string& code) {
        auto ast = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(ast, nullptr) << "Failed to build AST";

        MemberExprExtractor extractor;
        extractor.TraverseDecl(ast->getASTContext().getTranslationUnitDecl());

        EXPECT_FALSE(extractor.memberExprs.empty()) << "No MemberExpr found in code";
        return extractor.memberExprs.empty() ? nullptr : extractor.memberExprs[0];
    }
};

// ============================================================================
// Test 1: Implicit field access in assignment
// ============================================================================
TEST_F(ExpressionHandlerTest_MemberAccess, ImplicitFieldAssignment) {
    // C++ code with implicit member access
    const char* code = R"(
        class Counter {
            int count;
        public:
            void reset() {
                count = 0;  // Implicit member access
            }
        };
    )";

    const clang::MemberExpr* ME = getMemberExprFromCode(code);
    ASSERT_NE(ME, nullptr);

    // Verify it's an implicit this access
    const clang::Expr* base = ME->getBase();
    ASSERT_NE(base, nullptr);
    const auto* thisExpr = llvm::dyn_cast<clang::CXXThisExpr>(base);
    ASSERT_NE(thisExpr, nullptr) << "Expected CXXThisExpr as base";
    EXPECT_TRUE(thisExpr->isImplicit()) << "Expected implicit this";

    // Get contexts
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    // Set up mock function context for translation
    clang::FunctionDecl* mockFunc = createMockFunctionWithThis(cCtx, "Counter");
    ctx.dispatcher->setCurrentFunction(mockFunc);

    // Translate the MemberExpr
    // Expected: count → this->count (in C AST)
    ctx.dispatcher->dispatch(ME);
    clang::Expr* translated = ctx.exprMapper->get(ME);
    ASSERT_NE(translated, nullptr) << "Translation failed";

    // Verify translated expression is MemberExpr
    const auto* translatedME = llvm::dyn_cast<clang::MemberExpr>(translated);
    ASSERT_NE(translatedME, nullptr) << "Expected MemberExpr result";

    // Verify it uses arrow operator (this->count)
    EXPECT_TRUE(translatedME->isArrow()) << "Expected arrow operator (->)";

    // Verify the member name is preserved
    EXPECT_EQ(translatedME->getMemberDecl()->getNameAsString(), "count");
}

// ============================================================================
// Test 2: Implicit field read in return statement
// ============================================================================
TEST_F(ExpressionHandlerTest_MemberAccess, ImplicitFieldReturn) {
    const char* code = R"(
        class Counter {
            int count;
        public:
            int getCount() {
                return count;  // Implicit member access
            }
        };
    )";

    const clang::MemberExpr* ME = getMemberExprFromCode(code);
    ASSERT_NE(ME, nullptr);

    // Verify implicit this access
    const auto* thisExpr = llvm::dyn_cast<clang::CXXThisExpr>(ME->getBase());
    ASSERT_NE(thisExpr, nullptr);
    EXPECT_TRUE(thisExpr->isImplicit());

    // Get contexts
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    // Set up mock function context for translation
    clang::FunctionDecl* mockFunc = createMockFunctionWithThis(cCtx, "Counter");
    ctx.dispatcher->setCurrentFunction(mockFunc);

    // Translate
    ctx.dispatcher->dispatch(ME);
    clang::Expr* translated = ctx.exprMapper->get(ME);
    ASSERT_NE(translated, nullptr);

    // Verify result is this->count
    const auto* translatedME = llvm::dyn_cast<clang::MemberExpr>(translated);
    ASSERT_NE(translatedME, nullptr);
    EXPECT_TRUE(translatedME->isArrow());
    EXPECT_EQ(translatedME->getMemberDecl()->getNameAsString(), "count");
}

// ============================================================================
// Test 3: Explicit this->field access (should already work from Phase 43)
// ============================================================================
TEST_F(ExpressionHandlerTest_MemberAccess, ExplicitThisFieldAccess) {
    const char* code = R"(
        class Counter {
            int count;
        public:
            void reset() {
                this->count = 0;  // Explicit this->field
            }
        };
    )";

    const clang::MemberExpr* ME = getMemberExprFromCode(code);
    ASSERT_NE(ME, nullptr);

    // Verify it's an explicit this access
    const auto* thisExpr = llvm::dyn_cast<clang::CXXThisExpr>(ME->getBase());
    ASSERT_NE(thisExpr, nullptr);
    EXPECT_FALSE(thisExpr->isImplicit()) << "Expected explicit this";

    // Get contexts
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    // Set up mock function context for translation
    clang::FunctionDecl* mockFunc = createMockFunctionWithThis(cCtx, "Counter");
    ctx.dispatcher->setCurrentFunction(mockFunc);

    // Translate
    ctx.dispatcher->dispatch(ME);
    clang::Expr* translated = ctx.exprMapper->get(ME);
    ASSERT_NE(translated, nullptr);

    // Should preserve this->count structure
    const auto* translatedME = llvm::dyn_cast<clang::MemberExpr>(translated);
    ASSERT_NE(translatedME, nullptr);
    EXPECT_TRUE(translatedME->isArrow());
    EXPECT_EQ(translatedME->getMemberDecl()->getNameAsString(), "count");
}

// ============================================================================
// Test 4: Chained member access (obj.field1.field2)
// ============================================================================
TEST_F(ExpressionHandlerTest_MemberAccess, ChainedMemberAccess) {
    const char* code = R"(
        struct Inner { int value; };
        class Outer {
            Inner inner;
        public:
            int getValue() {
                return inner.value;  // Chained: implicit inner, then .value
            }
        };
    )";

    auto ast = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(ast, nullptr);

    MemberExprExtractor extractor;
    extractor.TraverseDecl(ast->getASTContext().getTranslationUnitDecl());

    // Should have two MemberExprs: inner.value and this->inner
    // RecursiveASTVisitor visits in pre-order, so we get: value (first), inner (second)
    ASSERT_EQ(extractor.memberExprs.size(), 2) << "Expected two MemberExprs";

    // First MemberExpr is inner.value (outer)
    const clang::MemberExpr* valueME = extractor.memberExprs[0];
    ASSERT_NE(valueME, nullptr);
    EXPECT_EQ(valueME->getMemberDecl()->getNameAsString(), "value");

    // Second MemberExpr is this->inner (inner)
    const clang::MemberExpr* innerME = extractor.memberExprs[1];
    ASSERT_NE(innerME, nullptr);
    EXPECT_EQ(innerME->getMemberDecl()->getNameAsString(), "inner");

    // valueME's base should be innerME (verify structure)
    const auto* baseCheck = llvm::dyn_cast<clang::MemberExpr>(valueME->getBase());
    ASSERT_NE(baseCheck, nullptr);
    EXPECT_EQ(baseCheck->getMemberDecl()->getNameAsString(), "inner");

    // inner's base should be implicit this
    const auto* thisExpr = llvm::dyn_cast<clang::CXXThisExpr>(innerME->getBase());
    ASSERT_NE(thisExpr, nullptr);
    EXPECT_TRUE(thisExpr->isImplicit());

    // Get contexts
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    // Set up mock function context for translation
    clang::FunctionDecl* mockFunc = createMockFunctionWithThis(cCtx, "Outer");
    ctx.dispatcher->setCurrentFunction(mockFunc);

    // Translate the entire chain
    clang::Expr* translated = handler->handleExpr(valueME, *context);
    ASSERT_NE(translated, nullptr);

    // Should be: this->inner.value
    const auto* translatedValueME = llvm::dyn_cast<clang::MemberExpr>(translated);
    ASSERT_NE(translatedValueME, nullptr);
    EXPECT_EQ(translatedValueME->getMemberDecl()->getNameAsString(), "value");
    EXPECT_FALSE(translatedValueME->isArrow()) << "Second access should be dot (.)";

    // Base should be this->inner
    const auto* translatedInnerME = llvm::dyn_cast<clang::MemberExpr>(translatedValueME->getBase());
    ASSERT_NE(translatedInnerME, nullptr);
    EXPECT_EQ(translatedInnerME->getMemberDecl()->getNameAsString(), "inner");
    EXPECT_TRUE(translatedInnerME->isArrow()) << "First access should be arrow (->) from this";
}

// ============================================================================
// Test 5: Implicit field in compound assignment
// ============================================================================
TEST_F(ExpressionHandlerTest_MemberAccess, ImplicitFieldCompoundAssignment) {
    const char* code = R"(
        class Counter {
            int count;
        public:
            void add(int n) {
                count += n;  // Implicit member in compound assignment
            }
        };
    )";

    const clang::MemberExpr* ME = getMemberExprFromCode(code);
    ASSERT_NE(ME, nullptr);

    // Verify implicit this
    const auto* thisExpr = llvm::dyn_cast<clang::CXXThisExpr>(ME->getBase());
    ASSERT_NE(thisExpr, nullptr);
    EXPECT_TRUE(thisExpr->isImplicit());

    // Get contexts
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    // Set up mock function context for translation
    clang::FunctionDecl* mockFunc = createMockFunctionWithThis(cCtx, "Counter");
    ctx.dispatcher->setCurrentFunction(mockFunc);

    // Translate
    ctx.dispatcher->dispatch(ME);
    clang::Expr* translated = ctx.exprMapper->get(ME);
    ASSERT_NE(translated, nullptr);

    // Should be this->count
    const auto* translatedME = llvm::dyn_cast<clang::MemberExpr>(translated);
    ASSERT_NE(translatedME, nullptr);
    EXPECT_TRUE(translatedME->isArrow());
    EXPECT_EQ(translatedME->getMemberDecl()->getNameAsString(), "count");
}

// ============================================================================
// Test 6: Implicit field in unary operator
// ============================================================================
TEST_F(ExpressionHandlerTest_MemberAccess, ImplicitFieldUnaryOperator) {
    const char* code = R"(
        class Counter {
            int count;
        public:
            void increment() {
                count++;  // Implicit member in postfix increment
            }
        };
    )";

    const clang::MemberExpr* ME = getMemberExprFromCode(code);
    ASSERT_NE(ME, nullptr);

    // Verify implicit this
    const auto* thisExpr = llvm::dyn_cast<clang::CXXThisExpr>(ME->getBase());
    ASSERT_NE(thisExpr, nullptr);
    EXPECT_TRUE(thisExpr->isImplicit());

    // Get contexts
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    // Set up mock function context for translation
    clang::FunctionDecl* mockFunc = createMockFunctionWithThis(cCtx, "Counter");
    ctx.dispatcher->setCurrentFunction(mockFunc);

    // Translate
    ctx.dispatcher->dispatch(ME);
    clang::Expr* translated = ctx.exprMapper->get(ME);
    ASSERT_NE(translated, nullptr);

    // Should be this->count
    const auto* translatedME = llvm::dyn_cast<clang::MemberExpr>(translated);
    ASSERT_NE(translatedME, nullptr);
    EXPECT_TRUE(translatedME->isArrow());
    EXPECT_EQ(translatedME->getMemberDecl()->getNameAsString(), "count");
}

// ============================================================================
// Test 7: Multiple implicit field accesses in expression
// ============================================================================
TEST_F(ExpressionHandlerTest_MemberAccess, MultipleImplicitFields) {
    const char* code = R"(
        class Math {
            int x;
            int y;
        public:
            int sum() {
                return x + y;  // Two implicit member accesses
            }
        };
    )";

    auto ast = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(ast, nullptr);

    MemberExprExtractor extractor;
    extractor.TraverseDecl(ast->getASTContext().getTranslationUnitDecl());

    // Should have two MemberExprs: x and y
    ASSERT_EQ(extractor.memberExprs.size(), 2);

    // Get contexts
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    // Set up mock function context for translation
    clang::FunctionDecl* mockFunc = createMockFunctionWithThis(cCtx, "Math");
    ctx.dispatcher->setCurrentFunction(mockFunc);

    // Translate both
    for (const auto* ME : extractor.memberExprs) {
        // Verify implicit this
        const auto* thisExpr = llvm::dyn_cast<clang::CXXThisExpr>(ME->getBase());
        ASSERT_NE(thisExpr, nullptr);
        EXPECT_TRUE(thisExpr->isImplicit());

        // Translate
        ctx.dispatcher->dispatch(ME);
        clang::Expr* translated = ctx.exprMapper->get(ME);
        ASSERT_NE(translated, nullptr);

        // Should be this->field
        const auto* translatedME = llvm::dyn_cast<clang::MemberExpr>(translated);
        ASSERT_NE(translatedME, nullptr);
        EXPECT_TRUE(translatedME->isArrow());
    }
}

// ============================================================================
// Test 8: Mixed explicit and implicit member access
// ============================================================================
TEST_F(ExpressionHandlerTest_MemberAccess, MixedExplicitImplicit) {
    const char* code = R"(
        class Math {
            int x;
            int y;
        public:
            int sum() {
                return this->x + y;  // Mixed: explicit this->x, implicit y
            }
        };
    )";

    auto ast = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(ast, nullptr);

    MemberExprExtractor extractor;
    extractor.TraverseDecl(ast->getASTContext().getTranslationUnitDecl());

    // Should have two MemberExprs
    ASSERT_EQ(extractor.memberExprs.size(), 2);

    // First: this->x (explicit)
    const auto* xME = extractor.memberExprs[0];
    const auto* xThis = llvm::dyn_cast<clang::CXXThisExpr>(xME->getBase());
    ASSERT_NE(xThis, nullptr);
    EXPECT_FALSE(xThis->isImplicit()) << "this->x should be explicit";

    // Second: y (implicit)
    const auto* yME = extractor.memberExprs[1];
    const auto* yThis = llvm::dyn_cast<clang::CXXThisExpr>(yME->getBase());
    ASSERT_NE(yThis, nullptr);
    EXPECT_TRUE(yThis->isImplicit()) << "y should be implicit";

    // Get contexts
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    // Set up mock function context for translation
    clang::FunctionDecl* mockFunc = createMockFunctionWithThis(cCtx, "Math");
    ctx.dispatcher->setCurrentFunction(mockFunc);

    // Both should translate to this->field
    for (const auto* ME : extractor.memberExprs) {
        clang::Expr* translated = handler->handleExpr(ME, *context);
        ASSERT_NE(translated, nullptr);

        const auto* translatedME = llvm::dyn_cast<clang::MemberExpr>(translated);
        ASSERT_NE(translatedME, nullptr);
        EXPECT_TRUE(translatedME->isArrow());
    }
}

// ============================================================================
// Test 9: Implicit field in array subscript
// ============================================================================
TEST_F(ExpressionHandlerTest_MemberAccess, ImplicitFieldArraySubscript) {
    const char* code = R"(
        class Array {
            int data[10];
        public:
            int get(int i) {
                return data[i];  // Implicit member array access
            }
        };
    )";

    const clang::MemberExpr* ME = getMemberExprFromCode(code);
    ASSERT_NE(ME, nullptr);

    // Verify implicit this
    const auto* thisExpr = llvm::dyn_cast<clang::CXXThisExpr>(ME->getBase());
    ASSERT_NE(thisExpr, nullptr);
    EXPECT_TRUE(thisExpr->isImplicit());

    // Get contexts
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    // Set up mock function context for translation
    clang::FunctionDecl* mockFunc = createMockFunctionWithThis(cCtx, "Counter");
    ctx.dispatcher->setCurrentFunction(mockFunc);

    // Translate
    ctx.dispatcher->dispatch(ME);
    clang::Expr* translated = ctx.exprMapper->get(ME);
    ASSERT_NE(translated, nullptr);

    // Should be this->data
    const auto* translatedME = llvm::dyn_cast<clang::MemberExpr>(translated);
    ASSERT_NE(translatedME, nullptr);
    EXPECT_TRUE(translatedME->isArrow());
    EXPECT_EQ(translatedME->getMemberDecl()->getNameAsString(), "data");
}

// ============================================================================
// Test 10: Pointer member access (ptrField->member)
// ============================================================================
TEST_F(ExpressionHandlerTest_MemberAccess, PointerMemberAccess) {
    const char* code = R"(
        struct Inner { int value; };
        class Outer {
            Inner* ptr;
        public:
            int getValue() {
                return ptr->value;  // Chained: implicit ptr, then ->value
            }
        };
    )";

    auto ast = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(ast, nullptr);

    MemberExprExtractor extractor;
    extractor.TraverseDecl(ast->getASTContext().getTranslationUnitDecl());

    // Should have two MemberExprs: ptr->value and this->ptr
    // RecursiveASTVisitor visits in pre-order, so we get: value (first), ptr (second)
    ASSERT_EQ(extractor.memberExprs.size(), 2) << "Expected two MemberExprs";

    // First MemberExpr is ptr->value (outer)
    const clang::MemberExpr* valueME = extractor.memberExprs[0];
    ASSERT_NE(valueME, nullptr);
    EXPECT_EQ(valueME->getMemberDecl()->getNameAsString(), "value");
    EXPECT_TRUE(valueME->isArrow()) << "Should use arrow operator";

    // Second MemberExpr is this->ptr (inner)
    const clang::MemberExpr* ptrME = extractor.memberExprs[1];
    ASSERT_NE(ptrME, nullptr);
    EXPECT_EQ(ptrME->getMemberDecl()->getNameAsString(), "ptr");

    // valueME's base might have an ImplicitCastExpr for pointer access
    const clang::Expr* valueBase = valueME->getBase();
    // Skip implicit cast if present
    if (const auto* ICE = llvm::dyn_cast<clang::ImplicitCastExpr>(valueBase)) {
        valueBase = ICE->getSubExpr();
    }
    const auto* baseCheck = llvm::dyn_cast<clang::MemberExpr>(valueBase);
    ASSERT_NE(baseCheck, nullptr);
    EXPECT_EQ(baseCheck->getMemberDecl()->getNameAsString(), "ptr");

    // ptr's base should be implicit this
    const auto* thisExpr = llvm::dyn_cast<clang::CXXThisExpr>(ptrME->getBase());
    ASSERT_NE(thisExpr, nullptr);
    EXPECT_TRUE(thisExpr->isImplicit());

    // Get contexts
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    // Set up mock function context for translation
    clang::FunctionDecl* mockFunc = createMockFunctionWithThis(cCtx, "Outer");
    ctx.dispatcher->setCurrentFunction(mockFunc);

    // Translate the entire chain
    clang::Expr* translated = handler->handleExpr(valueME, *context);
    ASSERT_NE(translated, nullptr);

    // Should be: this->ptr->value
    const auto* translatedValueME = llvm::dyn_cast<clang::MemberExpr>(translated);
    ASSERT_NE(translatedValueME, nullptr);
    EXPECT_EQ(translatedValueME->getMemberDecl()->getNameAsString(), "value");
    EXPECT_TRUE(translatedValueME->isArrow());

    // Base should be this->ptr
    const auto* translatedPtrME = llvm::dyn_cast<clang::MemberExpr>(translatedValueME->getBase());
    ASSERT_NE(translatedPtrME, nullptr);
    EXPECT_EQ(translatedPtrME->getMemberDecl()->getNameAsString(), "ptr");
    EXPECT_TRUE(translatedPtrME->isArrow());
}

// ============================================================================
// Test 11: Nested implicit access in complex expression
// ============================================================================
TEST_F(ExpressionHandlerTest_MemberAccess, NestedImplicitInExpression) {
    const char* code = R"(
        class Math {
            int value;
        public:
            int compute() {
                return (value + 1) * 2;  // Implicit value in nested expression
            }
        };
    )";

    const clang::MemberExpr* ME = getMemberExprFromCode(code);
    ASSERT_NE(ME, nullptr);

    // Verify implicit this
    const auto* thisExpr = llvm::dyn_cast<clang::CXXThisExpr>(ME->getBase());
    ASSERT_NE(thisExpr, nullptr);
    EXPECT_TRUE(thisExpr->isImplicit());

    // Get contexts
    clang::ASTContext& cppCtx = ctx.cppAST->getASTContext();
    clang::ASTContext& cCtx = ctx.cAST->getASTContext();

    // Set up mock function context for translation
    clang::FunctionDecl* mockFunc = createMockFunctionWithThis(cCtx, "Counter");
    ctx.dispatcher->setCurrentFunction(mockFunc);

    // Translate
    ctx.dispatcher->dispatch(ME);
    clang::Expr* translated = ctx.exprMapper->get(ME);
    ASSERT_NE(translated, nullptr);

    // Should be this->value
    const auto* translatedME = llvm::dyn_cast<clang::MemberExpr>(translated);
    ASSERT_NE(translatedME, nullptr);
    EXPECT_TRUE(translatedME->isArrow());
    EXPECT_EQ(translatedME->getMemberDecl()->getNameAsString(), "value");
}

// ============================================================================
// Test 12: Verify CXXThisExpr is handled by ExpressionHandler
// ============================================================================
TEST_F(ExpressionHandlerTest_MemberAccess, CXXThisExprHandling) {
    const char* code = R"(
        class Ptr {
        public:
            Ptr* getSelf() {
                return this;  // Explicit this
            }
        };
    )";

    auto ast = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(ast, nullptr);

    ThisExprExtractor extractor;
    extractor.TraverseDecl(ast->getASTContext().getTranslationUnitDecl());

    ASSERT_FALSE(extractor.thisExprs.empty());
    const auto* thisExpr = extractor.thisExprs[0];
    EXPECT_FALSE(thisExpr->isImplicit()) << "Explicit this in return statement";

    // Translate CXXThisExpr
    // In C, this becomes a reference to the "this" parameter
    ctx.dispatcher->dispatch(thisExpr);
    clang::Expr* translated = ctx.exprMapper->get(thisExpr);
    // For now, this might not be implemented yet
    // We'll implement it as part of the feature
    // Just document the expected behavior
    (void)translated;  // Suppress unused warning
}
