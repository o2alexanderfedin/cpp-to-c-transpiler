/**
 * @file ExpressionHandlerTest_VirtualCall.cpp
 * @brief TDD tests for ExpressionHandler - Virtual Call Translation (Phase 45 Task 7)
 *
 * Tests COM-style vtable dispatch for virtual method calls.
 * Pattern: obj->lpVtbl->methodName(obj, args...)
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (15 tests):
 * 1. VirtualCallOnPointer - ptr->virtualMethod() → ptr->lpVtbl->virtualMethod(ptr)
 * 2. VirtualCallOnValue - obj.virtualMethod() → (&obj)->lpVtbl->virtualMethod(&obj)
 * 3. VirtualCallWithArgs - ptr->method(a, b) → ptr->lpVtbl->method(ptr, a, b)
 * 4. VirtualCallWithReturn - int x = ptr->getValue() → int x = ptr->lpVtbl->getValue(ptr)
 * 5. VirtualCallThroughBasePointer - Base* ptr = derived; ptr->method() (polymorphism)
 * 6. ChainedVirtualCalls - obj.getNext()->virtualMethod()
 * 7. VirtualCallInCondition - if (ptr->isValid()) with virtual isValid
 * 8. VirtualCallInExpression - result = ptr->getValue() + 10
 * 9. VirtualDestructorCall - ptr->~Shape() → ptr->lpVtbl->destructor(ptr)
 * 10. CastThenVirtualCall - ((Derived*)ptr)->method()
 * 11. VirtualCallThroughReference - Shape& ref; ref.draw()
 * 12. MultipleVirtualCalls - ptr1->m1(); ptr2->m2(); in sequence
 * 13. VirtualCallWithComplexArgs - ptr->method(a + b * c, obj.field)
 * 14. NonVirtualCallUnchanged - ptr->nonVirtualMethod() → ClassName_nonVirtualMethod(ptr)
 * 15. MixedVirtualNonVirtual - Test class with both virtual and non-virtual methods
 */

#include "helpers/UnitTestHelper.h"
#include "CNodeBuilder.h"
#include "VirtualCallTranslator.h"
#include "VirtualMethodAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ExprCXX.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ExpressionHandlerVirtualCallTest
 * @brief Test fixture for virtual call translation
 *
 * Tests translation of C++ virtual method calls to COM-style vtable dispatch.
 */
class ExpressionHandlerVirtualCallTest : public ::testing::Test {
protected:
    UnitTestContext ctx;
    std::unique_ptr<VirtualMethodAnalyzer> virtualAnalyzer;
    std::unique_ptr<VirtualCallTranslator> virtualTranslator;

    void SetUp() override {
        ctx = createUnitTestContext();
        ctx.dispatcher->registerHandler<ExpressionHandler>();
    }
/**
     * @brief Extract CXXMemberCallExpr from C++ code
     * @param code C++ code containing method call
     * @return Extracted CXXMemberCallExpr (first one found)
     */
    const clang::CXXMemberCallExpr* extractMethodCall(const std::string& code) {
        class Visitor : public clang::RecursiveASTVisitor<Visitor> {
        public:
            const clang::CXXMemberCallExpr* foundCall = nullptr;

            bool VisitCXXMemberCallExpr(clang::CXXMemberCallExpr* E) {
                if (!foundCall) {
                    foundCall = E;
                }
                return true;
            }
        };

        cppAST = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(cppAST, nullptr) << "Failed to parse code: " << code;

        // Recreate virtual analyzer with new AST
        virtualAnalyzer = std::make_unique<VirtualMethodAnalyzer>(cppAST->getASTContext());
        virtualTranslator = std::make_unique<VirtualCallTranslator>(
            cppAST->getASTContext(),
            *virtualAnalyzer
        );

        Visitor visitor;
        visitor.TraverseDecl(cppAST->getASTContext().getTranslationUnitDecl());

        EXPECT_NE(visitor.foundCall, nullptr) << "No CXXMemberCallExpr found in code: " << code;
        return visitor.foundCall;
    }

    /**
     * @brief Create a C function representing a translated virtual method
     * @param className Name of the class
     * @param methodName Name of the method
     * @param returnType Return type of the method
     * @param paramTypes Additional parameter types (beyond 'this')
     * @return C FunctionDecl
     */
    clang::FunctionDecl* createVirtualMethodCFunction(
        const std::string& className,
        const std::string& methodName,
        clang::QualType returnType,
        const std::vector<clang::QualType>& paramTypes = {}
    ) {
        clang::ASTContext& cCtx = cAST->getASTContext();

        // Create function name: ClassName_methodName
        std::string funcName = className + "_" + methodName;

        // Create parameters: this, param1, param2, ...
        llvm::SmallVector<clang::ParmVarDecl*, 4> params;

        // First parameter: struct ClassName* this
        clang::QualType thisType = cCtx.getPointerType(
            cCtx.getRecordType(
                cCtx.buildImplicitRecord(className.c_str())
            )
        );
        clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
            cCtx,
            nullptr,  // DeclContext
            clang::SourceLocation(),
            clang::SourceLocation(),
            &cCtx.Idents.get("this"),
            thisType,
            nullptr,  // TypeSourceInfo
            clang::SC_None,
            nullptr   // Default argument
        );
        params.push_back(thisParam);

        // Additional parameters
        for (size_t i = 0; i < paramTypes.size(); ++i) {
            std::string paramName = "arg" + std::to_string(i);
            clang::ParmVarDecl* param = clang::ParmVarDecl::Create(
                cCtx,
                nullptr,
                clang::SourceLocation(),
                clang::SourceLocation(),
                &cCtx.Idents.get(paramName),
                paramTypes[i],
                nullptr,
                clang::SC_None,
                nullptr
            );
            params.push_back(param);
        }

        // Create array of parameter types for function type
        llvm::SmallVector<clang::QualType, 4> paramQualTypes;
        for (auto* param : params) {
            paramQualTypes.push_back(param->getType());
        }

        // Create function declaration
        clang::FunctionDecl* func = clang::FunctionDecl::Create(
            cCtx,
            cCtx.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            clang::DeclarationName(&cCtx.Idents.get(funcName)),
            cCtx.getFunctionType(returnType, paramQualTypes,
                                 clang::FunctionProtoType::ExtProtoInfo()),
            nullptr,  // TypeSourceInfo
            clang::SC_None
        );

        func->setParams(params);

        return func;
    }
};

// ============================================================================
// Test 1: VirtualCallOnPointer - ptr->virtualMethod()
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, VirtualCallOnPointer) {
    // C++: ptr->draw()
    // Expected C: ptr->lpVtbl->draw(ptr)

    const char* code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };
        void test(Shape* ptr) {
            ptr->draw();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    // Verify this is a virtual call
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall))
        << "draw() should be detected as virtual call";

    // Get method being called
    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_EQ(method->getNameAsString(), "draw");
    EXPECT_TRUE(method->isVirtual()) << "draw() should be virtual";

    // Create C function for this virtual method
    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Shape", "draw", cCtx.VoidTy);

    // Register the method mapping
    context->registerMethod(method, cFunc);

    // Translate the method call
    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;

    // For virtual calls, we expect vtable dispatch structure:
    // ptr->lpVtbl->draw(ptr)
    // This should be a CallExpr where:
    // - Callee is a MemberExpr accessing draw from lpVtbl
    // - First argument is ptr

    ASSERT_NE(result, nullptr) << "Translation should succeed";

    // Result should be a CallExpr
    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr) << "Expected CallExpr for virtual call";

    // TODO: Verify vtable dispatch structure when implementation is complete
    // - Callee should be MemberExpr for lpVtbl->draw
    // - First arg should be the object pointer
}

// ============================================================================
// Test 2: VirtualCallOnValue - obj.virtualMethod()
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, VirtualCallOnValue) {
    // C++: obj.draw()
    // Expected C: (&obj)->lpVtbl->draw(&obj)

    const char* code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };
        void test() {
            Shape obj;
            obj.draw();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    // Verify this is a virtual call
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_TRUE(method->isVirtual());

    // Create and register C function
    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Shape", "draw", cCtx.VoidTy);
    context->registerMethod(method, cFunc);

    // Translate
    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    // For value objects, we need to take address before vtable access
    // Expected: (&obj)->lpVtbl->draw(&obj)
    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // TODO: Verify that object is taken address of for vtable access
}

// ============================================================================
// Test 3: VirtualCallWithArgs - ptr->method(a, b)
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, VirtualCallWithArgs) {
    // C++: ptr->setColor(255, 128)
    // Expected C: ptr->lpVtbl->setColor(ptr, 255, 128)

    const char* code = R"(
        class Shape {
        public:
            virtual void setColor(int r, int g) {}
        };
        void test(Shape* ptr) {
            ptr->setColor(255, 128);
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_EQ(methodCall->getNumArgs(), 2);
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction(
        "Shape", "setColor", cCtx.VoidTy, {cCtx.IntTy, cCtx.IntTy}
    );
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // Should have object + 2 args = 3 total
    EXPECT_EQ(callExpr->getNumArgs(), 3);
}

// ============================================================================
// Test 4: VirtualCallWithReturn - int x = ptr->getValue()
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, VirtualCallWithReturn) {
    // C++: int x = ptr->getValue();
    // Expected C: int x = ptr->lpVtbl->getValue(ptr);

    const char* code = R"(
        class Counter {
        public:
            virtual int getValue() { return count; }
        private:
            int count;
        };
        void test(Counter* ptr) {
            int x = ptr->getValue();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Counter", "getValue", cCtx.IntTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // Verify return type
    EXPECT_TRUE(callExpr->getType()->isIntegerType());
}

// ============================================================================
// Test 5: VirtualCallThroughBasePointer - Polymorphism
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, VirtualCallThroughBasePointer) {
    // C++: Base* ptr = &derived; ptr->method();
    // Expected C: ptr->lpVtbl->method(ptr)
    // (Runtime vtable determines which implementation is called)

    const char* code = R"(
        class Base {
        public:
            virtual void method() {}
        };
        class Derived : public Base {
        public:
            virtual void method() override {}
        };
        void test() {
            Derived derived;
            Base* ptr = &derived;
            ptr->method();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_TRUE(method->isVirtual());

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Base", "method", cCtx.VoidTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // Polymorphic call through base pointer
    // The vtable dispatch ensures derived method is called at runtime
}

// ============================================================================
// Test 6: ChainedVirtualCalls - obj.getNext()->virtualMethod()
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, ChainedVirtualCalls) {
    // C++: obj.getNext()->draw()
    // Expected C: ((&obj)->lpVtbl->getNext(&obj))->lpVtbl->draw(...)

    const char* code = R"(
        class Node {
        public:
            virtual Node* getNext() { return next; }
            virtual void draw() {}
        private:
            Node* next;
        };
        void test() {
            Node obj;
            obj.getNext()->draw();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_EQ(method->getNameAsString(), "draw");

    // Note: In chained calls, the inner call (getNext) should also be virtual
    // This test focuses on the outer call translation
    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Node", "draw", cCtx.VoidTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);
}

// ============================================================================
// Test 7: VirtualCallInCondition - if (ptr->isValid())
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, VirtualCallInCondition) {
    // C++: if (ptr->isValid())
    // Expected C: if (ptr->lpVtbl->isValid(ptr))

    const char* code = R"(
        class Validator {
        public:
            virtual bool isValid() { return true; }
        };
        void test(Validator* ptr) {
            if (ptr->isValid()) {}
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Validator", "isValid", cCtx.BoolTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);
    EXPECT_TRUE(callExpr->getType()->isBooleanType());
}

// ============================================================================
// Test 8: VirtualCallInExpression - result = ptr->getValue() + 10
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, VirtualCallInExpression) {
    // C++: result = ptr->getValue() + 10;
    // Expected C: result = ptr->lpVtbl->getValue(ptr) + 10;

    const char* code = R"(
        class Counter {
        public:
            virtual int getValue() { return count; }
        private:
            int count;
        };
        void test(Counter* ptr) {
            int result = ptr->getValue() + 10;
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Counter", "getValue", cCtx.IntTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);
}

// ============================================================================
// Test 9: VirtualDestructorCall - ptr->~Shape()
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, VirtualDestructorCall) {
    // C++: ptr->~Shape()
    // Expected C: ptr->lpVtbl->destructor(ptr)

    const char* code = R"(
        class Shape {
        public:
            virtual ~Shape() {}
        };
        void test(Shape* ptr) {
            ptr->~Shape();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    // Virtual destructors should be detected as virtual calls
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    // Check if it's a destructor
    auto* dtor = llvm::dyn_cast<clang::CXXDestructorDecl>(method);
    EXPECT_NE(dtor, nullptr) << "Should be destructor";

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Shape", "destructor", cCtx.VoidTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);
}

// ============================================================================
// Test 10: CastThenVirtualCall - ((Derived*)ptr)->method()
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, CastThenVirtualCall) {
    // C++: ((Derived*)ptr)->method()
    // Expected C: ((struct Derived*)ptr)->lpVtbl->method((struct Derived*)ptr)

    const char* code = R"(
        class Base {
        public:
            virtual void method() {}
        };
        class Derived : public Base {
        public:
            virtual void method() override {}
        };
        void test(Base* ptr) {
            ((Derived*)ptr)->method();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Derived", "method", cCtx.VoidTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);
}

// ============================================================================
// Test 11: VirtualCallThroughReference - Shape& ref; ref.draw()
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, VirtualCallThroughReference) {
    // C++: ref.draw() [where ref is Shape&]
    // Expected C: ref->lpVtbl->draw(ref) [ref becomes pointer in C]

    const char* code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };
        void test(Shape& ref) {
            ref.draw();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Shape", "draw", cCtx.VoidTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // References become pointers in C, so no & needed
}

// ============================================================================
// Test 12: MultipleVirtualCalls - ptr1->m1(); ptr2->m2();
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, MultipleVirtualCalls) {
    // C++: ptr1->draw(); ptr2->draw();
    // Expected C: ptr1->lpVtbl->draw(ptr1); ptr2->lpVtbl->draw(ptr2);

    const char* code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };
        void test(Shape* ptr1, Shape* ptr2) {
            ptr1->draw();
            ptr2->draw();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Shape", "draw", cCtx.VoidTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // Each call should be independent
}

// ============================================================================
// Test 13: VirtualCallWithComplexArgs - ptr->method(a + b * c, obj.field)
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, VirtualCallWithComplexArgs) {
    // C++: ptr->compute(a + b * c, obj.x)
    // Expected C: ptr->lpVtbl->compute(ptr, a + b * c, obj.x)

    const char* code = R"(
        class Calculator {
        public:
            virtual int compute(int expr, int value) { return expr + value; }
        };
        struct Point { int x, y; };
        void test(Calculator* ptr) {
            int a = 1, b = 2, c = 3;
            Point obj;
            ptr->compute(a + b * c, obj.x);
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));
    EXPECT_EQ(methodCall->getNumArgs(), 2);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction(
        "Calculator", "compute", cCtx.IntTy, {cCtx.IntTy, cCtx.IntTy}
    );
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // Should have object + 2 complex args = 3 total
    EXPECT_EQ(callExpr->getNumArgs(), 3);
}

// ============================================================================
// Test 14: NonVirtualCallUnchanged - Non-virtual method should not use vtable
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, NonVirtualCallUnchanged) {
    // C++: ptr->nonVirtualMethod()
    // Expected C: Shape_nonVirtualMethod(ptr)  [NOT vtable dispatch]

    const char* code = R"(
        class Shape {
        public:
            void nonVirtualMethod() {}  // Not virtual
        };
        void test(Shape* ptr) {
            ptr->nonVirtualMethod();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    // Should NOT be detected as virtual call
    EXPECT_FALSE(virtualTranslator->isVirtualCall(methodCall))
        << "Non-virtual method should not be detected as virtual";

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_FALSE(method->isVirtual()) << "Method should not be virtual";

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Shape", "nonVirtualMethod", cCtx.VoidTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // For non-virtual methods, should use direct function call
    // NOT vtable dispatch
}

// ============================================================================
// Test 15: MixedVirtualNonVirtual - Class with both types
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallTest, MixedVirtualNonVirtual) {
    // C++: class with both virtual and non-virtual methods
    // Verify correct dispatch for each type

    const char* code = R"(
        class Widget {
        public:
            virtual void render() {}       // Virtual
            void setPosition(int x) {}     // Non-virtual
            virtual void update() {}       // Virtual
        };
        void test(Widget* ptr) {
            ptr->render();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_EQ(method->getNameAsString(), "render");

    // render() should be virtual
    EXPECT_TRUE(virtualTranslator->isVirtualCall(methodCall));
    EXPECT_TRUE(method->isVirtual());

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createVirtualMethodCFunction("Widget", "render", cCtx.VoidTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // Virtual method should use vtable dispatch
}
