/**
 * @file ExpressionHandlerTest_MethodCall.cpp
 * @brief TDD tests for ExpressionHandler - CXXMemberCallExpr translation
 *
 * Phase 44 Task 8: Method Call Translation
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (15 tests):
 * 1. SimpleMethodCall - Basic obj.method() call
 * 2. MethodCallWithOneArg - obj.method(arg) call
 * 3. MethodCallWithTwoArgs - obj.method(arg1, arg2) call
 * 4. MethodCallWithMultipleArgs - obj.method(arg1, arg2, arg3) call
 * 5. MethodCallOnPointer - ptr->method() call
 * 6. MethodCallOnThis - this->method() call
 * 7. ChainedMethodCalls - obj.m1().m2() call
 * 8. MethodCallReturningValue - int x = obj.getValue() call
 * 9. MethodCallInCondition - if (obj.isValid()) call
 * 10. MethodCallInLoop - while (obj.hasNext()) call
 * 11. MethodCallAsFunctionArg - printf("%d", obj.getValue()) call
 * 12. ConstMethodCall - const obj.getValue() call
 * 13. MethodCallWithComplexArg - obj.method(a + b * c) call
 * 14. NestedMethodCall - obj.method(obj2.getValue()) call
 * 15. MethodCallOnTemporary - Counter().getValue() call (if supported)
 */

#include "helpers/UnitTestHelper.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ExprCXX.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ExpressionHandlerMethodCallTest
 * @brief Test fixture for CXXMemberCallExpr translation
 *
 * Uses real AST contexts to test translation of C++ method calls
 * to C function calls with explicit 'this' parameter.
 */
class ExpressionHandlerMethodCallTest : public ::testing::Test {
protected:
    UnitTestContext ctx;

    void SetUp() override {
        ctx = createUnitTestContext();
        ctx.dispatcher->registerHandler<ExpressionHandler>();
    }
/**
     * @brief Extract CXXMemberCallExpr and all methods from C++ code
     * @param code C++ code containing method call and class definitions
     * @param outMethods Output map of method name → method declaration
     * @return Extracted CXXMemberCallExpr (first one found)
     */
    const clang::CXXMemberCallExpr* extractMethodCallAndMethods(
        const std::string& code,
        std::map<std::string, const clang::CXXMethodDecl*>& outMethods
    ) {
        class Visitor : public clang::RecursiveASTVisitor<Visitor> {
        public:
            const clang::CXXMemberCallExpr* foundCall = nullptr;
            std::map<std::string, const clang::CXXMethodDecl*> methods;

            bool VisitCXXMemberCallExpr(clang::CXXMemberCallExpr* E) {
                if (!foundCall) {
                    foundCall = E;
                }
                return true;
            }

            bool VisitCXXMethodDecl(clang::CXXMethodDecl* M) {
                // Skip constructors and destructors
                if (!llvm::isa<clang::CXXConstructorDecl>(M) &&
                    !llvm::isa<clang::CXXDestructorDecl>(M)) {
                    methods[M->getNameAsString()] = M;
                }
                return true;
            }
        };

        cppAST = clang::tooling::buildASTFromCode(code);
        EXPECT_NE(cppAST, nullptr) << "Failed to parse code: " << code;

        Visitor visitor;
        visitor.TraverseDecl(cppAST->getASTContext().getTranslationUnitDecl());

        EXPECT_NE(visitor.foundCall, nullptr) << "No CXXMemberCallExpr found in code: " << code;
        outMethods = visitor.methods;
        return visitor.foundCall;
    }

    /**
     * @brief Extract CXXMemberCallExpr from C++ code
     * @param code C++ code containing method call
     * @return Extracted CXXMemberCallExpr
     */
    const clang::CXXMemberCallExpr* extractMethodCall(const std::string& code) {
        std::map<std::string, const clang::CXXMethodDecl*> unused;
        return extractMethodCallAndMethods(code, unused);
    }

    /**
     * @brief Create a C function representing a translated method
     * @param className Name of the class
     * @param methodName Name of the method
     * @param returnType Return type of the method
     * @param paramTypes Additional parameter types (beyond 'this')
     * @return C FunctionDecl
     */
    clang::FunctionDecl* createCFunction(
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
// Test 1: SimpleMethodCall - Basic obj.method() call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, SimpleMethodCall) {
    // C++: obj.getValue()
    // Expected C: getValue(&obj)

    const char* code = R"(
        class Counter {
        public:
            int getValue() { return count; }
        private:
            int count;
        };
        void test() {
            Counter obj;
            obj.getValue();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    // Verify it's a method call with no arguments
    EXPECT_EQ(methodCall->getNumArgs(), 0);

    // Get method being called
    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_EQ(method->getNameAsString(), "getValue");

    // Create C function for this method
    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createCFunction("Counter", "getValue", cCtx.IntTy);

    // Register the method mapping
    context->registerMethod(method, cFunc);

    // Translate the method call
    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;

    // Verify result is a CallExpr
    ASSERT_NE(result, nullptr);
    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr) << "Expected CallExpr";

    // Verify function name
    auto* calleeDecl = callExpr->getDirectCallee();
    ASSERT_NE(calleeDecl, nullptr);
    EXPECT_EQ(calleeDecl->getNameAsString(), "Counter_getValue");

    // Verify arguments: should have 1 argument (the object)
    EXPECT_EQ(callExpr->getNumArgs(), 1);
}

// ============================================================================
// Test 2: MethodCallWithOneArg - obj.method(arg) call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, MethodCallWithOneArg) {
    // C++: obj.setValue(42)
    // Expected C: setValue(&obj, 42)

    const char* code = R"(
        class Counter {
        public:
            void setValue(int value) { count = value; }
        private:
            int count;
        };
        void test() {
            Counter obj;
            obj.setValue(42);
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    // Verify it has 1 argument
    EXPECT_EQ(methodCall->getNumArgs(), 1);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    // Create C function
    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createCFunction(
        "Counter", "setValue", cCtx.VoidTy, {cCtx.IntTy}
    );
    context->registerMethod(method, cFunc);

    // Translate
    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;

    ASSERT_NE(result, nullptr);
    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // Verify arguments: object + 1 original argument = 2 total
    EXPECT_EQ(callExpr->getNumArgs(), 2);
}

// ============================================================================
// Test 3: MethodCallWithTwoArgs - obj.method(arg1, arg2) call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, MethodCallWithTwoArgs) {
    // C++: obj.setPosition(10, 20)
    // Expected C: setPosition(&obj, 10, 20)

    const char* code = R"(
        class Point {
        public:
            void setPosition(int x, int y) { this->x = x; this->y = y; }
        private:
            int x, y;
        };
        void test() {
            Point obj;
            obj.setPosition(10, 20);
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_EQ(methodCall->getNumArgs(), 2);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createCFunction(
        "Point", "setPosition", cCtx.VoidTy, {cCtx.IntTy, cCtx.IntTy}
    );
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);
    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // Object + 2 args = 3 total
    EXPECT_EQ(callExpr->getNumArgs(), 3);
}

// ============================================================================
// Test 4: MethodCallWithMultipleArgs - obj.method(arg1, arg2, arg3) call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, MethodCallWithMultipleArgs) {
    // C++: obj.setColor(255, 128, 64, 1.0f)
    // Expected C: setColor(&obj, 255, 128, 64, 1.0f)

    const char* code = R"(
        class Color {
        public:
            void setColor(int r, int g, int b, float a) {
                this->r = r; this->g = g; this->b = b; this->a = a;
            }
        private:
            int r, g, b;
            float a;
        };
        void test() {
            Color obj;
            obj.setColor(255, 128, 64, 1.0f);
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_EQ(methodCall->getNumArgs(), 4);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createCFunction(
        "Color", "setColor", cCtx.VoidTy,
        {cCtx.IntTy, cCtx.IntTy, cCtx.IntTy, cCtx.FloatTy}
    );
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);
    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // Object + 4 args = 5 total
    EXPECT_EQ(callExpr->getNumArgs(), 5);
}

// ============================================================================
// Test 5: MethodCallOnPointer - ptr->method() call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, MethodCallOnPointer) {
    // C++: ptr->getValue()
    // Expected C: getValue(ptr)

    const char* code = R"(
        class Counter {
        public:
            int getValue() { return count; }
        private:
            int count;
        };
        void test() {
            Counter* ptr = nullptr;
            ptr->getValue();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createCFunction("Counter", "getValue", cCtx.IntTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);
    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // For pointer, we pass it directly (no & needed)
    EXPECT_EQ(callExpr->getNumArgs(), 1);

    // First arg should NOT be UnaryOperator (no & for pointers)
    const clang::Expr* firstArg = callExpr->getArg(0);
    ASSERT_NE(firstArg, nullptr);
    // For ptr->method(), the object is already a pointer, so no & needed
}

// ============================================================================
// Test 6: MethodCallOnThis - this->method() call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, MethodCallOnThis) {
    // C++: this->helper()
    // Expected C: helper(this)

    const char* code = R"(
        class Counter {
        public:
            void helper() {}
            void process() {
                this->helper();
            }
        private:
            int count;
        };
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_EQ(method->getNameAsString(), "helper");

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createCFunction("Counter", "helper", cCtx.VoidTy);
    context->registerMethod(method, cFunc);

    // We need to set the current function context (for 'this' translation)
    // Create a C function representing the enclosing method 'process'
    clang::FunctionDecl* processFunc = createCFunction("Counter", "process", cCtx.VoidTy);
    context->pushFunction(processFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;

    context->popFunction();

    ASSERT_NE(result, nullptr);
    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    EXPECT_EQ(callExpr->getNumArgs(), 1);
}

// ============================================================================
// Test 7: ChainedMethodCalls - obj.m1().m2() call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, ChainedMethodCalls) {
    // C++: obj.getNext().getValue()
    // Expected C: getValue(getNext(&obj))

    const char* code = R"(
        class Node {
        public:
            Node& getNext() { return *next; }
            int getValue() { return value; }
        private:
            Node* next;
            int value;
        };
        void test() {
            Node obj;
            obj.getNext().getValue();
        }
    )";

    // Extract all methods and the method call from the same AST
    std::map<std::string, const clang::CXXMethodDecl*> methods;
    const clang::CXXMemberCallExpr* methodCall = extractMethodCallAndMethods(code, methods);

    ASSERT_EQ(methods.size(), 2);
    ASSERT_NE(methods.find("getNext"), methods.end());
    ASSERT_NE(methods.find("getValue"), methods.end());
    ASSERT_NE(methodCall, nullptr);

    // The outer call is getValue()
    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_EQ(method->getNameAsString(), "getValue");

    clang::ASTContext& cCtx = cAST->getASTContext();

    // Create C functions for both methods
    clang::QualType nodeRefType = cCtx.getLValueReferenceType(
        cCtx.getRecordType(cCtx.buildImplicitRecord("Node"))
    );
    clang::FunctionDecl* getNextFunc = createCFunction("Node", "getNext", nodeRefType);
    clang::FunctionDecl* getValueFunc = createCFunction("Node", "getValue", cCtx.IntTy);

    // Register both methods
    context->registerMethod(methods["getNext"], getNextFunc);
    context->registerMethod(methods["getValue"], getValueFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    // Result should be a CallExpr
    auto* outerCall = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(outerCall, nullptr);

    // The first argument to getValue should be the result of getNext call
    EXPECT_EQ(outerCall->getNumArgs(), 1);
}

// ============================================================================
// Test 8: MethodCallReturningValue - int x = obj.getValue() call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, MethodCallReturningValue) {
    // C++: int x = obj.getValue();
    // Expected C: int x = getValue(&obj);

    const char* code = R"(
        class Counter {
        public:
            int getValue() { return count; }
        private:
            int count;
        };
        void test() {
            Counter obj;
            int x = obj.getValue();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createCFunction("Counter", "getValue", cCtx.IntTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // Verify return type matches
    EXPECT_TRUE(callExpr->getType()->isIntegerType());
}

// ============================================================================
// Test 9: MethodCallInCondition - if (obj.isValid()) call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, MethodCallInCondition) {
    // C++: if (obj.isValid())
    // Expected C: if (isValid(&obj))

    const char* code = R"(
        class Validator {
        public:
            bool isValid() { return valid; }
        private:
            bool valid;
        };
        void test() {
            Validator obj;
            if (obj.isValid()) {}
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createCFunction("Validator", "isValid", cCtx.BoolTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    EXPECT_TRUE(callExpr->getType()->isBooleanType());
}

// ============================================================================
// Test 10: MethodCallInLoop - while (obj.hasNext()) call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, MethodCallInLoop) {
    // C++: while (obj.hasNext())
    // Expected C: while (hasNext(&obj))

    const char* code = R"(
        class Iterator {
        public:
            bool hasNext() { return index < size; }
        private:
            int index;
            int size;
        };
        void test() {
            Iterator obj;
            while (obj.hasNext()) {}
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createCFunction("Iterator", "hasNext", cCtx.BoolTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);
}

// ============================================================================
// Test 11: MethodCallAsFunctionArg - printf("%d", obj.getValue()) call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, MethodCallAsFunctionArg) {
    // C++: someFunc(obj.getValue())
    // Expected C: someFunc(getValue(&obj))

    const char* code = R"(
        class Counter {
        public:
            int getValue() { return count; }
        private:
            int count;
        };
        void someFunc(int x) {}
        void test() {
            Counter obj;
            someFunc(obj.getValue());
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createCFunction("Counter", "getValue", cCtx.IntTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);
}

// ============================================================================
// Test 12: ConstMethodCall - const obj.getValue() call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, ConstMethodCall) {
    // C++: obj.getValue() [const method]
    // Expected C: getValue(&obj) [const is advisory in C]

    const char* code = R"(
        class Counter {
        public:
            int getValue() const { return count; }
        private:
            int count;
        };
        void test() {
            const Counter obj;
            obj.getValue();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_TRUE(method->isConst());

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createCFunction("Counter", "getValue", cCtx.IntTy);
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);
}

// ============================================================================
// Test 13: MethodCallWithComplexArg - obj.method(a + b * c) call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, MethodCallWithComplexArg) {
    // C++: obj.setValue(a + b * c)
    // Expected C: setValue(&obj, a + b * c)

    const char* code = R"(
        class Counter {
        public:
            void setValue(int value) { count = value; }
        private:
            int count;
        };
        void test() {
            Counter obj;
            int a = 1, b = 2, c = 3;
            obj.setValue(a + b * c);
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);
    EXPECT_EQ(methodCall->getNumArgs(), 1);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* cFunc = createCFunction("Counter", "setValue", cCtx.VoidTy, {cCtx.IntTy});
    context->registerMethod(method, cFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // Object + complex expression = 2 args
    EXPECT_EQ(callExpr->getNumArgs(), 2);
}

// ============================================================================
// Test 14: NestedMethodCall - obj.method(obj2.getValue()) call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, NestedMethodCall) {
    // C++: obj.setValue(obj2.getValue())
    // Expected C: setValue(&obj, getValue(&obj2))

    const char* code = R"(
        class Counter {
        public:
            int getValue() { return count; }
            void setValue(int value) { count = value; }
        private:
            int count;
        };
        void test() {
            Counter obj, obj2;
            obj.setValue(obj2.getValue());
        }
    )";

    // Extract all methods and the method call from the same AST
    std::map<std::string, const clang::CXXMethodDecl*> methods;
    const clang::CXXMemberCallExpr* methodCall = extractMethodCallAndMethods(code, methods);

    ASSERT_EQ(methods.size(), 2);
    ASSERT_NE(methods.find("getValue"), methods.end());
    ASSERT_NE(methods.find("setValue"), methods.end());
    ASSERT_NE(methodCall, nullptr);

    // This is setValue call
    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_EQ(method->getNameAsString(), "setValue");

    clang::ASTContext& cCtx = cAST->getASTContext();
    clang::FunctionDecl* setValueFunc = createCFunction("Counter", "setValue", cCtx.VoidTy, {cCtx.IntTy});
    clang::FunctionDecl* getValueFunc = createCFunction("Counter", "getValue", cCtx.IntTy);

    // Register both methods
    context->registerMethod(methods["setValue"], setValueFunc);
    context->registerMethod(methods["getValue"], getValueFunc);

    clang::Expr* result = ctx.dispatcher->dispatch(methodCall);
    auto __result = ctx.exprMapper->get(methodCall); __result;
    ASSERT_NE(result, nullptr);

    auto* callExpr = llvm::dyn_cast<clang::CallExpr>(result);
    ASSERT_NE(callExpr, nullptr);

    // Object + nested call = 2 args
    EXPECT_EQ(callExpr->getNumArgs(), 2);
}

// ============================================================================
// Test 15: MethodCallOnTemporary - Counter().getValue() call
// ============================================================================
TEST_F(ExpressionHandlerMethodCallTest, MethodCallOnTemporary) {
    // C++: Counter().getValue()
    // Expected C: Complex - depends on temporary object handling
    // For now, we test that we can at least detect the method call

    const char* code = R"(
        class Counter {
        public:
            Counter() : count(0) {}
            int getValue() { return count; }
        private:
            int count;
        };
        void test() {
            Counter().getValue();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    ASSERT_NE(methodCall, nullptr);

    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_EQ(method->getNameAsString(), "getValue");

    // Verify the object is a temporary (CXXConstructExpr)
    const clang::Expr* object = methodCall->getImplicitObjectArgument();
    ASSERT_NE(object, nullptr);

    // For now, we just verify we can identify this case
    // Full translation would require temporary variable creation
}
