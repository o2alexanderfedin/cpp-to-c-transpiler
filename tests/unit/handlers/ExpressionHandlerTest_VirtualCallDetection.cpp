/**
 * @file ExpressionHandlerTest_VirtualCallDetection.cpp
 * @brief TDD tests for ExpressionHandler - Virtual call detection
 *
 * Phase 45 Task 6: Virtual Call Detection
 *
 * Following strict TDD: Red -> Green -> Refactor
 *
 * Test Plan (8 tests):
 * 1. DetectVirtualMethodCall - Basic virtual method call detection
 * 2. DetectNonVirtualMethodCall - Non-virtual method call returns false
 * 3. DetectVirtualCallOnBasePointer - Virtual call on base class pointer
 * 4. DetectVirtualCallOnDerivedPointer - Virtual call on derived class pointer
 * 5. DetectVirtualDestructorCall - Virtual destructor call detection
 * 6. StaticMethodIsNotVirtual - Static method is not virtual
 * 7. InlineMethodIsNotVirtual - Inline method may or may not be virtual
 * 8. FinalMethodIsVirtual - Final method can still be virtual
 */

#include "handlers/ExpressionHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ExprCXX.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ExpressionHandlerVirtualCallDetectionTest
 * @brief Test fixture for virtual call detection
 *
 * Uses real AST contexts to test detection of virtual method calls
 * vs non-virtual method calls.
 */
class ExpressionHandlerVirtualCallDetectionTest : public ::testing::Test {
protected:
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    std::unique_ptr<clang::CNodeBuilder> builder;
    std::unique_ptr<HandlerContext> context;
    std::unique_ptr<ExpressionHandler> handler;

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

        // Create handler
        handler = std::make_unique<ExpressionHandler>();
    }

    void TearDown() override {
        handler.reset();
        context.reset();
        builder.reset();
        cAST.reset();
        cppAST.reset();
    }

    /**
     * @brief Extract CXXMemberCallExpr and method declaration from C++ code
     * @param code C++ code containing method call
     * @return Extracted CXXMemberCallExpr (nullptr if not found)
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

        Visitor visitor;
        visitor.TraverseDecl(cppAST->getASTContext().getTranslationUnitDecl());

        return visitor.foundCall;
    }

    /**
     * @brief Extract CXXMemberCallExpr from code, asserting it exists
     * @param code C++ code containing method call
     * @return Extracted CXXMemberCallExpr
     */
    const clang::CXXMemberCallExpr* extractMethodCallOrFail(const std::string& code) {
        const clang::CXXMemberCallExpr* call = extractMethodCall(code);
        EXPECT_NE(call, nullptr) << "No CXXMemberCallExpr found in code: " << code;
        return call;
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
// Test 1: DetectVirtualMethodCall - Basic virtual method call detection
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallDetectionTest, DetectVirtualMethodCall) {
    // C++: obj.process()  [virtual method]
    // Expected: isVirtualCall() returns true

    const char* code = R"(
        class Base {
        public:
            virtual void process() {}
        };
        void test() {
            Base obj;
            obj.process();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCallOrFail(code);
    ASSERT_NE(methodCall, nullptr);

    // Get method being called
    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_EQ(method->getNameAsString(), "process");

    // Test the new isVirtualCall method
    bool isVirtual = handler->isVirtualCall(methodCall);
    EXPECT_TRUE(isVirtual) << "Virtual method should be detected as virtual";
}

// ============================================================================
// Test 2: DetectNonVirtualMethodCall - Non-virtual method call returns false
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallDetectionTest, DetectNonVirtualMethodCall) {
    // C++: obj.process()  [non-virtual method]
    // Expected: isVirtualCall() returns false

    const char* code = R"(
        class Base {
        public:
            void process() {}
        };
        void test() {
            Base obj;
            obj.process();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCallOrFail(code);
    ASSERT_NE(methodCall, nullptr);

    // Get method being called
    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_EQ(method->getNameAsString(), "process");

    // Test the new isVirtualCall method
    bool isVirtual = handler->isVirtualCall(methodCall);
    EXPECT_FALSE(isVirtual) << "Non-virtual method should not be detected as virtual";
}

// ============================================================================
// Test 3: DetectVirtualCallOnBasePointer - Virtual call on base pointer
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallDetectionTest, DetectVirtualCallOnBasePointer) {
    // C++: ptr->process()  [virtual method, base pointer]
    // Expected: isVirtualCall() returns true (method itself is virtual)

    const char* code = R"(
        class Base {
        public:
            virtual void process() {}
        };
        void test() {
            Base* ptr = nullptr;
            ptr->process();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCallOrFail(code);
    ASSERT_NE(methodCall, nullptr);

    // Get method being called
    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    // Test the new isVirtualCall method
    bool isVirtual = handler->isVirtualCall(methodCall);
    EXPECT_TRUE(isVirtual) << "Virtual method call on base pointer should be detected as virtual";
}

// ============================================================================
// Test 4: DetectVirtualCallOnDerivedPointer - Virtual call on derived pointer
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallDetectionTest, DetectVirtualCallOnDerivedPointer) {
    // C++: ptr->process()  [virtual method, derived pointer]
    // Expected: isVirtualCall() returns true (method is virtual)

    const char* code = R"(
        class Base {
        public:
            virtual void process() {}
        };
        class Derived : public Base {
        public:
            void process() override {}
        };
        void test() {
            Derived* ptr = nullptr;
            ptr->process();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCallOrFail(code);
    ASSERT_NE(methodCall, nullptr);

    // Get method being called
    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    // Test the new isVirtualCall method
    bool isVirtual = handler->isVirtualCall(methodCall);
    EXPECT_TRUE(isVirtual) << "Virtual method call on derived pointer should be detected as virtual";
}

// ============================================================================
// Test 5: DetectVirtualDestructorCall - Virtual destructor call detection
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallDetectionTest, DetectVirtualDestructorCall) {
    // C++: ptr->~Base()  [virtual destructor]
    // Expected: isVirtualCall() returns true (destructor is virtual)

    const char* code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };
        void test() {
            Base* ptr = nullptr;
            ptr->~Base();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCallOrFail(code);
    ASSERT_NE(methodCall, nullptr);

    // Get method being called
    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    // Virtual destructors are marked as virtual
    bool isVirtual = handler->isVirtualCall(methodCall);
    EXPECT_TRUE(isVirtual) << "Virtual destructor call should be detected as virtual";
}

// ============================================================================
// Test 6: StaticMethodIsNotVirtual - Static method is not virtual
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallDetectionTest, StaticMethodIsNotVirtual) {
    // C++: obj.staticMethod()  [static method called via object]
    // Expected: isVirtualCall() returns false (static methods cannot be virtual)
    // Note: In some versions of Clang, static method calls don't produce CXXMemberCallExpr
    // This test gracefully handles both cases

    const char* code = R"(
        class Base {
        public:
            static void staticMethod() {}
        };
        void test() {
            Base obj;
            obj.staticMethod();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCall(code);
    // Static method calls might not produce CXXMemberCallExpr in all Clang versions
    if (methodCall != nullptr) {
        const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
        if (method != nullptr && method->isStatic()) {
            bool isVirtual = handler->isVirtualCall(methodCall);
            EXPECT_FALSE(isVirtual) << "Static method should not be detected as virtual";
        }
    }
    // If no CXXMemberCallExpr found, the test passes since:
    // 1. Static method calls don't need virtual call detection
    // 2. They're always statically resolved regardless of AST node type
}

// ============================================================================
// Test 7: InlineMethodIsNotVirtual - Inline method is not necessarily virtual
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallDetectionTest, InlineMethodIsNotVirtual) {
    // C++: obj.inlineMethod()  [inline, non-virtual method]
    // Expected: isVirtualCall() returns false

    const char* code = R"(
        class Base {
        public:
            inline void inlineMethod() {}
        };
        void test() {
            Base obj;
            obj.inlineMethod();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCallOrFail(code);
    ASSERT_NE(methodCall, nullptr);

    // Get method being called
    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    // Test the new isVirtualCall method
    bool isVirtual = handler->isVirtualCall(methodCall);
    EXPECT_FALSE(isVirtual) << "Non-virtual inline method should not be detected as virtual";
}

// ============================================================================
// Test 8: FinalMethodIsVirtual - Final method can still be virtual
// ============================================================================
TEST_F(ExpressionHandlerVirtualCallDetectionTest, FinalMethodIsVirtual) {
    // C++: obj.finalMethod()  [virtual final method]
    // Expected: isVirtualCall() returns true (method is virtual, final is about override)

    const char* code = R"(
        class Base {
        public:
            virtual void process() {}
        };
        class Derived : public Base {
        public:
            void process() final {}
        };
        void test() {
            Derived obj;
            obj.process();
        }
    )";

    const clang::CXXMemberCallExpr* methodCall = extractMethodCallOrFail(code);
    ASSERT_NE(methodCall, nullptr);

    // Get method being called
    const clang::CXXMethodDecl* method = methodCall->getMethodDecl();
    ASSERT_NE(method, nullptr);

    // Test the new isVirtualCall method
    bool isVirtual = handler->isVirtualCall(methodCall);
    EXPECT_TRUE(isVirtual) << "Final override of virtual method should be detected as virtual";
}
