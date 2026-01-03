/**
 * @file ExpressionHandlerTest_VirtualCallMultipleInheritance.cpp
 * @brief TDD tests for ExpressionHandler - Virtual Call Through Base Pointer (Phase 46 Task 10)
 *
 * Tests virtual method call routing through multiple lpVtbl pointers based on base class.
 * Pattern:
 * - Primary base: obj->lpVtbl->method(obj, args...)
 * - Non-primary base: obj->lpVtbl->method(obj, args...)  // BUT obj points to lpVtbl2 field!
 *
 * Key Insight:
 * When you have Base2* b2 pointing to Derived object, b2 points to the lpVtbl2 field.
 * From Base2's perspective, it always uses obj->lpVtbl (the first field in Base2).
 * But that lpVtbl is actually Derived::lpVtbl2 due to pointer adjustment.
 *
 * Following strict TDD: Red → Green → Refactor
 *
 * Test Plan (18 tests):
 * 1. VirtualCallThroughPrimaryBase - Base1* b1; b1->method() → b1->lpVtbl->method(b1)
 * 2. VirtualCallThroughNonPrimaryBase - Base2* b2; b2->method() → b2->lpVtbl->method(b2)
 * 3. VirtualCallThroughDerivedPointer - Derived* d; d->baseMethod() → uses correct lpVtbl
 * 4. CallPrimaryBaseThenNonPrimary - Multiple calls through different bases
 * 5. NonPrimaryWithParameters - b2->method(a, b) with non-primary base
 * 6. NonPrimaryWithReturnValue - int x = b2->getValue() with non-primary base
 * 7. ThreeBasesCallThroughThird - Base3* b3; b3->method() (lpVtbl3 scenario)
 * 8. PolymorphicCallInLoop - for loop calling through base pointer
 * 9. VirtualCallThroughReference - Base2& ref; ref.method()
 * 10. CastThenVirtualCall - ((Base2*)derived)->method()
 * 11. ChainedCallsThroughBases - b1->getNext()->method()
 * 12. VirtualCallInConditional - if (b2->isValid()) with non-primary base
 * 13. VirtualCallInExpression - result = b2->getValue() + 10
 * 14. MixedPrimaryNonPrimaryInSameFunction - Both types of calls in one function
 * 15. CallOverriddenMethodThroughBase - Derived overrides, call through base
 * 16. CallInheritedMethodThroughBase - Method not overridden, call through base
 * 17. ComplexExpressionWithBaseCall - b2->method(a + b * c, obj.field)
 * 18. EdgeCaseSingleInheritanceStillWorks - Ensure backward compatibility
 */

#include "helpers/UnitTestHelper.h"
#include "CNodeBuilder.h"
#include "MultipleInheritanceAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/ExprCXX.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;

/**
 * @class ExpressionHandlerVirtualCallMultipleInheritanceTest
 * @brief Test fixture for virtual call routing through multiple bases
 */
class ExpressionHandlerVirtualCallMultipleInheritanceTest : public ::testing::Test {
protected:
    UnitTestContext ctx;
    std::unique_ptr<MultipleInheritanceAnalyzer> miAnalyzer;

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

        // Recreate analyzer with new AST
        miAnalyzer = std::make_unique<MultipleInheritanceAnalyzer>(cppAST->getASTContext());

        Visitor visitor;
        visitor.TraverseDecl(cppAST->getASTContext().getTranslationUnitDecl());

        EXPECT_NE(visitor.foundCall, nullptr) << "No CXXMemberCallExpr found in code: " << code;
        return visitor.foundCall;
    }

    /**
     * @brief Helper to get the object type from a member call expression
     */
    const clang::Type* getObjectType(const clang::CXXMemberCallExpr* MCE) {
        if (!MCE) return nullptr;
        const clang::Expr* objExpr = MCE->getImplicitObjectArgument();
        if (!objExpr) return nullptr;
        clang::QualType qt = objExpr->getType();
        if (qt->isPointerType()) {
            return qt->getPointeeType().getTypePtr();
        }
        if (qt->isReferenceType()) {
            return qt->getPointeeType().getTypePtr();
        }
        return qt.getTypePtr();
    }
};

// ============================================================================
// Test 1: Virtual Call Through Primary Base
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, VirtualCallThroughPrimaryBase) {
    // C++ Code:
    // class Base1 { virtual void draw() {} };
    // class Base2 { virtual void serialize() {} };
    // class Derived : public Base1, public Base2 {
    //     void draw() override {}
    //     void serialize() override {}
    // };
    // void test(Base1* b1) {
    //     b1->draw();  // Call through primary base
    // }

    const char* code = R"(
        class Base1 {
        public:
            virtual void draw() {}
        };
        class Base2 {
        public:
            virtual void serialize() {}
        };
        class Derived : public Base1, public Base2 {
        public:
            void draw() override {}
            void serialize() override {}
        };
        void test(Base1* b1) {
            b1->draw();
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);

    // Verify it's a virtual call
    EXPECT_TRUE(handler->isVirtualCall(call));

    // Get the method
    const clang::CXXMethodDecl* method = call->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_EQ(method->getNameAsString(), "draw");

    // Get the class being called through (Base1)
    const clang::Type* objectType = getObjectType(call);
    ASSERT_NE(objectType, nullptr);
    const clang::CXXRecordDecl* objectClass = objectType->getAsCXXRecordDecl();
    ASSERT_NE(objectClass, nullptr);
    EXPECT_EQ(objectClass->getNameAsString(), "Base1");

    // Expected behavior:
    // - Base1 is the primary base of Derived
    // - Call through Base1* should use lpVtbl (the first vtable pointer)
    // - Pattern: b1->lpVtbl->draw(b1)

    // NOTE: The actual translation will happen in ExpressionHandler::translateVirtualCall
    // For now, we're testing that we can identify this is a call through the primary base
}

// ============================================================================
// Test 2: Virtual Call Through Non-Primary Base
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, VirtualCallThroughNonPrimaryBase) {
    // C++ Code:
    // void test(Base2* b2) {
    //     b2->serialize();  // Call through non-primary base
    // }

    const char* code = R"(
        class Base1 {
        public:
            virtual void draw() {}
        };
        class Base2 {
        public:
            virtual void serialize() {}
        };
        class Derived : public Base1, public Base2 {
        public:
            void draw() override {}
            void serialize() override {}
        };
        void test(Base2* b2) {
            b2->serialize();
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);

    // Verify it's a virtual call
    EXPECT_TRUE(handler->isVirtualCall(call));

    // Get the method
    const clang::CXXMethodDecl* method = call->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_EQ(method->getNameAsString(), "serialize");

    // Get the class being called through (Base2)
    const clang::Type* objectType = getObjectType(call);
    ASSERT_NE(objectType, nullptr);
    const clang::CXXRecordDecl* objectClass = objectType->getAsCXXRecordDecl();
    ASSERT_NE(objectClass, nullptr);
    EXPECT_EQ(objectClass->getNameAsString(), "Base2");

    // Expected behavior:
    // - Base2 is a non-primary base
    // - BUT: When calling through Base2*, the pointer points to the lpVtbl2 field
    // - From Base2's perspective, it still uses obj->lpVtbl (which is Derived::lpVtbl2)
    // - Pattern: b2->lpVtbl->serialize(b2)
    // - The key is that b2 already points to the correct offset due to pointer adjustment
}

// ============================================================================
// Test 3: Virtual Call Through Derived Pointer
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, VirtualCallThroughDerivedPointer) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void draw() {}
        };
        class Derived : public Base1 {
        public:
            void draw() override {}
        };
        void test(Derived* d) {
            d->draw();
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);

    // When calling through Derived*, we use the primary lpVtbl
    EXPECT_TRUE(handler->isVirtualCall(call));

    const clang::Type* objectType = getObjectType(call);
    ASSERT_NE(objectType, nullptr);
    const clang::CXXRecordDecl* objectClass = objectType->getAsCXXRecordDecl();
    ASSERT_NE(objectClass, nullptr);
    EXPECT_EQ(objectClass->getNameAsString(), "Derived");
}

// ============================================================================
// Test 4: Call Primary Base Then Non-Primary
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, CallPrimaryBaseThenNonPrimary) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void draw() {}
        };
        class Base2 {
        public:
            virtual void serialize() {}
        };
        class Derived : public Base1, public Base2 {
        public:
            void draw() override {}
            void serialize() override {}
        };
        void test(Base1* b1, Base2* b2) {
            b1->draw();
            b2->serialize();
        }
    )";

    // This test verifies we can handle multiple calls in the same function
    // We'll just check that the code parses correctly
    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);
}

// ============================================================================
// Test 5: Non-Primary With Parameters
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, NonPrimaryWithParameters) {
    const char* code = R"(
        class Base2 {
        public:
            virtual void setData(int x, int y) {}
        };
        class Derived : public Base2 {
        public:
            void setData(int x, int y) override {}
        };
        void test(Base2* b2, int a, int b) {
            b2->setData(a, b);
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);

    // Verify it has parameters
    EXPECT_EQ(call->getNumArgs(), 2);
    EXPECT_TRUE(handler->isVirtualCall(call));
}

// ============================================================================
// Test 6: Non-Primary With Return Value
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, NonPrimaryWithReturnValue) {
    const char* code = R"(
        class Base2 {
        public:
            virtual int getValue() { return 0; }
        };
        class Derived : public Base2 {
        public:
            int getValue() override { return 42; }
        };
        void test(Base2* b2) {
            int x = b2->getValue();
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);

    // Verify return type
    EXPECT_TRUE(call->getType()->isIntegerType());
    EXPECT_TRUE(handler->isVirtualCall(call));
}

// ============================================================================
// Test 7: Three Bases Call Through Third
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, ThreeBasesCallThroughThird) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void method1() {}
        };
        class Base2 {
        public:
            virtual void method2() {}
        };
        class Base3 {
        public:
            virtual void method3() {}
        };
        class Derived : public Base1, public Base2, public Base3 {
        public:
            void method1() override {}
            void method2() override {}
            void method3() override {}
        };
        void test(Base3* b3) {
            b3->method3();
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);

    const clang::Type* objectType = getObjectType(call);
    ASSERT_NE(objectType, nullptr);
    const clang::CXXRecordDecl* objectClass = objectType->getAsCXXRecordDecl();
    ASSERT_NE(objectClass, nullptr);
    EXPECT_EQ(objectClass->getNameAsString(), "Base3");

    // Base3 would be the second non-primary base (lpVtbl3)
    EXPECT_TRUE(handler->isVirtualCall(call));
}

// ============================================================================
// Test 8: Polymorphic Call In Loop
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, PolymorphicCallInLoop) {
    const char* code = R"(
        class Base {
        public:
            virtual void process() {}
        };
        class Derived : public Base {
        public:
            void process() override {}
        };
        void test(Base** array, int count) {
            for (int i = 0; i < count; i++) {
                array[i]->process();
            }
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);
    EXPECT_TRUE(handler->isVirtualCall(call));
}

// ============================================================================
// Test 9: Virtual Call Through Reference
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, VirtualCallThroughReference) {
    const char* code = R"(
        class Base2 {
        public:
            virtual void serialize() {}
        };
        class Derived : public Base2 {
        public:
            void serialize() override {}
        };
        void test(Base2& ref) {
            ref.serialize();
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);

    // References are converted to pointers by Clang in the implicit object argument
    const clang::Expr* objExpr = call->getImplicitObjectArgument();
    ASSERT_NE(objExpr, nullptr);
    // The implicit cast will make it a pointer, but the original type is reference
    // Just verify it's a virtual call
    EXPECT_TRUE(handler->isVirtualCall(call));
}

// ============================================================================
// Test 10: Cast Then Virtual Call
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, CastThenVirtualCall) {
    const char* code = R"(
        class Base {
        public:
            virtual void method() {}
        };
        class Derived : public Base {
        public:
            void method() override {}
        };
        void test(void* ptr) {
            ((Base*)ptr)->method();
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);
    EXPECT_TRUE(handler->isVirtualCall(call));
}

// ============================================================================
// Test 11: Chained Calls Through Bases
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, ChainedCallsThroughBases) {
    const char* code = R"(
        class Node {
        public:
            virtual Node* getNext() { return nullptr; }
        };
        class DerivedNode : public Node {
        public:
            Node* getNext() override { return nullptr; }
        };
        void test(Node* n) {
            Node* next = n->getNext();
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);
    EXPECT_TRUE(handler->isVirtualCall(call));
}

// ============================================================================
// Test 12: Virtual Call In Conditional
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, VirtualCallInConditional) {
    const char* code = R"(
        class Base {
        public:
            virtual bool isValid() { return true; }
        };
        class Derived : public Base {
        public:
            bool isValid() override { return false; }
        };
        void test(Base* b) {
            if (b->isValid()) {
                // do something
            }
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);
    EXPECT_TRUE(handler->isVirtualCall(call));
}

// ============================================================================
// Test 13: Virtual Call In Expression
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, VirtualCallInExpression) {
    const char* code = R"(
        class Base {
        public:
            virtual int getValue() { return 0; }
        };
        class Derived : public Base {
        public:
            int getValue() override { return 42; }
        };
        void test(Base* b) {
            int result = b->getValue() + 10;
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);
    EXPECT_TRUE(handler->isVirtualCall(call));
}

// ============================================================================
// Test 14: Mixed Primary Non-Primary In Same Function
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, MixedPrimaryNonPrimaryInSameFunction) {
    const char* code = R"(
        class Base1 {
        public:
            virtual void method1() {}
        };
        class Base2 {
        public:
            virtual void method2() {}
        };
        class Derived : public Base1, public Base2 {
        public:
            void method1() override {}
            void method2() override {}
        };
        void test(Derived* d) {
            d->method1();  // Call primary base method
            d->method2();  // Call non-primary base method
        }
    )";

    cppAST = clang::tooling::buildASTFromCode(code);
    ASSERT_NE(cppAST, nullptr);
}

// ============================================================================
// Test 15: Call Overridden Method Through Base
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, CallOverriddenMethodThroughBase) {
    const char* code = R"(
        class Base {
        public:
            virtual void method() {}
        };
        class Derived : public Base {
        public:
            void method() override {}  // Overrides Base::method
        };
        void test(Base* b) {
            b->method();  // Should call Derived::method at runtime
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);

    const clang::CXXMethodDecl* method = call->getMethodDecl();
    ASSERT_NE(method, nullptr);
    EXPECT_TRUE(method->isVirtual());
}

// ============================================================================
// Test 16: Call Inherited Method Through Base
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, CallInheritedMethodThroughBase) {
    const char* code = R"(
        class Base {
        public:
            virtual void method() {}
        };
        class Derived : public Base {
            // Does NOT override method
        };
        void test(Base* b) {
            b->method();  // Calls Base::method
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);
    EXPECT_TRUE(handler->isVirtualCall(call));
}

// ============================================================================
// Test 17: Complex Expression With Base Call
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, ComplexExpressionWithBaseCall) {
    const char* code = R"(
        class Data {
        public:
            int field;
        };
        class Base {
        public:
            virtual void process(int x, int y) {}
        };
        class Derived : public Base {
        public:
            void process(int x, int y) override {}
        };
        void test(Base* b, int a, int b_val, int c, Data obj) {
            b->process(a + b_val * c, obj.field);
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);
    EXPECT_TRUE(handler->isVirtualCall(call));
    EXPECT_EQ(call->getNumArgs(), 2);
}

// ============================================================================
// Test 18: Edge Case Single Inheritance Still Works
// ============================================================================

TEST_F(ExpressionHandlerVirtualCallMultipleInheritanceTest, EdgeCaseSingleInheritanceStillWorks) {
    const char* code = R"(
        class Base {
        public:
            virtual void method() {}
        };
        class Derived : public Base {
        public:
            void method() override {}
        };
        void test(Base* b) {
            b->method();
        }
    )";

    const clang::CXXMemberCallExpr* call = extractMethodCall(code);
    ASSERT_NE(call, nullptr);

    // Single inheritance should still use lpVtbl (no change from Phase 45)
    EXPECT_TRUE(handler->isVirtualCall(call));

    const clang::Type* objectType = getObjectType(call);
    ASSERT_NE(objectType, nullptr);
    const clang::CXXRecordDecl* objectClass = objectType->getAsCXXRecordDecl();
    ASSERT_NE(objectClass, nullptr);

    // Verify it's single inheritance
    miAnalyzer = std::make_unique<MultipleInheritanceAnalyzer>(cppAST->getASTContext());
    EXPECT_FALSE(miAnalyzer->hasMultiplePolymorphicBases(objectClass));
}
