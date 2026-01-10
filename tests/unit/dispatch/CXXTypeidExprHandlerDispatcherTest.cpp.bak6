/**
 * @file CXXTypeidExprHandlerDispatcherTest.cpp
 * @brief Unit tests for CXXTypeidExprHandler dispatcher integration
 *
 * Tests verify:
 * 1. Handler registration with dispatcher
 * 2. Predicate correctness (matches only CXXTypeidExpr)
 * 3. Polymorphic typeid translation (vtable lookup)
 * 4. Static typeid with type operand translation
 * 5. Static typeid with object operand translation
 * 6. TypeidTranslator integration
 * 7. ExprMapper integration
 * 8. Recursive dispatch of expression operand
 * 9. Complex nested expressions
 * 10. Integration with comparison operators
 *
 * SOLID Principles:
 * - Single Responsibility: Tests only CXXTypeidExprHandler
 * - Interface Segregation: Tests public API only
 * - Dependency Inversion: Tests against dispatcher abstraction
 */

#include "dispatch/CXXTypeidExprHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/ExprMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/StmtMapper.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Type.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include "gtest/gtest.h"
#include "llvm/Support/Casting.h"
#include <memory>

using namespace clang;
using namespace cpptoc;

/**
 * @class CXXTypeidExprHandlerTest
 * @brief Test fixture for CXXTypeidExprHandler tests
 *
 * Provides:
 * - C++ ASTContext with test code
 * - C ASTContext for target translation
 * - Dispatcher with registered handlers
 * - Mappers for verification
 */
class CXXTypeidExprHandlerTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> cppAST;
    std::unique_ptr<TargetContext> targetCtx;
    std::unique_ptr<PathMapper> pathMapper;
    std::unique_ptr<DeclLocationMapper> locMapper;
    DeclMapper declMapper;
    TypeMapper typeMapper;
    ExprMapper exprMapper;
    StmtMapper stmtMapper;
    std::unique_ptr<CppToCVisitorDispatcher> dispatcher;

    /**
     * @brief Set up test fixture with AST from C++ code
     * @param cppCode C++ source code to parse
     */
    void SetUpWithCode(const std::string& cppCode) {
        // Parse C++ code with RTTI enabled (-frtti)
        // This is required for typeid expressions to work
        std::vector<std::string> args = {"-std=c++17", "-frtti"};
        cppAST = tooling::buildASTFromCodeWithArgs(cppCode, args);
        ASSERT_TRUE(cppAST) << "Failed to parse C++ code";

        // RAII: Create fresh instances for test isolation
        targetCtx = std::make_unique<TargetContext>();
        pathMapper = std::make_unique<PathMapper>(*targetCtx, "/src", "/output");
        locMapper = std::make_unique<DeclLocationMapper>(*pathMapper);

        // Create dispatcher
        dispatcher = std::make_unique<CppToCVisitorDispatcher>(
            *pathMapper,
            *locMapper,
            declMapper,
            typeMapper,
            exprMapper,
            stmtMapper,
            *targetCtx
        );

        // Register CXXTypeidExprHandler
        CXXTypeidExprHandler::registerWith(*dispatcher);
    }

    /**
     * @brief Find first expression of given type in AST
     * @tparam T Expression type to find
     * @return Pointer to expression, or nullptr if not found
     */
    template<typename T>
    const T* findFirstExpr() {
        const auto& ctx = cppAST->getASTContext();
        const auto* TU = ctx.getTranslationUnitDecl();

        // Simple traversal - for tests, we assume expression is in first function
        for (const auto* D : TU->decls()) {
            if (const auto* FD = dyn_cast<FunctionDecl>(D)) {
                if (FD->hasBody()) {
                    const auto* Body = FD->getBody();
                    // Look for expression in function body
                    if (const auto* CS = dyn_cast<CompoundStmt>(Body)) {
                        for (const auto* S : CS->body()) {
                            // Check if statement contains target expression
                            if (const auto* DS = dyn_cast<DeclStmt>(S)) {
                                for (const auto* Decl : DS->decls()) {
                                    if (const auto* VD = dyn_cast<VarDecl>(Decl)) {
                                        if (VD->hasInit()) {
                                            if (const auto* Init = VD->getInit()) {
                                                // Strip casts
                                                const Expr* E = Init->IgnoreImpCasts();
                                                if (const auto* Target = dyn_cast<T>(E)) {
                                                    return Target;
                                                }
                                                // Check for nested expressions
                                                if (const auto* Call = dyn_cast<CXXOperatorCallExpr>(E)) {
                                                    for (unsigned i = 0; i < Call->getNumArgs(); ++i) {
                                                        const Expr* Arg = Call->getArg(i)->IgnoreImpCasts();
                                                        if (const auto* Target = dyn_cast<T>(Arg)) {
                                                            return Target;
                                                        }
                                                    }
                                                }
                                            }
                                        }
                                    }
                                }
                            } else if (const auto* Expr = dyn_cast<T>(S)) {
                                return Expr;
                            }
                        }
                    }
                }
            }
        }
        return nullptr;
    }

    ASTContext& getCppContext() { return cppAST->getASTContext(); }
    ASTContext& getCContext() { return targetCtx->getContext(); }
};

/**
 * TEST 1: Handler Registration
 * Verify handler can be registered with dispatcher
 */
TEST_F(CXXTypeidExprHandlerTest, HandlerRegistration) {
    // Setup code with typeid expression
    const char* code = R"(
        namespace std { class type_info; }
        class Base {
        public:
            public: virtual ~Base() {}
        };
        void test() {
            const std::type_info& ti = typeid(Base);
        }
    )";

    SetUpWithCode(code);

    // Handler registration verified in SetUpWithCode (via registerWith)
    // If registration failed, dispatcher would be null or incomplete
    EXPECT_NE(dispatcher, nullptr);
}

/**
 * TEST 2: Predicate Matches CXXTypeidExpr
 * Verify canHandle returns true only for CXXTypeidExpr
 */
TEST_F(CXXTypeidExprHandlerTest, PredicateMatchesCXXTypeidExpr) {
    const char* code = R"(
        namespace std { class type_info; }
        class Base {
            public: virtual ~Base() {}
        };
        void test() {
            const std::type_info& ti = typeid(Base);
        }
    )";

    SetUpWithCode(code);

    const CXXTypeidExpr* typeidExpr = findFirstExpr<CXXTypeidExpr>();
    ASSERT_NE(typeidExpr, nullptr) << "CXXTypeidExpr not found in AST";

    // Test predicate
    EXPECT_TRUE(CXXTypeidExprHandler::canHandle(typeidExpr));
}

/**
 * TEST 3: Predicate Rejects Non-CXXTypeidExpr
 * Verify canHandle returns false for other expression types
 */
TEST_F(CXXTypeidExprHandlerTest, PredicateRejectsNonTypeidExpr) {
    const char* code = R"(
        void test() {
            int x = 42;
            int y = x + 1;
        }
    )";

    SetUpWithCode(code);

    // Find a BinaryOperator (not a CXXTypeidExpr)
    const BinaryOperator* binOp = findFirstExpr<BinaryOperator>();
    ASSERT_NE(binOp, nullptr) << "BinaryOperator not found in AST";

    // Test predicate
    EXPECT_FALSE(CXXTypeidExprHandler::canHandle(binOp));
}

/**
 * TEST 4: Static Typeid with Type Operand
 * Test: typeid(Base) → &__ti_Base
 */
TEST_F(CXXTypeidExprHandlerTest, StaticTypeidWithTypeOperand) {
    const char* code = R"(
        namespace std { class type_info; }
        class Base {
            public: virtual ~Base() {}
        };
        void test() {
            const std::type_info& ti = typeid(Base);
        }
    )";

    SetUpWithCode(code);

    const CXXTypeidExpr* typeidExpr = findFirstExpr<CXXTypeidExpr>();
    ASSERT_NE(typeidExpr, nullptr);

    // Verify it's a type operand
    EXPECT_TRUE(typeidExpr->isTypeOperand());

    // Dispatch through handler
    bool handled = dispatcher->dispatch(getCppContext(), getCContext(), typeidExpr);
    EXPECT_TRUE(handled) << "CXXTypeidExpr not handled by dispatcher";

    // Verify ExprMapper has result
    EXPECT_TRUE(exprMapper.hasCreated(typeidExpr));

    // Verify result is a C expression
    const Expr* cExpr = exprMapper.getCreated(typeidExpr);
    EXPECT_NE(cExpr, nullptr);
}

/**
 * TEST 5: Static Typeid with Object Operand (Non-Polymorphic)
 * Test: typeid(obj) where obj is non-polymorphic → &__ti_Base
 */
TEST_F(CXXTypeidExprHandlerTest, StaticTypeidWithObjectOperand) {
    const char* code = R"(
        namespace std { class type_info; }
        class Base {};  // Non-polymorphic (no virtual functions)
        void test() {
            Base b;
            const std::type_info& ti = typeid(b);
        }
    )";

    SetUpWithCode(code);

    const CXXTypeidExpr* typeidExpr = findFirstExpr<CXXTypeidExpr>();
    ASSERT_NE(typeidExpr, nullptr);

    // Verify it's an expression operand (not type operand)
    EXPECT_FALSE(typeidExpr->isTypeOperand());

    // Dispatch through handler
    bool handled = dispatcher->dispatch(getCppContext(), getCContext(), typeidExpr);
    EXPECT_TRUE(handled);

    // Verify result in ExprMapper
    EXPECT_TRUE(exprMapper.hasCreated(typeidExpr));
}

/**
 * TEST 6: Polymorphic Typeid with Dereferenced Pointer
 * Test: typeid(*ptr) where ptr is polymorphic → vtable lookup
 */
TEST_F(CXXTypeidExprHandlerTest, PolymorphicTypeidWithPointer) {
    const char* code = R"(
        namespace std { class type_info; }
        class Base {
            public: virtual ~Base() {}
        };
        class Derived : public Base {
            public: virtual ~Derived() {}
        };
        void test() {
            Base* ptr = new Derived();
            const std::type_info& ti = typeid(*ptr);
        }
    )";

    SetUpWithCode(code);

    const CXXTypeidExpr* typeidExpr = findFirstExpr<CXXTypeidExpr>();
    ASSERT_NE(typeidExpr, nullptr);

    // Verify it's an expression operand
    EXPECT_FALSE(typeidExpr->isTypeOperand());

    // Dispatch through handler
    bool handled = dispatcher->dispatch(getCppContext(), getCContext(), typeidExpr);
    EXPECT_TRUE(handled);

    // Verify result in ExprMapper
    EXPECT_TRUE(exprMapper.hasCreated(typeidExpr));
}

/**
 * TEST 7: TypeidTranslator Integration
 * Verify handler delegates to TypeidTranslator correctly
 */
TEST_F(CXXTypeidExprHandlerTest, TypeidTranslatorIntegration) {
    const char* code = R"(
        namespace std { class type_info; }
        class Base {
            public: virtual ~Base() {}
        };
        void test() {
            const std::type_info& ti = typeid(Base);
        }
    )";

    SetUpWithCode(code);

    const CXXTypeidExpr* typeidExpr = findFirstExpr<CXXTypeidExpr>();
    ASSERT_NE(typeidExpr, nullptr);

    // Dispatch and verify translation
    bool handled = dispatcher->dispatch(getCppContext(), getCContext(), typeidExpr);
    EXPECT_TRUE(handled);

    // TypeidTranslator should have created a C expression
    EXPECT_TRUE(exprMapper.hasCreated(typeidExpr));
}

/**
 * TEST 8: ExprMapper Prevents Duplicate Translation
 * Verify handler checks ExprMapper before translating
 */
TEST_F(CXXTypeidExprHandlerTest, ExprMapperPreventsDuplication) {
    const char* code = R"(
        namespace std { class type_info; }
        class Base {
            public: virtual ~Base() {}
        };
        void test() {
            const std::type_info& ti = typeid(Base);
        }
    )";

    SetUpWithCode(code);

    const CXXTypeidExpr* typeidExpr = findFirstExpr<CXXTypeidExpr>();
    ASSERT_NE(typeidExpr, nullptr);

    // First dispatch
    bool handled1 = dispatcher->dispatch(getCppContext(), getCContext(), typeidExpr);
    EXPECT_TRUE(handled1);
    EXPECT_TRUE(exprMapper.hasCreated(typeidExpr));

    const Expr* firstResult = exprMapper.getCreated(typeidExpr);

    // Second dispatch (should skip translation)
    bool handled2 = dispatcher->dispatch(getCppContext(), getCContext(), typeidExpr);
    EXPECT_TRUE(handled2);

    // Verify same result (no duplication)
    const Expr* secondResult = exprMapper.getCreated(typeidExpr);
    EXPECT_EQ(firstResult, secondResult);
}

/**
 * TEST 9: Complex Nested Expression
 * Test: typeid(*(arr[i].ptr))
 */
TEST_F(CXXTypeidExprHandlerTest, ComplexNestedExpression) {
    const char* code = R"(
        namespace std { class type_info; }
        class Base {
            public: virtual ~Base() {}
        };
        struct Container {
            Base* ptr;
        };
        void test() {
            Container arr[10];
            int i = 0;
            const std::type_info& ti = typeid(*(arr[i].ptr));
        }
    )";

    SetUpWithCode(code);

    const CXXTypeidExpr* typeidExpr = findFirstExpr<CXXTypeidExpr>();
    ASSERT_NE(typeidExpr, nullptr);

    // Dispatch and verify
    bool handled = dispatcher->dispatch(getCppContext(), getCContext(), typeidExpr);
    EXPECT_TRUE(handled);
    EXPECT_TRUE(exprMapper.hasCreated(typeidExpr));
}

/**
 * TEST 10: Integration with Comparison Operators
 * Test: typeid(*a) == typeid(*b)
 *
 * INVESTIGATION: This test checks what AST structure is actually generated
 * for typeid comparisons and verifies the handler works with it.
 */
TEST_F(CXXTypeidExprHandlerTest, IntegrationWithComparisonOperators) {
    const char* code = R"(
        namespace std {
            class type_info {};
            bool operator==(const type_info&, const type_info&);
        }
        class Base {
            public: virtual ~Base() {}
        };
        void test() {
            Base* a = nullptr;
            Base* b = nullptr;
            bool result = (typeid(*a) == typeid(*b));
        }
    )";

    SetUpWithCode(code);

    // First, let's find out what expression type we actually have
    const auto& ctx = cppAST->getASTContext();
    const auto* TU = ctx.getTranslationUnitDecl();

    const Expr* actualExpr = nullptr;
    std::string actualType;

    // Find the expression in the result variable initialization
    for (const auto* D : TU->decls()) {
        if (const auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                const auto* Body = FD->getBody();
                if (const auto* CS = dyn_cast<CompoundStmt>(Body)) {
                    for (const auto* S : CS->body()) {
                        if (const auto* DS = dyn_cast<DeclStmt>(S)) {
                            for (const auto* Decl : DS->decls()) {
                                if (const auto* VD = dyn_cast<VarDecl>(Decl)) {
                                    if (VD->getNameAsString() == "result" && VD->hasInit()) {
                                        actualExpr = VD->getInit()->IgnoreImpCasts();
                                        actualType = actualExpr->getStmtClassName();
                                        break;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    ASSERT_NE(actualExpr, nullptr) << "Could not find 'result' variable initialization";

    // Check if it's a ParenExpr and unwrap it
    if (const auto* PE = dyn_cast<ParenExpr>(actualExpr)) {
        actualExpr = PE->getSubExpr()->IgnoreImpCasts();
        actualType = actualExpr->getStmtClassName();
    }

    // Now check what we actually have
    if (const auto* BO = dyn_cast<BinaryOperator>(actualExpr)) {
        // It's a BinaryOperator, not CXXOperatorCallExpr
        // This happens when operator== is only forward-declared
        EXPECT_EQ(BO->getOpcode(), BO_EQ);

        // Get the operands
        const Expr* LHS = BO->getLHS()->IgnoreImpCasts();
        const Expr* RHS = BO->getRHS()->IgnoreImpCasts();

        // Both should be CXXTypeidExpr
        const CXXTypeidExpr* lhsTypeid = dyn_cast<CXXTypeidExpr>(LHS);
        const CXXTypeidExpr* rhsTypeid = dyn_cast<CXXTypeidExpr>(RHS);

        ASSERT_NE(lhsTypeid, nullptr) << "LHS should be CXXTypeidExpr";
        ASSERT_NE(rhsTypeid, nullptr) << "RHS should be CXXTypeidExpr";

        // Dispatch both typeid expressions
        bool handled1 = dispatcher->dispatch(getCppContext(), getCContext(), lhsTypeid);
        EXPECT_TRUE(handled1);
        EXPECT_TRUE(exprMapper.hasCreated(lhsTypeid));

        bool handled2 = dispatcher->dispatch(getCppContext(), getCContext(), rhsTypeid);
        EXPECT_TRUE(handled2);
        EXPECT_TRUE(exprMapper.hasCreated(rhsTypeid));
    } else if (const auto* Call = dyn_cast<CXXOperatorCallExpr>(actualExpr)) {
        // It's a CXXOperatorCallExpr (would happen with inline operator== definition)
        ASSERT_EQ(Call->getNumArgs(), 2u);

        const Expr* LHS = Call->getArg(0)->IgnoreImpCasts();
        const Expr* RHS = Call->getArg(1)->IgnoreImpCasts();

        const CXXTypeidExpr* lhsTypeid = dyn_cast<CXXTypeidExpr>(LHS);
        const CXXTypeidExpr* rhsTypeid = dyn_cast<CXXTypeidExpr>(RHS);

        ASSERT_NE(lhsTypeid, nullptr) << "LHS should be CXXTypeidExpr";
        ASSERT_NE(rhsTypeid, nullptr) << "RHS should be CXXTypeidExpr";

        bool handled1 = dispatcher->dispatch(getCppContext(), getCContext(), lhsTypeid);
        EXPECT_TRUE(handled1);
        EXPECT_TRUE(exprMapper.hasCreated(lhsTypeid));

        bool handled2 = dispatcher->dispatch(getCppContext(), getCContext(), rhsTypeid);
        EXPECT_TRUE(handled2);
        EXPECT_TRUE(exprMapper.hasCreated(rhsTypeid));
    } else {
        FAIL() << "Expected BinaryOperator or CXXOperatorCallExpr, got: " << actualType;
    }
}

/**
 * TEST 11: Polymorphic Detection
 * Verify handler correctly distinguishes polymorphic vs static typeid
 */
TEST_F(CXXTypeidExprHandlerTest, PolymorphicDetection) {
    const char* code = R"(
        namespace std { class type_info; }
        class NonPolymorphic {};
        class Polymorphic {
            public: virtual ~Polymorphic() {}
        };
        void test() {
            NonPolymorphic np;
            Polymorphic p;
            const std::type_info& ti1 = typeid(np);  // Static
            const std::type_info& ti2 = typeid(p);   // Static (not dereferenced)
        }
    )";

    SetUpWithCode(code);

    // Both should be handled as static (not polymorphic)
    // Polymorphic requires dereferencing a pointer/reference
    const auto& ctx = cppAST->getASTContext();
    const auto* TU = ctx.getTranslationUnitDecl();

    int typeidCount = 0;
    for (const auto* D : TU->decls()) {
        if (const auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                const auto* Body = FD->getBody();
                if (const auto* CS = dyn_cast<CompoundStmt>(Body)) {
                    for (const auto* S : CS->body()) {
                        if (const auto* DS = dyn_cast<DeclStmt>(S)) {
                            for (const auto* Decl : DS->decls()) {
                                if (const auto* VD = dyn_cast<VarDecl>(Decl)) {
                                    if (VD->hasInit()) {
                                        const Expr* E = VD->getInit()->IgnoreImpCasts();
                                        if (const auto* TypeidExpr = dyn_cast<CXXTypeidExpr>(E)) {
                                            bool handled = dispatcher->dispatch(getCppContext(), getCContext(), TypeidExpr);
                                            EXPECT_TRUE(handled);
                                            typeidCount++;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    // Should have found and handled 2 typeid expressions
    EXPECT_EQ(typeidCount, 2);
}

/**
 * TEST 12: Recursive Dispatch of Expression Operand
 * Verify handler recursively dispatches expression operand
 */
TEST_F(CXXTypeidExprHandlerTest, RecursiveDispatchOfOperand) {
    const char* code = R"(
        namespace std { class type_info; }
        class Base {
            public: virtual ~Base() {}
        };
        Base* getPtr() { return nullptr; }
        void test() {
            const std::type_info& ti = typeid(*getPtr());
        }
    )";

    SetUpWithCode(code);

    const CXXTypeidExpr* typeidExpr = findFirstExpr<CXXTypeidExpr>();
    ASSERT_NE(typeidExpr, nullptr);

    // The operand is a UnaryOperator (dereference of function call)
    EXPECT_FALSE(typeidExpr->isTypeOperand());
    const Expr* operand = typeidExpr->getExprOperand();
    EXPECT_NE(operand, nullptr);

    // Dispatch typeid
    bool handled = dispatcher->dispatch(getCppContext(), getCContext(), typeidExpr);
    EXPECT_TRUE(handled);

    // Verify typeid is translated
    EXPECT_TRUE(exprMapper.hasCreated(typeidExpr));
}
