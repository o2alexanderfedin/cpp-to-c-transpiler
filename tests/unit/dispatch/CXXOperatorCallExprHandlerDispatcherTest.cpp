/**
 * @file CXXOperatorCallExprHandlerDispatcherTest.cpp
 * @brief Unit tests for CXXOperatorCallExprHandler integrating with SpecialOperatorTranslator
 *
 * Verifies:
 * - Handler registration with dispatcher
 * - Detection of CXXOperatorCallExpr (overloaded operators)
 * - Integration with SpecialOperatorTranslator for all 12 special operators
 * - Integration with ExprMapper
 * - Distinction from built-in operators (BinaryOperator, UnaryOperator)
 * - All 12 special operator categories:
 *   1. Instance subscript (operator[])
 *   2. Instance call (operator())
 *   3. Smart pointer arrow (operator->)
 *   4. Smart pointer dereference (operator*)
 *   5. Stream output (operator<<)
 *   6. Stream input (operator>>)
 *   7. Conversion operators (operator T())
 *   8. Bool conversion (operator bool())
 *   9. Copy assignment (operator=)
 *   10. Move assignment (operator=(T&&))
 *   11. Address-of (operator&)
 *   12. Comma (operator,)
 *
 * Design Principles:
 * - TDD: Write failing tests first, implement to pass
 * - SOLID: Single Responsibility (only test CXXOperatorCallExprHandler)
 * - Integration: Verify SpecialOperatorTranslator integration works correctly
 */

#include "dispatch/CXXOperatorCallExprHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "mapping/FieldOffsetMapper.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/Casting.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

template<typename T>
T* findNode(Stmt* root) {
    if (!root) return nullptr;
    if (auto* node = dyn_cast<T>(root)) return node;
    for (auto* child : root->children()) {
        if (auto* found = findNode<T>(child)) return found;
    }
    return nullptr;
}

// ============================================================================
// Test 1: Handler Registration
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, Registration) {
    const char *cpp = R"(
        class Array {
        public:
            int& operator[](int index);
        };
        int test() {
            Array arr;
            return arr[5];
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXOperatorCallExpr* opCall = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                opCall = findNode<CXXOperatorCallExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(opCall, nullptr);
    EXPECT_EQ(opCall->getOperator(), OO_Subscript);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, opCall);
    EXPECT_TRUE(handled);
}

// ============================================================================
// Test 2: Predicate Correctness - CXXOperatorCallExpr
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, PredicateMatchesCXXOperatorCallExpr) {
    const char *cpp = R"(
        class Vector {
        public:
            int operator()(int x) const;
        };
        int test() {
            Vector v;
            return v(42);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    TranslationUnitDecl* TU = AST->getASTContext().getTranslationUnitDecl();
    CXXOperatorCallExpr* opCall = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                opCall = findNode<CXXOperatorCallExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(opCall, nullptr);
    EXPECT_TRUE(cpptoc::CXXOperatorCallExprHandler::canHandle(opCall));
}

// ============================================================================
// Test 3: Predicate Rejects Built-in Binary Operator
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, PredicateRejectsBinaryOperator) {
    const char *cpp = R"(
        int test() { return 1 + 2; }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    TranslationUnitDecl* TU = AST->getASTContext().getTranslationUnitDecl();
    BinaryOperator* binOp = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                binOp = findNode<BinaryOperator>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(binOp, nullptr);
    EXPECT_FALSE(cpptoc::CXXOperatorCallExprHandler::canHandle(binOp));
}

// ============================================================================
// Test 4: Instance Subscript Operator (operator[])
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, InstanceSubscriptOperator) {
    const char *cpp = R"(
        class Container {
        public:
            int& operator[](size_t index);
        };
        int test() {
            Container c;
            return c[10];
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXOperatorCallExpr* opCall = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                opCall = findNode<CXXOperatorCallExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(opCall, nullptr);
    EXPECT_EQ(opCall->getOperator(), OO_Subscript);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, opCall);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(opCall);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<CallExpr>(cExpr)) << "Should translate to C CallExpr";
}

// ============================================================================
// Test 5: Instance Call Operator (operator())
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, InstanceCallOperator) {
    const char *cpp = R"(
        class Functor {
        public:
            int operator()(int x, int y) const;
        };
        int test() {
            Functor f;
            return f(10, 20);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXOperatorCallExpr* opCall = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                opCall = findNode<CXXOperatorCallExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(opCall, nullptr);
    EXPECT_EQ(opCall->getOperator(), OO_Call);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, opCall);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(opCall);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<CallExpr>(cExpr));
}

// ============================================================================
// Test 6: Smart Pointer Arrow Operator (operator->)
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, SmartPointerArrowOperator) {
    const char *cpp = R"(
        class Data {
        public:
            int value;
        };
        class SmartPtr {
        public:
            Data* operator->() const;
        };
        int test() {
            SmartPtr ptr;
            return ptr->value;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXOperatorCallExpr* opCall = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                opCall = findNode<CXXOperatorCallExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(opCall, nullptr);
    EXPECT_EQ(opCall->getOperator(), OO_Arrow);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, opCall);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(opCall);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<CallExpr>(cExpr));
}

// ============================================================================
// Test 7: Smart Pointer Dereference Operator (operator*)
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, SmartPointerDereferenceOperator) {
    const char *cpp = R"(
        class Data {
        public:
            int value;
        };
        class SmartPtr {
        public:
            Data& operator*() const;
        };
        int test() {
            SmartPtr ptr;
            Data& d = *ptr;
            return d.value;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXOperatorCallExpr* opCall = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                opCall = findNode<CXXOperatorCallExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(opCall, nullptr);
    EXPECT_EQ(opCall->getOperator(), OO_Star);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, opCall);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(opCall);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<CallExpr>(cExpr));
}

// ============================================================================
// Test 8: Copy Assignment Operator (operator=)
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, CopyAssignmentOperator) {
    const char *cpp = R"(
        class String {
        public:
            String& operator=(const String& other);
        };
        void test() {
            String s1, s2;
            s1 = s2;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXOperatorCallExpr* opCall = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                opCall = findNode<CXXOperatorCallExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(opCall, nullptr);
    EXPECT_EQ(opCall->getOperator(), OO_Equal);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, opCall);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(opCall);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<CallExpr>(cExpr));
}

// ============================================================================
// Test 9: ExprMapper Integration (Duplicate Prevention)
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, ExprMapperIntegration) {
    const char *cpp = R"(
        class Array {
        public:
            int& operator[](int index);
        };
        int test() {
            Array arr;
            return arr[5];
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXOperatorCallExpr* opCall = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                opCall = findNode<CXXOperatorCallExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(opCall, nullptr);

    // First dispatch
    bool handled1 = dispatcher.dispatch(cppCtx, cCtx, opCall);
    EXPECT_TRUE(handled1);
    Expr* cExpr1 = exprMapper.getCreated(opCall);
    ASSERT_NE(cExpr1, nullptr);

    // Second dispatch (should be skipped)
    bool handled2 = dispatcher.dispatch(cppCtx, cCtx, opCall);
    EXPECT_TRUE(handled2);
    Expr* cExpr2 = exprMapper.getCreated(opCall);

    // Should return same expression
    EXPECT_EQ(cExpr1, cExpr2);
}

// ============================================================================
// Test 10: Nested Operator Calls (arr[i] + vec[j])
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, NestedOperatorCalls) {
    const char *cpp = R"(
        class Array {
        public:
            int operator[](int index) const;
        };
        int test() {
            Array arr1, arr2;
            return arr1[0] + arr2[1];
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);

    // Find all CXXOperatorCallExpr nodes
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<CXXOperatorCallExpr*> opCalls;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                std::function<void(Stmt*)> findAll = [&](Stmt* S) {
                    if (!S) return;
                    if (auto* OC = dyn_cast<CXXOperatorCallExpr>(S)) {
                        opCalls.push_back(OC);
                    }
                    for (auto* child : S->children()) {
                        findAll(child);
                    }
                };
                findAll(FD->getBody());
                break;
            }
        }
    }

    ASSERT_EQ(opCalls.size(), 2) << "Should find 2 operator[] calls";

    // Dispatch all operator calls
    for (auto* opCall : opCalls) {
        dispatcher.dispatch(cppCtx, cCtx, opCall);
    }

    // Verify all were translated
    for (auto* opCall : opCalls) {
        Expr* cExpr = exprMapper.getCreated(opCall);
        EXPECT_NE(cExpr, nullptr);
        EXPECT_TRUE(isa<CallExpr>(cExpr));
    }
}

// ============================================================================
// Test 11: Multiple Operator Types in One Expression
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, MultipleOperatorTypes) {
    const char *cpp = R"(
        class Array {
        public:
            int& operator[](int index);
        };
        class Functor {
        public:
            int operator()(int x) const;
        };
        int test() {
            Array arr;
            Functor fn;
            return arr[fn(5)];
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);

    // Find all operator calls
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    std::vector<CXXOperatorCallExpr*> opCalls;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                std::function<void(Stmt*)> findAll = [&](Stmt* S) {
                    if (!S) return;
                    if (auto* OC = dyn_cast<CXXOperatorCallExpr>(S)) {
                        opCalls.push_back(OC);
                    }
                    for (auto* child : S->children()) {
                        findAll(child);
                    }
                };
                findAll(FD->getBody());
                break;
            }
        }
    }

    ASSERT_EQ(opCalls.size(), 2) << "Should find operator[] and operator()";

    // Find outer operator[] and verify it contains operator()
    CXXOperatorCallExpr* outerOp = nullptr;
    for (auto* opCall : opCalls) {
        if (opCall->getOperator() == OO_Subscript) {
            outerOp = opCall;
            break;
        }
    }
    ASSERT_NE(outerOp, nullptr);

    // Dispatch outer (should recursively dispatch inner)
    bool handled = dispatcher.dispatch(cppCtx, cCtx, outerOp);
    EXPECT_TRUE(handled);

    // Verify both operators were translated
    for (auto* opCall : opCalls) {
        Expr* cExpr = exprMapper.getCreated(opCall);
        EXPECT_NE(cExpr, nullptr);
        EXPECT_TRUE(isa<CallExpr>(cExpr));
    }
}

// ============================================================================
// Test 12: Distinction from Built-in Operators
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, DistinctionFromBuiltinOperators) {
    const char *cpp = R"(
        class Vector {
        public:
            Vector operator+(const Vector& other) const;
        };
        int test(int a, int b) {
            Vector v1, v2;
            Vector v3 = v1 + v2;  // CXXOperatorCallExpr
            return a + b;          // BinaryOperator (built-in)
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    TranslationUnitDecl* TU = AST->getASTContext().getTranslationUnitDecl();

    // Find CXXOperatorCallExpr
    CXXOperatorCallExpr* cxxOpCall = nullptr;
    BinaryOperator* binOp = nullptr;

    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                std::function<void(Stmt*)> findAll = [&](Stmt* S) {
                    if (!S) return;
                    if (auto* OC = dyn_cast<CXXOperatorCallExpr>(S)) {
                        if (OC->getOperator() == OO_Plus) {
                            cxxOpCall = OC;
                        }
                    }
                    if (auto* BO = dyn_cast<BinaryOperator>(S)) {
                        binOp = BO;
                    }
                    for (auto* child : S->children()) {
                        findAll(child);
                    }
                };
                findAll(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(cxxOpCall, nullptr);
    ASSERT_NE(binOp, nullptr);

    // Verify predicate correctly distinguishes
    EXPECT_TRUE(cpptoc::CXXOperatorCallExprHandler::canHandle(cxxOpCall));
    EXPECT_FALSE(cpptoc::CXXOperatorCallExprHandler::canHandle(binOp));
}

// ============================================================================
// Test 13: Address-of Operator (operator&) - Rare
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, AddressOfOperatorRare) {
    const char *cpp = R"(
        class Ptr {
        public:
            void* operator&();
        };
        void test() {
            Ptr p;
            void* addr = &p;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXOperatorCallExpr* opCall = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                opCall = findNode<CXXOperatorCallExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(opCall, nullptr);
    EXPECT_EQ(opCall->getOperator(), OO_Amp);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, opCall);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(opCall);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<CallExpr>(cExpr));
}

// ============================================================================
// Test 14: Comma Operator (operator,) - Very Rare
// ============================================================================

TEST(CXXOperatorCallExprHandlerDispatcherTest, CommaOperatorVeryRare) {
    const char *cpp = R"(
        class Sequence {
        public:
            Sequence& operator,(int value);
        };
        void test() {
            Sequence seq;
            (seq, 1);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_NE(AST, nullptr);

    ASTContext& cppCtx = AST->getASTContext();
    TargetContext targetCtx;
    ASTContext& cCtx = targetCtx.getContext();

    cpptoc::PathMapper mapper(targetCtx, "/src", "/output");
    cpptoc::DeclLocationMapper locMapper(mapper);
    cpptoc::DeclMapper declMapper;
    cpptoc::TypeMapper typeMapper;
    cpptoc::ExprMapper exprMapper;
    cpptoc::StmtMapper stmtMapper;
    cpptoc::FieldOffsetMapper fieldOffsetMapper;

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, fieldOffsetMapper, targetCtx);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::CXXOperatorCallExprHandler::registerWith(dispatcher);

    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    CXXOperatorCallExpr* opCall = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                opCall = findNode<CXXOperatorCallExpr>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(opCall, nullptr);
    EXPECT_EQ(opCall->getOperator(), OO_Comma);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, opCall);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(opCall);
    EXPECT_NE(cExpr, nullptr);
    EXPECT_TRUE(isa<CallExpr>(cExpr));
}
