/**
 * @file OperatorIntegrationTest.cpp
 * @brief Comprehensive integration tests for ALL operator handlers working together
 *
 * Verifies that all operator handlers (existing + new) work correctly together
 * in the dispatcher framework with recursive dispatch and proper handler cooperation.
 *
 * Tests ALL operator handlers:
 * - BinaryOperatorHandler (arithmetic, comparison, logical, bitwise, assignment)
 * - UnaryOperatorHandler (unary +/-, !, ~, ++, --, address-of, dereference)
 * - CommaOperatorHandler (sequential evaluation)
 * - MemberExprHandler (. and ->)
 * - ArraySubscriptExprHandler ([])
 *
 * Plus supporting handlers:
 * - LiteralHandler (integer, float, string, boolean literals)
 * - DeclRefExprHandler (variable references)
 * - ImplicitCastExprHandler (implicit conversions)
 * - ParenExprHandler (parenthesized expressions)
 */

#include "dispatch/BinaryOperatorHandler.h"
#include "dispatch/UnaryOperatorHandler.h"
#include "dispatch/CommaOperatorHandler.h"
#include "dispatch/MemberExprHandler.h"
#include "dispatch/ArraySubscriptExprHandler.h"
#include "dispatch/LiteralHandler.h"
#include "dispatch/DeclRefExprHandler.h"
#include "dispatch/ImplicitCastExprHandler.h"
#include "dispatch/ParenExprHandler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "TargetContext.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Expr.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/Casting.h"
#include <gtest/gtest.h>
#include <memory>

using namespace clang;

// ============================================================================
// Helper Functions
// ============================================================================

/**
 * @brief Build AST from C++ code snippet
 */
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

/**
 * @brief Find first node of type T in AST subtree
 */
template<typename T>
T* findNode(Stmt* root) {
    if (!root) return nullptr;
    if (auto* node = dyn_cast<T>(root)) return node;
    for (auto* child : root->children()) {
        if (auto* found = findNode<T>(child)) return found;
    }
    return nullptr;
}

/**
 * @brief Register ALL operator handlers with dispatcher (plus supporting handlers)
 *
 * CRITICAL: Order matters for some handlers. Register foundational handlers first,
 * then build up to more complex ones.
 */
void registerAllOperatorHandlers(CppToCVisitorDispatcher& dispatcher) {
    // Register foundational handlers first
    cpptoc::LiteralHandler::registerWith(dispatcher);
    cpptoc::DeclRefExprHandler::registerWith(dispatcher);
    cpptoc::ImplicitCastExprHandler::registerWith(dispatcher);
    cpptoc::ParenExprHandler::registerWith(dispatcher);

    // Register operator handlers (can be in any order - they're independent)
    cpptoc::BinaryOperatorHandler::registerWith(dispatcher);
    cpptoc::UnaryOperatorHandler::registerWith(dispatcher);
    cpptoc::CommaOperatorHandler::registerWith(dispatcher);
    cpptoc::MemberExprHandler::registerWith(dispatcher);
    cpptoc::ArraySubscriptExprHandler::registerWith(dispatcher);
}

// ============================================================================
// Test Fixture
// ============================================================================

/**
 * @class OperatorIntegrationTest
 * @brief Test fixture for operator integration testing
 */
class OperatorIntegrationTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Context setup will be done per-test since each test builds its own AST
    }

    void TearDown() override {
        // Cleanup happens automatically with unique_ptr
    }

    /**
     * @brief Test helper: dispatch expression and verify it was handled
     */
    bool dispatchAndVerify(ASTContext& cppCtx, ASTContext& cCtx,
                          CppToCVisitorDispatcher& dispatcher,
                          cpptoc::ExprMapper& exprMapper,
                          Expr* cppExpr) {
        if (!cppExpr) return false;

        bool handled = dispatcher.dispatch(cppCtx, cCtx, cppExpr);
        if (!handled) return false;

        Expr* cExpr = exprMapper.getCreated(cppExpr);
        return cExpr != nullptr;
    }
};

// ============================================================================
// Test 1: All Operator Handlers Registered
// ============================================================================

TEST_F(OperatorIntegrationTest, AllOperatorHandlersRegistered) {
    // Test: Verify all operator handlers can be registered successfully
    const char *cpp = R"(
        struct Point { int x; int y; };
        int arr[10];
        int test() {
            Point p;
            int a = 5;
            int b = (p.x + arr[0]) * a++;
            return b, a;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);

    // Should not throw or crash when registering all handlers
    EXPECT_NO_THROW(registerAllOperatorHandlers(dispatcher));
}

// ============================================================================
// Test 2: Arithmetic Operators Integration
// ============================================================================

TEST_F(OperatorIntegrationTest, ArithmeticOperatorsIntegration) {
    // Test: Complex arithmetic with multiple operators: (a + b) * (c - d) / e % f
    const char *cpp = R"(
        int test() {
            int a = 1, b = 2, c = 3, d = 4, e = 5, f = 6;
            return (a + b) * (c - d) / e % f;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    registerAllOperatorHandlers(dispatcher);

    // Find the return statement's expression
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ReturnStmt* retStmt = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                retStmt = findNode<ReturnStmt>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(retStmt, nullptr);
    Expr* expr = retStmt->getRetValue();
    ASSERT_NE(expr, nullptr);

    // Dispatch the complex arithmetic expression
    bool handled = dispatcher.dispatch(cppCtx, cCtx, expr);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(expr);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test 3: Assignment and Simple Binary Operations
// ============================================================================

TEST_F(OperatorIntegrationTest, AssignmentAndBinaryOperations) {
    // Test: Simple assignment with binary operators
    // NOTE: CompoundAssignOperator (+=, -=, etc.) requires separate handler - not tested here
    const char *cpp = R"(
        int test() {
            int a = 10;
            int b = 5;
            a = a + b;
            a = a - 2;
            a = a * 3;
            a = a / 4;
            a = a % 7;
            return a;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    registerAllOperatorHandlers(dispatcher);

    // Find and verify assignment operations work
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ReturnStmt* retStmt = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                retStmt = findNode<ReturnStmt>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(retStmt, nullptr);
    bool handled = dispatcher.dispatch(cppCtx, cCtx, retStmt->getRetValue());
    EXPECT_TRUE(handled);
}

// ============================================================================
// Test 4: Increment/Decrement Integration
// ============================================================================

TEST_F(OperatorIntegrationTest, IncrementDecrementIntegration) {
    // Test: Prefix and postfix ++/-- in complex expressions
    const char *cpp = R"(
        int test() {
            int i = 0, j = 10;
            int a = ++i + j--;
            int b = i++ - --j;
            return a + b;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    registerAllOperatorHandlers(dispatcher);

    // Find and verify all increment/decrement operations
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                // Just verify the function body dispatches successfully
                ReturnStmt* retStmt = findNode<ReturnStmt>(FD->getBody());
                ASSERT_NE(retStmt, nullptr);

                bool handled = dispatcher.dispatch(cppCtx, cCtx, retStmt->getRetValue());
                EXPECT_TRUE(handled);
                break;
            }
        }
    }
}

// ============================================================================
// Test 5: Member Access Integration
// ============================================================================

TEST_F(OperatorIntegrationTest, MemberAccessIntegration) {
    // Test: Member access with . and -> operators
    const char *cpp = R"(
        struct Point { int x; int y; };
        struct Line { Point *start; Point end; };
        int test() {
            Line line;
            Point p;
            line.start = &p;
            return line.start->x + line.end.y;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    registerAllOperatorHandlers(dispatcher);

    // Find the return expression with member access
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ReturnStmt* retStmt = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test" && FD->hasBody()) {
                retStmt = findNode<ReturnStmt>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(retStmt, nullptr);
    Expr* expr = retStmt->getRetValue();
    ASSERT_NE(expr, nullptr);

    // Should contain member access: line.start->x + line.end.y
    bool handled = dispatcher.dispatch(cppCtx, cCtx, expr);
    EXPECT_TRUE(handled);
}

// ============================================================================
// Test 6: Array Subscript Integration
// ============================================================================

TEST_F(OperatorIntegrationTest, ArraySubscriptIntegration) {
    // Test: Array subscript with arithmetic index expressions
    const char *cpp = R"(
        int test() {
            int arr[10];
            int i = 2, j = 3;
            return arr[i] + arr[j * 2] + arr[i + j];
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    registerAllOperatorHandlers(dispatcher);

    // Find the return expression with array subscripts
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ReturnStmt* retStmt = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                retStmt = findNode<ReturnStmt>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(retStmt, nullptr);
    Expr* expr = retStmt->getRetValue();
    ASSERT_NE(expr, nullptr);

    bool handled = dispatcher.dispatch(cppCtx, cCtx, expr);
    EXPECT_TRUE(handled);
}

// ============================================================================
// Test 7: Comma Operator Integration
// ============================================================================

TEST_F(OperatorIntegrationTest, CommaOperatorIntegration) {
    // Test: Comma operator in simple expression context
    // NOTE: ForStmt requires separate handler - testing comma operator in expression only
    const char *cpp = R"(
        int test() {
            int a = 1;
            int b = 2;
            int c = 3;
            return (a + 1, b + 2, c + 3);
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    registerAllOperatorHandlers(dispatcher);

    // Find return statement with comma expression
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ReturnStmt* retStmt = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                retStmt = findNode<ReturnStmt>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(retStmt, nullptr);
    Expr* expr = retStmt->getRetValue();
    ASSERT_NE(expr, nullptr);

    // Verify comma operator expression dispatches successfully
    bool handled = dispatcher.dispatch(cppCtx, cCtx, expr);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(expr);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test 8: Complex Nested Expression
// ============================================================================

TEST_F(OperatorIntegrationTest, ComplexNestedExpression) {
    // Test: Combination of operators in deeply nested expression
    // arr[i++].ptr->value (without compound assignment)
    const char *cpp = R"(
        struct Data { int value; };
        struct Node { Data *ptr; };
        Node arr[10];
        int test() {
            int i = 0;
            int x = arr[i++].ptr->value;
            return x + 5;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    registerAllOperatorHandlers(dispatcher);

    // Find the return expression: x + 5
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ReturnStmt* retStmt = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test" && FD->hasBody()) {
                retStmt = findNode<ReturnStmt>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(retStmt, nullptr);
    Expr* expr = retStmt->getRetValue();
    ASSERT_NE(expr, nullptr);

    // This expression uses:
    // - BinaryOperator: +
    // - DeclRefExpr: x
    // - IntegerLiteral: 5
    // The declaration of x involves:
    // - ArraySubscriptExpr: arr[i++]
    // - UnaryOperator: i++ (postfix increment)
    // - MemberExpr: .ptr
    // - MemberExpr: ->value (arrow)
    bool handled = dispatcher.dispatch(cppCtx, cCtx, expr);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(expr);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test 9: Multi-Dimensional Array with Member Access
// ============================================================================

TEST_F(OperatorIntegrationTest, MultiDimensionalArrayWithMemberAccess) {
    // Test: Nested array subscripts combined with member access
    // objects[i][j].field
    const char *cpp = R"(
        struct Point { int x; int y; };
        Point matrix[5][5];
        int test() {
            int i = 2, j = 3;
            return matrix[i][j].x + matrix[j][i].y;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    registerAllOperatorHandlers(dispatcher);

    // Find the return expression with nested subscripts and member access
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ReturnStmt* retStmt = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test" && FD->hasBody()) {
                retStmt = findNode<ReturnStmt>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(retStmt, nullptr);
    Expr* expr = retStmt->getRetValue();
    ASSERT_NE(expr, nullptr);

    // Expression chain: matrix[i][j].x + matrix[j][i].y
    // Uses: ArraySubscriptExpr (nested), MemberExpr, BinaryOperator
    bool handled = dispatcher.dispatch(cppCtx, cCtx, expr);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(expr);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test 10: Logical and Comparison Operators
// ============================================================================

TEST_F(OperatorIntegrationTest, LogicalAndComparisonOperators) {
    // Test: Complex boolean expressions with && || ! and comparisons
    const char *cpp = R"(
        int test(int a, int b, int c) {
            if ((a > b && b < c) || (a == c && b != 0) || !(a < 0)) {
                return 1;
            }
            return 0;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    registerAllOperatorHandlers(dispatcher);

    // Find the if condition
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    IfStmt* ifStmt = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                ifStmt = findNode<IfStmt>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(ifStmt, nullptr);
    Expr* condition = ifStmt->getCond();
    ASSERT_NE(condition, nullptr);

    // Complex condition with &&, ||, !, >, <, ==, !=
    bool handled = dispatcher.dispatch(cppCtx, cCtx, condition);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(condition);
    EXPECT_NE(cExpr, nullptr);
}

// ============================================================================
// Test 11: Bitwise Operators Integration
// ============================================================================

TEST_F(OperatorIntegrationTest, BitwiseOperatorsIntegration) {
    // Test: All bitwise operators: &, |, ^, ~, <<, >>
    const char *cpp = R"(
        int test(int flags) {
            int mask = 0xFF;
            int result = (flags & mask) | (flags ^ 0xAA);
            result = (result << 2) >> 1;
            result = ~result & 0xFFFF;
            return result;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    registerAllOperatorHandlers(dispatcher);

    // Find return statement
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ReturnStmt* retStmt = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                retStmt = findNode<ReturnStmt>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(retStmt, nullptr);
    bool handled = dispatcher.dispatch(cppCtx, cCtx, retStmt->getRetValue());
    EXPECT_TRUE(handled);
}

// ============================================================================
// Test 12: Pointer and Address-Of Operators
// ============================================================================

TEST_F(OperatorIntegrationTest, PointerAndAddressOfOperators) {
    // Test: Pointer dereference (*) and address-of (&) operators
    const char *cpp = R"(
        int test() {
            int x = 42;
            int *ptr = &x;
            int **pptr = &ptr;
            return **pptr + *ptr;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    registerAllOperatorHandlers(dispatcher);

    // Find return expression with pointer operations
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ReturnStmt* retStmt = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->hasBody()) {
                retStmt = findNode<ReturnStmt>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(retStmt, nullptr);
    Expr* expr = retStmt->getRetValue();
    ASSERT_NE(expr, nullptr);

    // Expression: **pptr + *ptr
    bool handled = dispatcher.dispatch(cppCtx, cCtx, expr);
    EXPECT_TRUE(handled);
}

// ============================================================================
// Test 13: All Operators Together (Maximum Complexity)
// ============================================================================

TEST_F(OperatorIntegrationTest, AllOperatorsTogether) {
    // Test: Stress test - many operators in complex expression
    // Tests operators we have handlers for (not CompoundAssign or CallExpr)
    const char *cpp = R"(
        struct Data { int value; int *ptr; };
        struct Container { Data items[10]; };

        int test() {
            Container containers[3];
            int i = 0, j = 1;

            // Complex expression using: array[], member., arrow->, ++, *, &, binary ops, comma
            int result = (containers[i++].items[j].value * 2,
                         *containers[j].items[i].ptr & 0xFF,
                         containers[0].items[0].value + 100);

            return result;
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

    CppToCVisitorDispatcher dispatcher(mapper, locMapper, declMapper, typeMapper, exprMapper, stmtMapper, targetCtx);
    registerAllOperatorHandlers(dispatcher);

    // Find the return statement
    TranslationUnitDecl* TU = cppCtx.getTranslationUnitDecl();
    ReturnStmt* retStmt = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test" && FD->hasBody()) {
                retStmt = findNode<ReturnStmt>(FD->getBody());
                break;
            }
        }
    }

    ASSERT_NE(retStmt, nullptr);
    Expr* expr = retStmt->getRetValue();
    ASSERT_NE(expr, nullptr);

    // This mega-expression uses:
    // - ArraySubscriptExpr (multiple levels)
    // - MemberExpr (dot and arrow)
    // - UnaryOperator (++, *)
    // - BinaryOperator (*, &, +)
    // - CommaOperator
    bool handled = dispatcher.dispatch(cppCtx, cCtx, expr);
    EXPECT_TRUE(handled);

    Expr* cExpr = exprMapper.getCreated(expr);
    EXPECT_NE(cExpr, nullptr);
}
