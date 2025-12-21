/**
 * @file MoveSemanticIntegrationTestFixture.h
 * @brief Shared test fixture and helper classes for move semantics integration tests
 *
 * This fixture provides common functionality for testing move semantics integration:
 * - AST building and traversal
 * - Move semantics element collection (constructors, assignments, std::move calls)
 * - Helper methods for finding and verifying move semantics constructs
 */

#ifndef MOVE_SEMANTIC_INTEGRATION_TEST_FIXTURE_H
#define MOVE_SEMANTIC_INTEGRATION_TEST_FIXTURE_H

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include <memory>
#include <vector>
#include <string>

using namespace clang;

/**
 * @brief Helper visitor to collect move semantics elements during AST traversal
 *
 * Collects:
 * - Move constructors
 * - Move assignment operators
 * - std::move() calls
 */
class MoveIntegrationCollector : public RecursiveASTVisitor<MoveIntegrationCollector> {
public:
    std::vector<CXXConstructorDecl*> moveConstructors;
    std::vector<CXXMethodDecl*> moveAssignments;
    std::vector<CallExpr*> stdMoveCalls;
    int moveConstructorCount = 0;
    int moveAssignmentCount = 0;

    /**
     * @brief Visit constructor declarations to find move constructors
     */
    bool VisitCXXConstructorDecl(CXXConstructorDecl *D) {
        if (!D->isImplicit() && D->isMoveConstructor()) {
            moveConstructors.push_back(D);
            moveConstructorCount++;
        }
        return true;
    }

    /**
     * @brief Visit method declarations to find move assignment operators
     */
    bool VisitCXXMethodDecl(CXXMethodDecl *D) {
        if (!D->isImplicit() && D->isMoveAssignmentOperator()) {
            moveAssignments.push_back(D);
            moveAssignmentCount++;
        }
        return true;
    }

    /**
     * @brief Visit call expressions to find std::move() calls
     */
    bool VisitCallExpr(CallExpr *CE) {
        if (auto *Callee = CE->getDirectCallee()) {
            std::string name = Callee->getNameAsString();
            if (name == "move" || name.find("move") != std::string::npos) {
                stdMoveCalls.push_back(CE);
            }
        }
        return true;
    }

    /**
     * @brief Reset all collected data
     */
    void reset() {
        moveConstructors.clear();
        moveAssignments.clear();
        stdMoveCalls.clear();
        moveConstructorCount = 0;
        moveAssignmentCount = 0;
    }
};

/**
 * @brief Base test fixture for move semantics integration tests
 *
 * Provides:
 * - AST building helper
 * - Common collector instance
 * - Setup/teardown for each test
 */
class MoveSemanticIntegrationTestFixture : public ::testing::Test {
protected:
    MoveIntegrationCollector collector;

    void SetUp() override {
        // Reset collector before each test
        collector.reset();
    }

    void TearDown() override {
        // Cleanup after each test
        collector.reset();
    }

    /**
     * @brief Build AST from C++ code string
     * @param code The C++ source code to parse
     * @return Unique pointer to ASTUnit
     */
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }

    /**
     * @brief Traverse AST and collect move semantics elements
     * @param AST The AST unit to traverse
     */
    void traverseAndCollect(const std::unique_ptr<ASTUnit>& AST) {
        collector.reset();
        collector.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    }

    /**
     * @brief Helper to verify move constructor count
     */
    void expectMoveConstructors(int minCount, const std::string& message = "") {
        EXPECT_GE(collector.moveConstructorCount, minCount)
            << (message.empty() ? "Expected at least " + std::to_string(minCount) + " move constructor(s)" : message);
    }

    /**
     * @brief Helper to verify move assignment count
     */
    void expectMoveAssignments(int minCount, const std::string& message = "") {
        EXPECT_GE(collector.moveAssignmentCount, minCount)
            << (message.empty() ? "Expected at least " + std::to_string(minCount) + " move assignment(s)" : message);
    }

    /**
     * @brief Helper to verify std::move() calls
     */
    void expectStdMoveCalls(size_t minCount, const std::string& message = "") {
        EXPECT_GE(collector.stdMoveCalls.size(), minCount)
            << (message.empty() ? "Expected at least " + std::to_string(minCount) + " std::move() call(s)" : message);
    }

    /**
     * @brief Helper to verify AST was built successfully
     */
    void expectValidAST(const std::unique_ptr<ASTUnit>& AST, const std::string& message = "Failed to build AST") {
        ASSERT_TRUE(AST != nullptr) << message;
    }
};

#endif // MOVE_SEMANTIC_INTEGRATION_TEST_FIXTURE_H
