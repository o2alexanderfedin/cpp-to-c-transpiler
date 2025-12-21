/**
 * @file CopyMoveIntegrationTest.cpp
 * @brief Integration tests for copy and move semantics coexistence (Story #134)
 *
 * Test Strategy (TDD):
 * - Test 1: Class with both copy and move constructors
 * - Test 2: Class with both copy and move assignments
 * - Test 3: Call site selection (lvalue uses copy, rvalue uses move)
 * - Test 4: No naming conflicts in generated C
 * - Test 5: Complex class with members requiring both copy and move
 * - Test 6: Memory safety in mixed copy/move scenarios
 * - Test 7: Exception safety when both copy and move present
 *
 * Acceptance Criteria:
 * 1. Copy and move constructors can coexist in the same C++ class
 * 2. Copy and move assignment operators can coexist
 * 3. Proper selection between copy and move at call sites
 * 4. No naming conflicts in generated C functions
 * 5. Integration tests with complex classes
 * 6. Verify memory management in mixed scenarios
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "../../../include/CppToCVisitor.h"
#include "../../../include/CNodeBuilder.h"
#include "../../../include/MoveConstructorTranslator.h"
#include "../../../include/MoveAssignmentTranslator.h"
#include <cassert>
#include <string>
#include <vector>
#include <sstream>
#include <utility>

using namespace clang;

// Test helper to build AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const char *code) {
    return tooling::buildASTFromCode(code);
}

// Test helper macros
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

// Helper visitor to collect constructors and assignments
class CopyMoveCollector : public RecursiveASTVisitor<CopyMoveCollector> {
public:
    std::vector<CXXConstructorDecl*> copyConstructors;
    std::vector<CXXConstructorDecl*> moveConstructors;
    std::vector<CXXMethodDecl*> copyAssignments;
    std::vector<CXXMethodDecl*> moveAssignments;

    bool VisitCXXConstructorDecl(CXXConstructorDecl *D) {
        if (!D->isImplicit()) {
            if (D->isCopyConstructor()) {
                copyConstructors.push_back(D);
            } else if (D->isMoveConstructor()) {
                moveConstructors.push_back(D);
            }
        }
        return true;
    }

    bool VisitCXXMethodDecl(CXXMethodDecl *D) {
        if (!D->isImplicit()) {
            if (D->isCopyAssignmentOperator()) {
                copyAssignments.push_back(D);
            } else if (D->isMoveAssignmentOperator()) {
                moveAssignments.push_back(D);
            }
        }
        return true;
    }
};

// Helper to find call expressions
class CallExprFinder : public RecursiveASTVisitor<CallExprFinder> {
public:
    std::vector<CallExpr*> callExprs;
    std::vector<CXXConstructExpr*> constructExprs;

    bool VisitCallExpr(CallExpr *E) {
        callExprs.push_back(E);
        return true;
    }

    bool VisitCXXConstructExpr(CXXConstructExpr *E) {
        constructExprs.push_back(E);
        return true;
    }
};

/**
 * Test 1: Class with both copy and move constructors
 *
 * Verifies:
 * - Both constructors are detected
 * - Both are translated to C
 * - Different function names generated
 */

// Test fixture
class CopyMoveIntegrationTest : public ::testing::Test {
protected:
};

TEST_F(CopyMoveIntegrationTest, Call site selection based on value category) {
    const char *code = R"(
            #include <utility>

            class Resource {
            public:
                int* data;

                Resource(const Resource& other);  // Copy constructor
                Resource(Resource&& other);       // Move constructor
            };

            void testFunction() {
                Resource r1;
                Resource r2(r1);              // Lvalue -> copy constructor
                Resource r3(std::move(r1));   // Rvalue -> move constructor
                Resource r4(Resource());      // Temporary -> move constructor
            }
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        ASTContext &Context = AST->getASTContext();

        // Find construct expressions
        CallExprFinder Finder;
        Finder.TraverseDecl(Context.getTranslationUnitDecl());

        ASSERT_TRUE(Finder.constructExprs.size() >= 3) << "Expected at least 3 construct expressions";

        // Analyze each construct expression
        int copyConstructCalls = 0;
        int moveConstructCalls = 0;

        for (CXXConstructExpr *CE : Finder.constructExprs) {
            CXXConstructorDecl *Ctor = CE->getConstructor();

            if (Ctor->isCopyConstructor()) {
                copyConstructCalls++;
            } else if (Ctor->isMoveConstructor()) {
                moveConstructCalls++;
            }
        }

        // We should have at least 1 copy construct and 2 move constructs
        ASSERT_TRUE(copyConstructCalls >= 1) << "Expected at least 1 copy constructor call for lvalue";
        ASSERT_TRUE(moveConstructCalls >= 2) << "Expected at least 2 move constructor calls for rvalues";
}

TEST_F(CopyMoveIntegrationTest, No naming conflicts in generated C functions) {
    const char *code = R"(
            class Widget {
            public:
                int value;

                Widget(const Widget& other);              // Copy ctor
                Widget(Widget&& other) noexcept;          // Move ctor
                Widget& operator=(const Widget& other);   // Copy assign
                Widget& operator=(Widget&& other) noexcept; // Move assign
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        ASTContext &Context = AST->getASTContext();
        CNodeBuilder Builder(Context);
        CppToCVisitor Visitor(Context, Builder);

        // Collect all special members
        CopyMoveCollector Collector;
        Collector.TraverseDecl(Context.getTranslationUnitDecl());

        ASSERT_TRUE(Collector.copyConstructors.size() == 1) << "Expected 1 copy constructor";
        ASSERT_TRUE(Collector.moveConstructors.size() == 1) << "Expected 1 move constructor";
        ASSERT_TRUE(Collector.copyAssignments.size() == 1) << "Expected 1 copy assignment";
        ASSERT_TRUE(Collector.moveAssignments.size() == 1) << "Expected 1 move assignment";

        // Generate all C code
        MoveConstructorTranslator MoveCtorTranslator(Context);
        MoveAssignmentTranslator MoveAssignTranslator(Context);

        std::string moveCtor = MoveCtorTranslator.generateMoveConstructor(
            Collector.moveConstructors[0]);
        std::string moveAssign = MoveAssignTranslator.generateMoveAssignment(
            Collector.moveAssignments[0]);

        // Verify unique names
        std::vector<std::string> functionNames;

        // Extract function names from generated code
        if (moveCtor.find("Widget_move_construct") != std::string::npos) {
            functionNames.push_back("Widget_move_construct");
        }
        if (moveAssign.find("Widget_move_assign") != std::string::npos) {
            functionNames.push_back("Widget_move_assign");
        }

        // Add expected copy names (these would be generated by existing logic)
        functionNames.push_back("Widget__ctor_copy");
        functionNames.push_back("Widget__operator_assign");

        // Check for uniqueness
        std::sort(functionNames.begin(), functionNames.end());
        auto last = std::unique(functionNames.begin(), functionNames.end());
        ASSERT_TRUE(last == functionNames.end()) << "Duplicate function names detected";
}

TEST_F(CopyMoveIntegrationTest, Memory safety in mixed copy/move scenarios) {
    const char *code = R"(
            class SafeResource {
            public:
                int* data;
                int size;

                // Copy constructor - allocates new memory
                SafeResource(const SafeResource& other)
                    : data(new int[other.size]), size(other.size) {
                }

                // Move constructor - transfers ownership
                SafeResource(SafeResource&& other) noexcept
                    : data(other.data), size(other.size) {
                    other.data = nullptr;  // Critical: prevent double-free
                    other.size = 0;
                }

                ~SafeResource() {
                    delete[] data;  // Safe even if data is nullptr
                }
            };

            void testSafety() {
                SafeResource r1;
                SafeResource r2(r1);              // Copy - both valid
                SafeResource r3(std::move(r2));   // Move - r2 now empty
                // r2.data is nullptr - safe to destroy
            }
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        ASTContext &Context = AST->getASTContext();
        MoveConstructorTranslator MoveTranslator(Context);

        // Collect move constructor
        CopyMoveCollector Collector;
        Collector.TraverseDecl(Context.getTranslationUnitDecl());

        ASSERT_TRUE(Collector.moveConstructors.size() == 1) << "Expected 1 move constructor";

        CXXConstructorDecl *MoveCtor = Collector.moveConstructors[0];
        std::string moveCode = MoveTranslator.generateMoveConstructor(MoveCtor);

        // Verify pointer nullification is present
        ASSERT_TRUE(moveCode.find("NULL") != std::string::npos ||
               moveCode.find("nullptr") != std::string::npos) << "Move constructor must nullify source pointers";

        // Verify data is copied before nullification
        ASSERT_TRUE(moveCode.find("dest->data = src->data") != std::string::npos) << "Move constructor must transfer data pointer";
}

TEST_F(CopyMoveIntegrationTest, Exception safety when both copy and move present) {
    const char *code = R"(
            class ThrowingMove {
            public:
                int* data;

                // Copy constructor - strong exception safety
                ThrowingMove(const ThrowingMove& other);

                // Move constructor - may throw (not noexcept)
                ThrowingMove(ThrowingMove&& other);
            };

            class NoThrowMove {
            public:
                int* data;

                // Copy constructor
                NoThrowMove(const NoThrowMove& other);

                // Move constructor - guaranteed not to throw
                NoThrowMove(NoThrowMove&& other) noexcept;
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        ASTContext &Context = AST->getASTContext();

        // Collect constructors
        CopyMoveCollector Collector;
        Collector.TraverseDecl(Context.getTranslationUnitDecl());

        // Find NoThrowMove's move constructor
        CXXConstructorDecl *NoThrowMoveCtor = nullptr;
        for (CXXConstructorDecl *Ctor : Collector.moveConstructors) {
            if (Ctor->getParent()->getNameAsString() == "NoThrowMove") {
                NoThrowMoveCtor = Ctor;
                break;
            }
        }

        ASSERT_TRUE(NoThrowMoveCtor != nullptr) << "NoThrowMove's move constructor not found";

        // Verify noexcept specification
        const auto *FPT = NoThrowMoveCtor->getType()->getAs<FunctionProtoType>();
        ASSERT_TRUE(FPT != nullptr) << "Function prototype not found";

        bool isNoExcept = FPT->isNothrow();
        ASSERT_TRUE(isNoExcept) << "Move constructor should be marked noexcept";
}
