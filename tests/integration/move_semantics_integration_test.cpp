/**
 * @file move_semantics_integration_test.cpp
 * @brief Comprehensive integration tests for move semantics (Story #135)
 *
 * Test Strategy (TDD):
 * - Test 1: Unique pointer-like ownership transfer
 * - Test 2: Vector-like move construction
 * - Test 3: Vector-like move assignment
 * - Test 4: Custom move-only type (FileHandle)
 * - Test 5: Custom move-only type (Socket)
 * - Test 6: Return value optimization with move semantics
 * - Test 7: Member-wise moves (class with multiple movable members)
 * - Test 8: Complex class hierarchy with move semantics
 * - Test 9: Move semantics with inheritance
 * - Test 10: Move-only types cannot be copied
 * - Test 11: Rvalue reference parameters
 * - Test 12: Perfect forwarding with move semantics
 * - Test 13: Move elision and RVO
 * - Test 14: Conditional move vs copy
 * - Test 15: Move semantics with exception safety
 *
 * Acceptance Criteria:
 * 1. Unique pointer-like types transpile successfully
 * 2. Vector-like move operations work
 * 3. Custom move-only classes work
 * 4. Return value moves work correctly
 * 5. Member-wise moves work (classes with multiple movable members)
 * 6. Performance validation (moves cheaper than copies)
 * 7. Zero regressions in existing tests
 * 8. Documentation: move semantics usage guide
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "../../include/CppToCVisitor.h"
#include "../../include/CNodeBuilder.h"
#include "../../include/MoveConstructorTranslator.h"
#include "../../include/MoveAssignmentTranslator.h"
#include "../../include/StdMoveTranslator.h"
#include <cassert>
#include <string>
#include <vector>
#include <sstream>

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

// Helper visitor to collect move semantics elements
class MoveIntegrationCollector : public RecursiveASTVisitor<MoveIntegrationCollector> {
public:
    std::vector<CXXConstructorDecl*> moveConstructors;
    std::vector<CXXMethodDecl*> moveAssignments;
    std::vector<CallExpr*> stdMoveCalls;
    int moveConstructorCount = 0;
    int moveAssignmentCount = 0;

    bool VisitCXXConstructorDecl(CXXConstructorDecl *D) {
        if (!D->isImplicit() && D->isMoveConstructor()) {
            moveConstructors.push_back(D);
            moveConstructorCount++;
        }
        return true;
    }

    bool VisitCXXMethodDecl(CXXMethodDecl *D) {
        if (!D->isImplicit() && D->isMoveAssignmentOperator()) {
            moveAssignments.push_back(D);
            moveAssignmentCount++;
        }
        return true;
    }

    bool VisitCallExpr(CallExpr *CE) {
        if (auto *Callee = CE->getDirectCallee()) {
            std::string name = Callee->getNameAsString();
            if (name == "move" || name.find("move") != std::string::npos) {
                stdMoveCalls.push_back(CE);
            }
        }
        return true;
    }
};

//=============================================================================
// Test 1: Unique pointer-like ownership transfer
//=============================================================================

// Test fixture
class move_semantics_integration_testTest : public ::testing::Test {
protected:
};

TEST_F(move_semantics_integration_testTest, Vector-like move construction) {
    const char *code = R"(
            namespace std {
                template<typename T>
                T&& move(T& t);
            }

            template<typename T>
            class DynamicArray {
                T* data;
                int size;
            public:
                DynamicArray() : data(nullptr), size(0) {}

                // Move constructor
                DynamicArray(DynamicArray&& other)
                    : data(other.data), size(other.size) {
                    other.data = nullptr;
                    other.size = 0;
                }
            };

            void use_array() {
                DynamicArray<int> arr1;
                DynamicArray<int> arr2 = std::move(arr1);
            }
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        MoveIntegrationCollector collector;
        collector.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(collector.moveConstructorCount >= 1) << "Expected move constructor for DynamicArray";
        ASSERT_TRUE(!collector.stdMoveCalls.empty()) << "Expected std::move(;call");
}

TEST_F(move_semantics_integration_testTest, Return value optimization with move semantics) {
    const char *code = R"(
            namespace std {
                template<typename T>
                T&& move(T& t);
            }

            template<typename T>
            class UniquePtr {
                T* ptr;
            public:
                UniquePtr(T* p) : ptr(p) {}
                UniquePtr(UniquePtr&& other) : ptr(other.ptr) {
                    other.ptr = nullptr;
                }
            };

            class Widget {
                int value;
            public:
                Widget(int v) : value(v) {}
            };

            UniquePtr<Widget> createWidget(int value) {
                UniquePtr<Widget> w(nullptr);
                return std::move(w);
            }

            void use_factory() {
                auto widget = createWidget(42);
            }
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        MoveIntegrationCollector collector;
        collector.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(collector.moveConstructorCount >= 1) << "Expected move constructor";
        ASSERT_TRUE(!collector.stdMoveCalls.empty()) << "Expected std::move(;in return");
}

TEST_F(move_semantics_integration_testTest, Move semantics with inheritance (base class move)) {
    ");

        const char *code = R"(
            namespace std {
                template<typename T>
                T&& move(T& t);
            }

            class Base {
                int baseValue;
            public:
                Base(int v) : baseValue(v) {}

                Base(Base&& other) : baseValue(other.baseValue) {
                    other.baseValue = 0;
                }
            };

            class Derived : public Base {
                int derivedValue;
            public:
                Derived(int b, int d) : Base(b), derivedValue(d) {}

                // Move constructor calls base move constructor
                Derived(Derived&& other)
                    : Base(std::move(other)), derivedValue(other.derivedValue) {
                    other.derivedValue = 0;
                }
            };

            void use_derived() {
                Derived d1(10, 20);
                Derived d2 = std::move(d1);
            }
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        MoveIntegrationCollector collector;
        collector.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(collector.moveConstructorCount >= 2) << "Expected move constructors for Base and Derived";
        ASSERT_TRUE(!collector.stdMoveCalls.empty()) << "Expected std::move(;for base class");");
}

TEST_F(move_semantics_integration_testTest, Move-only types cannot be copied) {
    const char *code = R"(
            namespace std {
                template<typename T>
                T&& move(T& t);
            }

            class MoveOnly {
            public:
                MoveOnly() = default;
                MoveOnly(MoveOnly&&) = default;
                MoveOnly& operator=(MoveOnly&&) = default;

                // Delete copy operations
                MoveOnly(const MoveOnly&) = delete;
                MoveOnly& operator=(const MoveOnly&) = delete;
            };

            void use_move_only() {
                MoveOnly m1;
                MoveOnly m2 = std::move(m1);
            }
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        MoveIntegrationCollector collector;
        collector.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Note: defaulted move constructor/assignment may not show up in visitor
        // but the code should compile and std::move() should be present
        ASSERT_TRUE(!collector.stdMoveCalls.empty()) << "Expected std::move(;call");
}

TEST_F(move_semantics_integration_testTest, Rvalue reference parameters) {
    const char *code = R"(
            namespace std {
                template<typename T>
                T&& move(T& t);
            }

            template<typename T>
            class UniquePtr {
                T* ptr;
            public:
                UniquePtr() : ptr(nullptr) {}
                UniquePtr(UniquePtr&& other) : ptr(other.ptr) {
                    other.ptr = nullptr;
                }
            };

            class Widget {
                UniquePtr<int> data;
            public:
                Widget(UniquePtr<int>&& ptr) : data(std::move(ptr)) {}

                void setData(UniquePtr<int>&& ptr) {
                    data = std::move(ptr);
                }
            };

            void use_widget() {
                UniquePtr<int> p;
                Widget w(std::move(p));
            }
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        MoveIntegrationCollector collector;
        collector.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(collector.stdMoveCalls.size() >= 2) << "Expected std::move(;calls for rvalue reference parameters");
}

TEST_F(move_semantics_integration_testTest, Perfect forwarding with move semantics) {
    const char *code = R"(
            namespace std {
                template<typename T>
                T&& move(T& t);

                template<typename T>
                T&& forward(T& t);
            }

            class Resource {
                int value;
            public:
                Resource(int v) : value(v) {}
                Resource(Resource&& other) : value(other.value) {
                    other.value = 0;
                }
            };

            template<typename T>
            void process(T&& arg) {
                Resource r = std::forward<T>(arg);
            }

            void use_forward() {
                Resource r1(42);
                process(std::move(r1));
            }
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        MoveIntegrationCollector collector;
        collector.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(collector.moveConstructorCount >= 1) << "Expected move constructor for Resource";
        ASSERT_TRUE(!collector.stdMoveCalls.empty()) << "Expected std::move(;or std::forward() calls");
}

TEST_F(move_semantics_integration_testTest, Move elision and RVO) {
    const char *code = R"(
            namespace std {
                template<typename T>
                T&& move(T& t);
            }

            class Heavy {
                int data[1000];
            public:
                Heavy() {}
                Heavy(Heavy&& other) {}
            };

            Heavy createHeavy() {
                Heavy h;
                return h;  // Should use RVO, not move
            }

            Heavy createHeavyExplicit() {
                Heavy h;
                return std::move(h);  // Explicit move
            }

            void use_heavy() {
                Heavy h1 = createHeavy();
                Heavy h2 = createHeavyExplicit();
            }
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        MoveIntegrationCollector collector;
        collector.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(collector.moveConstructorCount >= 1) << "Expected move constructor for Heavy";
}

TEST_F(move_semantics_integration_testTest, Conditional move vs copy) {
    const char *code = R"(
            namespace std {
                template<typename T>
                T&& move(T& t);
            }

            class Data {
                int value;
            public:
                Data(int v) : value(v) {}
                Data(const Data& other) : value(other.value) {}
                Data(Data&& other) : value(other.value) {
                    other.value = 0;
                }
            };

            void conditional_move(bool should_move) {
                Data d1(42);
                Data d2 = should_move ? std::move(d1) : d1;
            }
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        MoveIntegrationCollector collector;
        collector.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(collector.moveConstructorCount >= 1) << "Expected move constructor for Data";
}
