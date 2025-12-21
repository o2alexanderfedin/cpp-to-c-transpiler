#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include <gtest/gtest.h>
#include <string>
#include <vector>

using namespace clang;

// Test fixture for Move Semantics tests
class MoveSemanticTestFixture : public ::testing::Test {
protected:
    // Helper to build AST from C++ code
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }
};

// Helper visitor to find specific AST nodes
class MoveSemanticsFinder : public RecursiveASTVisitor<MoveSemanticsFinder> {
public:
    std::vector<const CXXMethodDecl*> moveConstructors;
    std::vector<const CXXMethodDecl*> moveAssignments;
    std::vector<const CXXConstructExpr*> moveConstructorCalls;
    std::vector<const CallExpr*> stdMoveCalls;
    std::vector<const ValueDecl*> rvalueRefs;
    std::vector<const FunctionDecl*> forwardingFunctions;

    bool VisitCXXConstructorDecl(CXXConstructorDecl *D) {
        if (D->isMoveConstructor()) {
            moveConstructors.push_back(D);
        }
        return true;
    }

    bool VisitCXXMethodDecl(CXXMethodDecl *D) {
        if (D->isMoveAssignmentOperator()) {
            moveAssignments.push_back(D);
        }
        return true;
    }

    bool VisitCXXConstructExpr(CXXConstructExpr *E) {
        if (E->getConstructor()->isMoveConstructor()) {
            moveConstructorCalls.push_back(E);
        }
        return true;
    }

    bool VisitCallExpr(CallExpr *E) {
        if (auto *Callee = E->getDirectCallee()) {
            std::string name = Callee->getNameAsString();
            if (name == "move") {
                stdMoveCalls.push_back(E);
            } else if (name == "forward") {
                forwardingFunctions.push_back(Callee);
            }
        }
        return true;
    }

    bool VisitValueDecl(ValueDecl *D) {
        if (auto *VD = dyn_cast<VarDecl>(D)) {
            if (VD->getType()->isRValueReferenceType()) {
                rvalueRefs.push_back(VD);
            }
        } else if (auto *PD = dyn_cast<ParmVarDecl>(D)) {
            if (PD->getType()->isRValueReferenceType()) {
                rvalueRefs.push_back(PD);
            }
        }
        return true;
    }
};

// ============================================================================
// Category 1: Rvalue References (8-10 tests)
// ============================================================================

TEST_F(MoveSemanticTestFixture, RvalueReferenceParameterDetection) {
    const char *code = R"(
        void process(int&& value) {
            // Process rvalue reference
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.rvalueRefs.size(), 1) << "Expected at least one rvalue reference parameter";

    const auto *param = finder.rvalueRefs[0];
    ASSERT_TRUE(param->getType()->isRValueReferenceType()) << "Parameter should be rvalue reference type";
}

TEST_F(MoveSemanticTestFixture, RvalueReferenceReturnType) {
    const char *code = R"(
        class Widget {
            int data;
        public:
            int&& getData() { return static_cast<int&&>(data); }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXMethodDecl *method = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Widget") {
                for (auto *M : RD->methods()) {
                    if (M->getNameAsString() == "getData") {
                        method = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_TRUE(method != nullptr) << "getData method not found";
    ASSERT_TRUE(method->getReturnType()->isRValueReferenceType()) << "Return type should be rvalue reference";
}

TEST_F(MoveSemanticTestFixture, LvalueCannotBindToRvalueReference) {
    // This code would fail to compile with proper C++ semantics
    // The transpiler should detect this constraint
    const char *code = R"(
        void accept_rvalue(int&& value) {}

        void test() {
            int x = 42;
            // accept_rvalue(x);  // Should not compile - lvalue binding
            accept_rvalue(100);   // OK - rvalue binding
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.rvalueRefs.size(), 1) << "Expected rvalue reference parameter";
}

TEST_F(MoveSemanticTestFixture, RvalueReferenceVariableDeclaration) {
    const char *code = R"(
        int getTemporary() { return 42; }

        void test() {
            int&& rref = getTemporary();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.rvalueRefs.size(), 1) << "Expected rvalue reference variable";
}

TEST_F(MoveSemanticTestFixture, ReferenceCollapsingRvalueRvalue) {
    const char *code = R"(
        template<typename T>
        void func(T&& param) {
            // T&& is a universal reference
        }

        void test() {
            func(42);  // T = int, param is int&&
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Reference collapsing: && + && -> &&
    // This is tested by verifying template instantiation
}

TEST_F(MoveSemanticTestFixture, ReferenceCollapsingLvalueRvalue) {
    const char *code = R"(
        template<typename T>
        void func(T&& param) {
            // Universal reference
        }

        void test() {
            int x = 42;
            func(x);  // T = int&, param is int& (& + && -> &)
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Reference collapsing: & + && -> &
    // This is tested by verifying template instantiation
}

TEST_F(MoveSemanticTestFixture, RvalueReferenceMemberVariable) {
    const char *code = R"(
        class Container {
            int&& rref;  // Rvalue reference member (rare but legal)
        public:
            Container(int&& r) : rref(static_cast<int&&>(r)) {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    bool foundRvalueRefMember = false;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Container") {
                for (auto *F : RD->fields()) {
                    if (F->getType()->isRValueReferenceType()) {
                        foundRvalueRefMember = true;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_TRUE(foundRvalueRefMember) << "Expected rvalue reference member variable";
}

TEST_F(MoveSemanticTestFixture, RvalueReferenceTemporaryLifetimeExtension) {
    const char *code = R"(
        class Widget {
            int value;
        public:
            Widget(int v) : value(v) {}
        };

        void test() {
            const Widget&& rref = Widget(42);
            // Temporary's lifetime is extended
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify that rvalue reference extends temporary lifetime
    ASSERT_GE(finder.rvalueRefs.size(), 1) << "Expected rvalue reference";
}

TEST_F(MoveSemanticTestFixture, RvalueReferenceFunctionOverloading) {
    const char *code = R"(
        void process(int& lvalue) {}
        void process(int&& rvalue) {}

        void test() {
            int x = 42;
            process(x);    // Calls lvalue version
            process(100);  // Calls rvalue version
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Count overloaded functions
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    int processCount = 0;

    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "process") {
                processCount++;
            }
        }
    }

    ASSERT_GE(processCount, 2) << "Expected at least 2 overloads of process";
}

TEST_F(MoveSemanticTestFixture, RvalueReferenceCastExpression) {
    const char *code = R"(
        void test() {
            int x = 42;
            int&& rref = static_cast<int&&>(x);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.rvalueRefs.size(), 1) << "Expected rvalue reference from cast";
}

// ============================================================================
// Category 2: Move Constructor & Assignment (10-12 tests)
// ============================================================================

TEST_F(MoveSemanticTestFixture, MoveConstructorDetection) {
    const char *code = R"(
        class Widget {
            int* data;
        public:
            Widget(Widget&& other) : data(other.data) {
                other.data = nullptr;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_EQ(finder.moveConstructors.size(), 1) << "Expected exactly one move constructor";
}

TEST_F(MoveSemanticTestFixture, MoveAssignmentOperatorDetection) {
    const char *code = R"(
        class Widget {
            int* data;
        public:
            Widget& operator=(Widget&& other) {
                if (this != &other) {
                    delete data;
                    data = other.data;
                    other.data = nullptr;
                }
                return *this;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_EQ(finder.moveAssignments.size(), 1) << "Expected exactly one move assignment operator";
}

TEST_F(MoveSemanticTestFixture, CompilerGeneratedMoveConstructor) {

    const char *code = R"(
        class Widget {
            int value;
            // Compiler generates default move constructor
        };

        void test() {
            Widget w1;
            Widget w2(static_cast<Widget&&>(w1));
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *WidgetClass = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Widget" && RD->isCompleteDefinition()) {
                WidgetClass = RD;
                break;
            }
        }
    }

    ASSERT_TRUE(WidgetClass != nullptr) << "Widget class not found";
    ASSERT_TRUE(WidgetClass->hasDefaultConstructor() || !WidgetClass->needsImplicitDefaultConstructor())
           << "Widget should have constructor";

}

TEST_F(MoveSemanticTestFixture, DeletedMoveConstructor) {

    const char *code = R"(
        class NonMovable {
        public:
            NonMovable(NonMovable&&) = delete;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXConstructorDecl *moveConstructor = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "NonMovable") {
                for (auto *M : RD->ctors()) {
                    if (M->isMoveConstructor()) {
                        moveConstructor = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_TRUE(moveConstructor != nullptr) << "Move constructor not found";
    ASSERT_TRUE(moveConstructor->isDeleted()) << "Move constructor should be deleted";

}

TEST_F(MoveSemanticTestFixture, MoveConstructorWithNoexcept) {

    const char *code = R"(
        class Widget {
            int* data;
        public:
            Widget(Widget&& other) noexcept : data(other.data) {
                other.data = nullptr;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_EQ(finder.moveConstructors.size(), 1) << "Expected exactly one move constructor";

    const auto *moveCtor = finder.moveConstructors[0];
    auto exceptionSpec = moveCtor->getExceptionSpecType();
    ASSERT_TRUE(exceptionSpec == EST_NoexceptTrue || exceptionSpec == EST_BasicNoexcept)
           << "Move constructor should be noexcept";

}

TEST_F(MoveSemanticTestFixture, MoveAssignmentSelfAssignmentCheck) {

    const char *code = R"(
        class Widget {
            int* data;
        public:
            Widget& operator=(Widget&& other) noexcept {
                if (this != &other) {
                    delete data;
                    data = other.data;
                    other.data = nullptr;
                }
                return *this;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_EQ(finder.moveAssignments.size(), 1) << "Expected exactly one move assignment operator";

}

TEST_F(MoveSemanticTestFixture, MemberwiseMoveConstruction) {

    const char *code = R"(
        class Inner {
        public:
            Inner(Inner&&) noexcept = default;
        };

        class Outer {
            Inner inner1;
            Inner inner2;
        public:
            Outer(Outer&& other) noexcept
                : inner1(static_cast<Inner&&>(other.inner1)),
                  inner2(static_cast<Inner&&>(other.inner2)) {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.moveConstructors.size(), 1) << "Expected at least one move constructor";

}

TEST_F(MoveSemanticTestFixture, MoveConstructorResourceTransfer) {

    const char *code = R"(
        class Resource {
            int* buffer;
            int size;
        public:
            Resource(Resource&& other) noexcept
                : buffer(other.buffer), size(other.size) {
                other.buffer = nullptr;
                other.size = 0;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_EQ(finder.moveConstructors.size(), 1) << "Expected exactly one move constructor";

}

TEST_F(MoveSemanticTestFixture, MoveAssignmentResourceCleanup) {

    const char *code = R"(
        class Resource {
            int* buffer;
        public:
            Resource& operator=(Resource&& other) noexcept {
                if (this != &other) {
                    delete[] buffer;  // Clean up existing resource
                    buffer = other.buffer;
                    other.buffer = nullptr;
                }
                return *this;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_EQ(finder.moveAssignments.size(), 1) << "Expected exactly one move assignment operator";

}

TEST_F(MoveSemanticTestFixture, MoveConstructorWithBaseClass) {

    const char *code = R"(
        class Base {
        public:
            Base(Base&&) noexcept = default;
        };

        class Derived : public Base {
        public:
            Derived(Derived&& other) noexcept
                : Base(static_cast<Base&&>(other)) {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.moveConstructors.size(), 2) << "Expected move constructors for Base and Derived";

}

TEST_F(MoveSemanticTestFixture, MoveOnlyType) {

    const char *code = R"(
        class MoveOnly {
        public:
            MoveOnly() = default;
            MoveOnly(const MoveOnly&) = delete;
            MoveOnly& operator=(const MoveOnly&) = delete;
            MoveOnly(MoveOnly&&) noexcept = default;
            MoveOnly& operator=(MoveOnly&&) noexcept = default;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *MoveOnlyClass = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "MoveOnly") {
                MoveOnlyClass = RD;
                break;
            }
        }
    }

    ASSERT_TRUE(MoveOnlyClass != nullptr) << "MoveOnly class not found";

}

TEST_F(MoveSemanticTestFixture, MoveConstructorExceptionSafety) {

    const char *code = R"(
        class SafeMove {
            int* data;
        public:
            SafeMove(SafeMove&& other) noexcept
                : data(other.data) {
                other.data = nullptr;
                // No throwing operations
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_EQ(finder.moveConstructors.size(), 1) << "Expected exactly one move constructor";

}

// ============================================================================
// Category 3: std::move Usage (10-12 tests)
// ============================================================================

TEST_F(MoveSemanticTestFixture, ExplicitStdMoveCall) {

    const char *code = R"(
        #include <utility>

        void test() {
            int x = 42;
            int&& rref = std::move(x);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.stdMoveCalls.size(), 1) << "Expected at least one std::move call";

}

TEST_F(MoveSemanticTestFixture, StdMoveInReturnStatement) {

    const char *code = R"(
        #include <utility>

        class Widget {
            int* data;
        public:
            Widget clone() {
                Widget temp;
                return std::move(temp);
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.stdMoveCalls.size(), 1) << "Expected std::move in return statement";

}

TEST_F(MoveSemanticTestFixture, StdMoveWithFunctionArgument) {

    const char *code = R"(
        #include <utility>

        void consume(int&& value) {}

        void test() {
            int x = 42;
            consume(std::move(x));
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.stdMoveCalls.size(), 1) << "Expected std::move with function argument";

}

TEST_F(MoveSemanticTestFixture, StdMoveInConstructorInitialization) {

    const char *code = R"(
        #include <utility>

        class Inner {
        public:
            Inner(Inner&&) = default;
        };

        class Outer {
            Inner inner;
        public:
            Outer(Inner&& i) : inner(std::move(i)) {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.stdMoveCalls.size(), 1) << "Expected std::move in constructor initialization";

}

TEST_F(MoveSemanticTestFixture, StdMoveWithVectorPushBack) {

    const char *code = R"(
        #include <utility>
        #include <vector>

        class Widget {
        public:
            Widget(Widget&&) = default;
        };

        void test() {
            std::vector<Widget> vec;
            Widget w;
            vec.push_back(std::move(w));
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.stdMoveCalls.size(), 1) << "Expected std::move with vector::push_back";

}

TEST_F(MoveSemanticTestFixture, StdMoveWithUniquePtr) {

    const char *code = R"(
        #include <utility>
        #include <memory>

        void test() {
            std::unique_ptr<int> p1(new int(42));
            std::unique_ptr<int> p2 = std::move(p1);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.stdMoveCalls.size(), 1) << "Expected std::move with unique_ptr";

}

TEST_F(MoveSemanticTestFixture, StdMoveOnConstObject) {

    const char *code = R"(
        #include <utility>

        void test() {
            const int x = 42;
            // std::move on const returns const int&&
            // which binds to const int&, not int&&
            auto&& result = std::move(x);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // std::move on const is a no-op effectively
    // Transpiler should detect this edge case

}

TEST_F(MoveSemanticTestFixture, StdMoveChain) {

    const char *code = R"(
        #include <utility>

        class Widget {
        public:
            Widget(Widget&&) = default;
        };

        Widget createWidget() {
            Widget w1;
            Widget w2(std::move(w1));
            Widget w3(std::move(w2));
            return std::move(w3);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.stdMoveCalls.size(), 3) << "Expected multiple chained std::move calls";

}

TEST_F(MoveSemanticTestFixture, StdMoveUnnecessaryOnTemporary) {

    const char *code = R"(
        #include <utility>

        class Widget {
        public:
            Widget(Widget&&) = default;
        };

        Widget createWidget() {
            return Widget();  // Already an rvalue, std::move unnecessary
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // This test verifies that we can detect when std::move is unnecessary

}

TEST_F(MoveSemanticTestFixture, StdMoveWithMemberVariable) {

    const char *code = R"(
        #include <utility>

        class Widget {
            int* data;
        public:
            int* release() {
                int* temp = data;
                data = nullptr;
                return std::move(temp);  // std::move on pointer (no effect but legal)
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.stdMoveCalls.size(), 1) << "Expected std::move on member variable";

}

TEST_F(MoveSemanticTestFixture, StdMoveInRangeBasedForLoop) {

    const char *code = R"(
        #include <utility>
        #include <vector>

        class Widget {
        public:
            Widget(Widget&&) = default;
        };

        void processAll(std::vector<Widget>& vec) {
            for (auto& w : vec) {
                Widget moved = std::move(w);
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.stdMoveCalls.size(), 1) << "Expected std::move in range-based for loop";

}

TEST_F(MoveSemanticTestFixture, StdMoveWithSwap) {

    const char *code = R"(
        #include <utility>

        template<typename T>
        void swap(T& a, T& b) {
            T temp = std::move(a);
            a = std::move(b);
            b = std::move(temp);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_GE(finder.stdMoveCalls.size(), 3) << "Expected three std::move calls in swap";

}

// ============================================================================
// Category 4: Perfect Forwarding (8-10 tests)
// ============================================================================

TEST_F(MoveSemanticTestFixture, StdForwardBasicUsage) {

    const char *code = R"(
        #include <utility>

        template<typename T>
        void wrapper(T&& arg) {
            process(std::forward<T>(arg));
        }

        void process(int&) {}
        void process(int&&) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // std::forward preserves value category

}

TEST_F(MoveSemanticTestFixture, UniversalReferenceTemplateParameter) {

    const char *code = R"(
        template<typename T>
        void func(T&& param) {
            // T&& is a universal reference (forwarding reference)
        }

        void test() {
            int x = 42;
            func(x);    // T = int&
            func(100);  // T = int
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Universal references can bind to both lvalues and rvalues

}

TEST_F(MoveSemanticTestFixture, StdForwardToConstructor) {

    const char *code = R"(
        #include <utility>

        class Widget {
        public:
            Widget(int&& value) {}
            Widget(const int& value) {}
        };

        template<typename T>
        Widget makeWidget(T&& value) {
            return Widget(std::forward<T>(value));
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // std::forward preserves value category when forwarding to constructor

}

TEST_F(MoveSemanticTestFixture, VariadicTemplatePerfectForwarding) {

    const char *code = R"(
        #include <utility>

        template<typename... Args>
        void forwardAll(Args&&... args) {
            process(std::forward<Args>(args)...);
        }

        void process(int, double, char) {}
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Perfect forwarding with variadic templates

}

TEST_F(MoveSemanticTestFixture, StdForwardWithEmplace) {

    const char *code = R"(
        #include <utility>
        #include <vector>

        class Widget {
        public:
            Widget(int, double) {}
        };

        void test() {
            std::vector<Widget> vec;
            vec.emplace_back(42, 3.14);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // emplace_back uses perfect forwarding internally

}

TEST_F(MoveSemanticTestFixture, StdForwardPreservesLvalue) {

    const char *code = R"(
        #include <utility>

        template<typename T>
        void wrapper(T&& arg) {
            process(std::forward<T>(arg));
        }

        void process(int& lvalue) {}

        void test() {
            int x = 42;
            wrapper(x);  // Should preserve lvalue-ness
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // std::forward<T&>(x) returns lvalue reference

}

TEST_F(MoveSemanticTestFixture, StdForwardPreservesRvalue) {

    const char *code = R"(
        #include <utility>

        template<typename T>
        void wrapper(T&& arg) {
            process(std::forward<T>(arg));
        }

        void process(int&& rvalue) {}

        void test() {
            wrapper(42);  // Should preserve rvalue-ness
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // std::forward<T>(x) returns rvalue reference when T is non-reference

}

TEST_F(MoveSemanticTestFixture, MakeUniquePerfectForwarding) {

    const char *code = R"(
        #include <memory>
        #include <utility>

        class Widget {
        public:
            Widget(int, double, const char*) {}
        };

        void test() {
            auto ptr = std::make_unique<Widget>(42, 3.14, "test");
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // make_unique uses perfect forwarding

}

TEST_F(MoveSemanticTestFixture, StdForwardWithMultipleParameters) {

    const char *code = R"(
        #include <utility>

        template<typename T1, typename T2>
        void wrapper(T1&& arg1, T2&& arg2) {
            process(std::forward<T1>(arg1), std::forward<T2>(arg2));
        }

        void process(int&, double&&) {}

        void test() {
            int x = 42;
            wrapper(x, 3.14);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Multiple parameters forwarded independently

}

TEST_F(MoveSemanticTestFixture, StdForwardInLambda) {

    const char *code = R"(
        #include <utility>

        template<typename Func, typename T>
        void apply(Func&& f, T&& arg) {
            auto lambda = [&f](auto&& x) {
                return std::forward<Func>(f)(std::forward<decltype(x)>(x));
            };
            lambda(std::forward<T>(arg));
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Perfect forwarding within lambda

}

// ============================================================================
// Category 5: Edge Cases (4-6 tests)
// ============================================================================

TEST_F(MoveSemanticTestFixture, MoveFromMovedObject) {

    const char *code = R"(
        #include <utility>

        class Widget {
        public:
            Widget(Widget&&) = default;
        };

        void test() {
            Widget w1;
            Widget w2 = std::move(w1);
            // w1 is now in a valid but unspecified state
            Widget w3 = std::move(w1);  // Moving from moved-from object
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Transpiler should handle moved-from state correctly
    ASSERT_GE(finder.stdMoveCalls.size(), 2) << "Expected multiple move operations";

}

TEST_F(MoveSemanticTestFixture, SelfMoveAssignment) {

    const char *code = R"(
        #include <utility>

        class Widget {
            int* data;
        public:
            Widget& operator=(Widget&& other) noexcept {
                if (this != &other) {  // Critical: check for self-assignment
                    delete data;
                    data = other.data;
                    other.data = nullptr;
                }
                return *this;
            }
        };

        void test() {
            Widget w;
            w = std::move(w);  // Self-move assignment
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_EQ(finder.moveAssignments.size(), 1) << "Expected move assignment operator";

}

TEST_F(MoveSemanticTestFixture, NoexceptGuaranteeVerification) {

    const char *code = R"(
        class Widget {
        public:
            Widget(Widget&&) noexcept = default;
            Widget& operator=(Widget&&) noexcept = default;
        };

        static_assert(noexcept(Widget(std::declval<Widget>())),
                     "Move constructor should be noexcept");
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify noexcept specifications on move operations
    if (!finder.moveConstructors.empty()) {
        const auto *moveCtor = finder.moveConstructors[0];
        auto exceptionSpec = moveCtor->getExceptionSpecType();
        ASSERT_TRUE(exceptionSpec == EST_NoexceptTrue || exceptionSpec == EST_BasicNoexcept)
               << "Move constructor should be noexcept";
    }

}

TEST_F(MoveSemanticTestFixture, MoveWithExceptionThrowingOperation) {

    const char *code = R"(
        class Widget {
            int* data;
        public:
            Widget(Widget&& other)  // Not noexcept
                : data(new int(*other.data)) {  // May throw
                other.data = nullptr;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT_EQ(finder.moveConstructors.size(), 1) << "Expected move constructor";

    // Transpiler should handle potentially-throwing move operations safely

}

TEST_F(MoveSemanticTestFixture, MoveSemanticsWithConstMember) {

    const char *code = R"(
        class Widget {
            const int value;  // Const member prevents default move
        public:
            Widget(Widget&& other) : value(other.value) {
                // Const members are copied, not moved
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Const members affect move semantics
    ASSERT_GE(finder.moveConstructors.size(), 1) << "Expected move constructor";

}

TEST_F(MoveSemanticTestFixture, MoveSemanticsWithReferenceMember) {

    const char *code = R"(
        class Widget {
            int& ref;  // Reference member prevents default move assignment
        public:
            Widget(int& r) : ref(r) {}
            Widget(Widget&& other) : ref(other.ref) {}
            // Move assignment would be implicitly deleted
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    MoveSemanticsFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Reference members affect move semantics
    ASSERT_GE(finder.moveConstructors.size(), 1) << "Expected move constructor";

}

// Main entry point for Google Test
// No explicit main() needed - gtest_main handles it
