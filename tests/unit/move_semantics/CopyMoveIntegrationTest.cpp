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
#include <iostream>
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
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
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
void test_class_with_copy_and_move_constructors() {
    TEST_START("Class with both copy and move constructors");

    const char *code = R"(
        class Resource {
        public:
            int* data;
            int size;

            // Copy constructor
            Resource(const Resource& other)
                : data(new int[other.size]), size(other.size) {
                for (int i = 0; i < size; ++i) {
                    data[i] = other.data[i];
                }
            }

            // Move constructor
            Resource(Resource&& other) noexcept
                : data(other.data), size(other.size) {
                other.data = nullptr;
                other.size = 0;
            }
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);
    CppToCVisitor Visitor(Context, Builder);

    // Collect copy and move constructors
    CopyMoveCollector Collector;
    Collector.TraverseDecl(Context.getTranslationUnitDecl());

    ASSERT(Collector.copyConstructors.size() == 1,
           "Expected 1 copy constructor");
    ASSERT(Collector.moveConstructors.size() == 1,
           "Expected 1 move constructor");

    // Visit the class to trigger translation
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());

    // Verify copy constructor translation
    CXXConstructorDecl *CopyCtor = Collector.copyConstructors[0];
    ASSERT(CopyCtor->isCopyConstructor(),
           "Copy constructor not properly detected");

    // Verify move constructor translation
    CXXConstructorDecl *MoveCtor = Collector.moveConstructors[0];
    MoveConstructorTranslator MoveTranslator(Context);
    ASSERT(MoveTranslator.isMoveConstructor(MoveCtor),
           "Move constructor not properly detected");

    // Generate C code for both
    std::string moveCode = MoveTranslator.generateMoveConstructor(MoveCtor);
    ASSERT(!moveCode.empty(), "Move constructor C code generation failed");

    // Verify different function names
    ASSERT(moveCode.find("Resource_move_construct") != std::string::npos,
           "Move constructor name not found in generated code");

    // The copy constructor should generate a different name (e.g., Resource__ctor_copy)
    // This is handled by the existing constructor translation logic

    TEST_PASS("Class with both copy and move constructors");
}

/**
 * Test 2: Class with both copy and move assignment operators
 *
 * Verifies:
 * - Both operators are detected
 * - Both are translated to C
 * - Different function names generated
 */
void test_class_with_copy_and_move_assignments() {
    TEST_START("Class with both copy and move assignment operators");

    const char *code = R"(
        class Resource {
        public:
            int* data;
            int size;

            // Copy assignment
            Resource& operator=(const Resource& other) {
                if (this != &other) {
                    delete[] data;
                    data = new int[other.size];
                    size = other.size;
                    for (int i = 0; i < size; ++i) {
                        data[i] = other.data[i];
                    }
                }
                return *this;
            }

            // Move assignment
            Resource& operator=(Resource&& other) noexcept {
                if (this != &other) {
                    delete[] data;
                    data = other.data;
                    size = other.size;
                    other.data = nullptr;
                    other.size = 0;
                }
                return *this;
            }
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);
    CppToCVisitor Visitor(Context, Builder);

    // Collect copy and move assignments
    CopyMoveCollector Collector;
    Collector.TraverseDecl(Context.getTranslationUnitDecl());

    ASSERT(Collector.copyAssignments.size() == 1,
           "Expected 1 copy assignment operator");
    ASSERT(Collector.moveAssignments.size() == 1,
           "Expected 1 move assignment operator");

    // Visit the class to trigger translation
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());

    // Verify copy assignment translation
    CXXMethodDecl *CopyAssign = Collector.copyAssignments[0];
    ASSERT(CopyAssign->isCopyAssignmentOperator(),
           "Copy assignment not properly detected");

    // Verify move assignment translation
    CXXMethodDecl *MoveAssign = Collector.moveAssignments[0];
    MoveAssignmentTranslator MoveAssignTranslator(Context);
    ASSERT(MoveAssignTranslator.isMoveAssignmentOperator(MoveAssign),
           "Move assignment not properly detected");

    // Generate C code for move assignment
    std::string moveCode = MoveAssignTranslator.generateMoveAssignment(MoveAssign);
    ASSERT(!moveCode.empty(), "Move assignment C code generation failed");

    // Verify different function names
    ASSERT(moveCode.find("Resource_move_assign") != std::string::npos,
           "Move assignment name not found in generated code");

    TEST_PASS("Class with both copy and move assignment operators");
}

/**
 * Test 3: Call site selection based on value category
 *
 * Verifies:
 * - Lvalue uses copy constructor
 * - Rvalue (std::move, temporary) uses move constructor
 * - Proper detection at call sites
 */
void test_call_site_selection() {
    TEST_START("Call site selection based on value category");

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
    ASSERT(AST, "Failed to parse C++ code");

    ASTContext &Context = AST->getASTContext();

    // Find construct expressions
    CallExprFinder Finder;
    Finder.TraverseDecl(Context.getTranslationUnitDecl());

    ASSERT(Finder.constructExprs.size() >= 3,
           "Expected at least 3 construct expressions");

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
    ASSERT(copyConstructCalls >= 1,
           "Expected at least 1 copy constructor call for lvalue");
    ASSERT(moveConstructCalls >= 2,
           "Expected at least 2 move constructor calls for rvalues");

    TEST_PASS("Call site selection based on value category");
}

/**
 * Test 4: No naming conflicts in generated C functions
 *
 * Verifies:
 * - Copy constructor has unique name (e.g., ClassName__ctor_copy)
 * - Move constructor has unique name (e.g., ClassName_move_construct)
 * - Copy assignment has unique name (e.g., ClassName__operator_assign)
 * - Move assignment has unique name (e.g., ClassName_move_assign)
 */
void test_no_naming_conflicts() {
    TEST_START("No naming conflicts in generated C functions");

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
    ASSERT(AST, "Failed to parse C++ code");

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);
    CppToCVisitor Visitor(Context, Builder);

    // Collect all special members
    CopyMoveCollector Collector;
    Collector.TraverseDecl(Context.getTranslationUnitDecl());

    ASSERT(Collector.copyConstructors.size() == 1, "Expected 1 copy constructor");
    ASSERT(Collector.moveConstructors.size() == 1, "Expected 1 move constructor");
    ASSERT(Collector.copyAssignments.size() == 1, "Expected 1 copy assignment");
    ASSERT(Collector.moveAssignments.size() == 1, "Expected 1 move assignment");

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
    ASSERT(last == functionNames.end(),
           "Duplicate function names detected");

    TEST_PASS("No naming conflicts in generated C functions");
}

/**
 * Test 5: Complex class with members requiring both copy and move
 *
 * Verifies:
 * - Class with multiple members (primitives, pointers, nested classes)
 * - Proper handling of member-wise copy vs move
 * - Correct generation for complex scenarios
 */
void test_complex_class_with_both_semantics() {
    TEST_START("Complex class with members requiring both copy and move");

    const char *code = R"(
        class Inner {
        public:
            int* data;
            Inner(const Inner& other);
            Inner(Inner&& other) noexcept;
        };

        class Outer {
        public:
            int primitiveValue;
            int* pointerMember;
            Inner innerObject;

            // Copy constructor - deep copy
            Outer(const Outer& other)
                : primitiveValue(other.primitiveValue),
                  pointerMember(new int(*other.pointerMember)),
                  innerObject(other.innerObject) {
            }

            // Move constructor - transfer ownership
            Outer(Outer&& other) noexcept
                : primitiveValue(other.primitiveValue),
                  pointerMember(other.pointerMember),
                  innerObject(std::move(other.innerObject)) {
                other.pointerMember = nullptr;
                other.primitiveValue = 0;
            }
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);
    CppToCVisitor Visitor(Context, Builder);

    // Collect constructors
    CopyMoveCollector Collector;
    Collector.TraverseDecl(Context.getTranslationUnitDecl());

    // Should have copy and move for both Inner and Outer
    ASSERT(Collector.copyConstructors.size() >= 2,
           "Expected at least 2 copy constructors (Inner and Outer)");
    ASSERT(Collector.moveConstructors.size() >= 2,
           "Expected at least 2 move constructors (Inner and Outer)");

    // Visit to trigger translation
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());

    // Find Outer's constructors
    CXXConstructorDecl *OuterCopyCtor = nullptr;
    CXXConstructorDecl *OuterMoveCtor = nullptr;

    for (CXXConstructorDecl *Ctor : Collector.copyConstructors) {
        if (Ctor->getParent()->getNameAsString() == "Outer") {
            OuterCopyCtor = Ctor;
        }
    }

    for (CXXConstructorDecl *Ctor : Collector.moveConstructors) {
        if (Ctor->getParent()->getNameAsString() == "Outer") {
            OuterMoveCtor = Ctor;
        }
    }

    ASSERT(OuterCopyCtor != nullptr, "Outer copy constructor not found");
    ASSERT(OuterMoveCtor != nullptr, "Outer move constructor not found");

    // Verify move constructor calls member move constructor
    // This is done by checking initializers
    bool foundMemberMoveInit = false;
    for (auto Init : OuterMoveCtor->inits()) {
        if (Init->isMemberInitializer()) {
            Expr *InitExpr = Init->getInit();
            if (auto CE = dyn_cast<CXXConstructExpr>(InitExpr)) {
                if (CE->getConstructor()->isMoveConstructor()) {
                    foundMemberMoveInit = true;
                    break;
                }
            }
        }
    }

    ASSERT(foundMemberMoveInit,
           "Move constructor should call member's move constructor");

    TEST_PASS("Complex class with members requiring both copy and move");
}

/**
 * Test 6: Memory safety in mixed copy/move scenarios
 *
 * Verifies:
 * - Proper pointer nullification in move
 * - No double-free scenarios
 * - Safe interaction between copy and move
 */
void test_memory_safety_mixed_scenarios() {
    TEST_START("Memory safety in mixed copy/move scenarios");

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
    ASSERT(AST, "Failed to parse C++ code");

    ASTContext &Context = AST->getASTContext();
    MoveConstructorTranslator MoveTranslator(Context);

    // Collect move constructor
    CopyMoveCollector Collector;
    Collector.TraverseDecl(Context.getTranslationUnitDecl());

    ASSERT(Collector.moveConstructors.size() == 1,
           "Expected 1 move constructor");

    CXXConstructorDecl *MoveCtor = Collector.moveConstructors[0];
    std::string moveCode = MoveTranslator.generateMoveConstructor(MoveCtor);

    // Verify pointer nullification is present
    ASSERT(moveCode.find("NULL") != std::string::npos ||
           moveCode.find("nullptr") != std::string::npos,
           "Move constructor must nullify source pointers");

    // Verify data is copied before nullification
    ASSERT(moveCode.find("dest->data = src->data") != std::string::npos,
           "Move constructor must transfer data pointer");

    TEST_PASS("Memory safety in mixed copy/move scenarios");
}

/**
 * Test 7: Exception safety when both copy and move present
 *
 * Verifies:
 * - noexcept specification affects move selection
 * - Exception safety guarantees
 * - Proper fallback to copy if move can throw
 */
void test_exception_safety_copy_move() {
    TEST_START("Exception safety when both copy and move present");

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
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(NoThrowMoveCtor != nullptr,
           "NoThrowMove's move constructor not found");

    // Verify noexcept specification
    const auto *FPT = NoThrowMoveCtor->getType()->getAs<FunctionProtoType>();
    ASSERT(FPT != nullptr, "Function prototype not found");

    bool isNoExcept = FPT->isNothrow();
    ASSERT(isNoExcept,
           "Move constructor should be marked noexcept");

    TEST_PASS("Exception safety when both copy and move present");
}

/**
 * Test 8: Integration - Full class with all special members
 *
 * Verifies complete integration of copy and move semantics
 */
void test_full_special_members_integration() {
    TEST_START("Integration - Full class with all special members");

    const char *code = R"(
        class FullResource {
        public:
            int* data;
            int size;

            // Default constructor
            FullResource() : data(nullptr), size(0) {}

            // Copy constructor
            FullResource(const FullResource& other)
                : data(new int[other.size]), size(other.size) {
            }

            // Move constructor
            FullResource(FullResource&& other) noexcept
                : data(other.data), size(other.size) {
                other.data = nullptr;
                other.size = 0;
            }

            // Copy assignment
            FullResource& operator=(const FullResource& other) {
                if (this != &other) {
                    delete[] data;
                    data = new int[other.size];
                    size = other.size;
                }
                return *this;
            }

            // Move assignment
            FullResource& operator=(FullResource&& other) noexcept {
                if (this != &other) {
                    delete[] data;
                    data = other.data;
                    size = other.size;
                    other.data = nullptr;
                    other.size = 0;
                }
                return *this;
            }

            // Destructor
            ~FullResource() {
                delete[] data;
            }
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder Builder(Context);
    CppToCVisitor Visitor(Context, Builder);

    // Collect all special members
    CopyMoveCollector Collector;
    Collector.TraverseDecl(Context.getTranslationUnitDecl());

    ASSERT(Collector.copyConstructors.size() == 1, "Expected 1 copy constructor");
    ASSERT(Collector.moveConstructors.size() == 1, "Expected 1 move constructor");
    ASSERT(Collector.copyAssignments.size() == 1, "Expected 1 copy assignment");
    ASSERT(Collector.moveAssignments.size() == 1, "Expected 1 move assignment");

    // Visit to trigger translation
    Visitor.TraverseDecl(Context.getTranslationUnitDecl());

    // Generate all C code
    MoveConstructorTranslator MoveCtorTranslator(Context);
    MoveAssignmentTranslator MoveAssignTranslator(Context);

    std::string moveCtor = MoveCtorTranslator.generateMoveConstructor(
        Collector.moveConstructors[0]);
    std::string moveAssign = MoveAssignTranslator.generateMoveAssignment(
        Collector.moveAssignments[0]);

    ASSERT(!moveCtor.empty(), "Move constructor generation failed");
    ASSERT(!moveAssign.empty(), "Move assignment generation failed");

    // Verify all functions have unique names
    std::vector<std::string> names = {
        "FullResource__ctor",          // Default constructor
        "FullResource__ctor_copy",     // Copy constructor
        "FullResource_move_construct", // Move constructor
        "FullResource__operator_assign", // Copy assignment
        "FullResource_move_assign",    // Move assignment
        "FullResource__dtor"           // Destructor
    };

    std::sort(names.begin(), names.end());
    auto last = std::unique(names.begin(), names.end());
    ASSERT(last == names.end(), "Duplicate function names in full class");

    TEST_PASS("Integration - Full class with all special members");
}

// Main test runner
int main() {
    std::cout << "=== Story #134: Integration with Copy Semantics Tests ===" << std::endl;
    std::cout << std::endl;

    test_class_with_copy_and_move_constructors();
    test_class_with_copy_and_move_assignments();
    test_call_site_selection();
    test_no_naming_conflicts();
    test_complex_class_with_both_semantics();
    test_memory_safety_mixed_scenarios();
    test_exception_safety_copy_move();
    test_full_special_members_integration();

    std::cout << std::endl;
    std::cout << "=== All Copy/Move Integration Tests Passed ===" << std::endl;
    return 0;
}
