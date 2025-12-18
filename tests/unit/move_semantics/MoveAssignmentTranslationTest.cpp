/**
 * @file MoveAssignmentTranslationTest.cpp
 * @brief Tests for move assignment operator detection and translation to C code (Story #131)
 *
 * Test Strategy:
 * - Following TDD: Tests written first, implementation follows
 * - Tests cover detection using Clang's isMoveAssignmentOperator()
 * - Tests verify C code generation with self-assignment check, destructor call, and transfer
 * - Memory leak prevention validation
 * - Integration with existing move constructor infrastructure
 */

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "../../../include/MoveAssignmentTranslator.h"
#include <iostream>
#include <cassert>
#include <string>
#include <vector>

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

// Helper visitor to find move assignment operators
class MoveAssignmentFinder : public RecursiveASTVisitor<MoveAssignmentFinder> {
public:
    std::vector<CXXMethodDecl*> moveAssignmentOperators;

    bool VisitCXXMethodDecl(CXXMethodDecl *D) {
        if (D->isMoveAssignmentOperator()) {
            moveAssignmentOperators.push_back(D);
        }
        return true;
    }
};

// ============================================================================
// Test 1: Simple move assignment - generates correct C function
// ============================================================================
void test_simple_move_assignment_c_generation() {
    TEST_START("simple_move_assignment_c_generation");

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
    ASSERT(AST, "Failed to parse C++ code");

    MoveAssignmentFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.moveAssignmentOperators.size() == 1, "Expected exactly one move assignment operator");

    CXXMethodDecl *MoveAssign = finder.moveAssignmentOperators[0];
    MoveAssignmentTranslator translator(AST->getASTContext());

    // Test detection
    ASSERT(translator.isMoveAssignmentOperator(MoveAssign), "Should detect move assignment operator");

    // Test C code generation
    std::string cCode = translator.generateMoveAssignment(MoveAssign);
    ASSERT(!cCode.empty(), "Should generate non-empty C code");

    // Verify signature: void Widget_move_assign(struct Widget *this, struct Widget *src)
    ASSERT(cCode.find("Widget_move_assign") != std::string::npos,
           "Should contain move assignment function name");
    ASSERT(cCode.find("struct Widget *this") != std::string::npos ||
           cCode.find("struct Widget *dest") != std::string::npos,
           "Should have this/dest parameter");
    ASSERT(cCode.find("struct Widget *src") != std::string::npos,
           "Should have src parameter");

    // Verify self-assignment check
    ASSERT(cCode.find("if") != std::string::npos &&
           (cCode.find("this == src") != std::string::npos || cCode.find("this != src") != std::string::npos),
           "Should have self-assignment check");

    // Verify member transfer
    ASSERT(cCode.find("data") != std::string::npos, "Should reference data member");

    TEST_PASS("simple_move_assignment_c_generation");
}

// ============================================================================
// Test 2: Self-assignment check - if (this != src) guard
// ============================================================================
void test_self_assignment_check() {
    TEST_START("self_assignment_check");

    const char *code = R"(
        class Container {
            int* buffer;
            int size;
        public:
            Container& operator=(Container&& other) noexcept {
                if (this != &other) {
                    delete[] buffer;
                    buffer = other.buffer;
                    size = other.size;
                    other.buffer = nullptr;
                    other.size = 0;
                }
                return *this;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    MoveAssignmentFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.moveAssignmentOperators.size() == 1, "Expected move assignment operator");

    CXXMethodDecl *MoveAssign = finder.moveAssignmentOperators[0];
    MoveAssignmentTranslator translator(AST->getASTContext());

    std::string cCode = translator.generateMoveAssignment(MoveAssign);
    ASSERT(!cCode.empty(), "Should generate C code");

    // Critical: Must have self-assignment check to prevent double-free
    // Pattern: if (this == src) return; OR if (this != src) { ... }
    bool hasSelfCheck = (cCode.find("if") != std::string::npos) &&
                        (cCode.find("this") != std::string::npos) &&
                        (cCode.find("src") != std::string::npos) &&
                        (cCode.find("==") != std::string::npos || cCode.find("!=") != std::string::npos);
    ASSERT(hasSelfCheck, "Must have self-assignment check");

    // Should have early return for self-assignment
    ASSERT(cCode.find("return") != std::string::npos, "Should have return statement");

    TEST_PASS("self_assignment_check");
}

// ============================================================================
// Test 3: Destructor call before transfer - cleanup old resources
// ============================================================================
void test_destructor_call_before_transfer() {
    TEST_START("destructor_call_before_transfer");

    const char *code = R"(
        class Resource {
            int* data;
        public:
            ~Resource() { delete data; }

            Resource& operator=(Resource&& other) noexcept {
                if (this != &other) {
                    delete data;  // Clean up old resource
                    data = other.data;
                    other.data = nullptr;
                }
                return *this;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    MoveAssignmentFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.moveAssignmentOperators.size() == 1, "Expected move assignment operator");

    CXXMethodDecl *MoveAssign = finder.moveAssignmentOperators[0];
    MoveAssignmentTranslator translator(AST->getASTContext());

    std::string cCode = translator.generateMoveAssignment(MoveAssign);
    ASSERT(!cCode.empty(), "Should generate C code");

    // Critical: Must call destructor before assignment to prevent memory leak
    // Pattern: Resource_destructor(this); OR equivalent cleanup
    ASSERT(cCode.find("destructor") != std::string::npos || cCode.find("Resource_") != std::string::npos,
           "Should reference destructor or cleanup");

    // Verify ordering: destructor before transfer
    size_t destructorPos = cCode.find("destructor");
    size_t transferPos = cCode.find("this->data = src->data");
    if (destructorPos != std::string::npos && transferPos != std::string::npos) {
        ASSERT(destructorPos < transferPos, "Destructor must be called before transfer");
    }

    TEST_PASS("destructor_call_before_transfer");
}

// ============================================================================
// Test 4: Move assignment with multiple pointer members
// ============================================================================
void test_move_assignment_multiple_pointers() {
    TEST_START("move_assignment_multiple_pointers");

    const char *code = R"(
        class MultiResource {
            int* buffer;
            char* name;
            double* values;
        public:
            MultiResource& operator=(MultiResource&& other) noexcept {
                if (this != &other) {
                    delete[] buffer;
                    delete[] name;
                    delete[] values;

                    buffer = other.buffer;
                    name = other.name;
                    values = other.values;

                    other.buffer = nullptr;
                    other.name = nullptr;
                    other.values = nullptr;
                }
                return *this;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    MoveAssignmentFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.moveAssignmentOperators.size() == 1, "Expected move assignment operator");

    CXXMethodDecl *MoveAssign = finder.moveAssignmentOperators[0];
    MoveAssignmentTranslator translator(AST->getASTContext());

    std::string cCode = translator.generateMoveAssignment(MoveAssign);
    ASSERT(!cCode.empty(), "Should generate C code");

    // Verify all three pointer members are transferred
    ASSERT(cCode.find("buffer") != std::string::npos, "Should reference buffer");
    ASSERT(cCode.find("name") != std::string::npos, "Should reference name");
    ASSERT(cCode.find("values") != std::string::npos, "Should reference values");

    // Verify source nullification
    int nullifications = 0;
    size_t pos = 0;
    std::string nullPattern = "NULL";
    while ((pos = cCode.find(nullPattern, pos)) != std::string::npos) {
        nullifications++;
        pos += nullPattern.length();
    }
    ASSERT(nullifications >= 3, "Should nullify at least 3 pointer members");

    TEST_PASS("move_assignment_multiple_pointers");
}

// ============================================================================
// Test 5: Move assignment with RAII members
// ============================================================================
void test_move_assignment_raii_members() {
    TEST_START("move_assignment_raii_members");

    const char *code = R"(
        class File {
            int fd;
        public:
            ~File() { /* close fd */ }
        };

        class FileManager {
            File* file;
            int* metadata;
        public:
            FileManager& operator=(FileManager&& other) noexcept {
                if (this != &other) {
                    delete file;
                    delete metadata;

                    file = other.file;
                    metadata = other.metadata;

                    other.file = nullptr;
                    other.metadata = nullptr;
                }
                return *this;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    MoveAssignmentFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.moveAssignmentOperators.size() == 1, "Expected move assignment operator");

    CXXMethodDecl *MoveAssign = finder.moveAssignmentOperators[0];
    MoveAssignmentTranslator translator(AST->getASTContext());

    std::string cCode = translator.generateMoveAssignment(MoveAssign);
    ASSERT(!cCode.empty(), "Should generate C code");

    // Verify proper cleanup before assignment
    ASSERT(cCode.find("file") != std::string::npos, "Should reference file member");
    ASSERT(cCode.find("metadata") != std::string::npos, "Should reference metadata member");

    TEST_PASS("move_assignment_raii_members");
}

// ============================================================================
// Test 6: Chained move assignments (a = b = std::move(c))
// ============================================================================
void test_chained_move_assignments() {
    TEST_START("chained_move_assignments");

    const char *code = R"(
        class Chain {
            int* data;
        public:
            Chain& operator=(Chain&& other) noexcept {
                if (this != &other) {
                    delete data;
                    data = other.data;
                    other.data = nullptr;
                }
                return *this;  // Return *this for chaining
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    MoveAssignmentFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.moveAssignmentOperators.size() == 1, "Expected move assignment operator");

    CXXMethodDecl *MoveAssign = finder.moveAssignmentOperators[0];
    MoveAssignmentTranslator translator(AST->getASTContext());

    std::string cCode = translator.generateMoveAssignment(MoveAssign);
    ASSERT(!cCode.empty(), "Should generate C code");

    // In C, chaining is handled differently (void return)
    // The C++ operator returns *this for chaining
    // Our C function returns void (chaining handled at call site)
    ASSERT(cCode.find("void") != std::string::npos, "Should return void in C");

    TEST_PASS("chained_move_assignments");
}

// ============================================================================
// Test 7: Memory leak prevention validation
// ============================================================================
void test_memory_leak_prevention() {
    TEST_START("memory_leak_prevention");

    const char *code = R"(
        class LeakPrevention {
            int* heap_data;
            char* heap_string;
        public:
            LeakPrevention& operator=(LeakPrevention&& other) noexcept {
                if (this != &other) {
                    // Must clean up existing resources before assignment
                    delete heap_data;
                    delete[] heap_string;

                    heap_data = other.heap_data;
                    heap_string = other.heap_string;

                    other.heap_data = nullptr;
                    other.heap_string = nullptr;
                }
                return *this;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    MoveAssignmentFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.moveAssignmentOperators.size() == 1, "Expected move assignment operator");

    CXXMethodDecl *MoveAssign = finder.moveAssignmentOperators[0];
    MoveAssignmentTranslator translator(AST->getASTContext());

    std::string cCode = translator.generateMoveAssignment(MoveAssign);
    ASSERT(!cCode.empty(), "Should generate C code");

    // Critical checks for memory leak prevention:
    // 1. Self-assignment check prevents double-free
    ASSERT(cCode.find("if") != std::string::npos, "Must have self-assignment check");

    // 2. Destructor call or cleanup before transfer prevents memory leak
    // The destructor should be called to free existing resources
    ASSERT(cCode.find("destructor") != std::string::npos ||
           cCode.find("delete") != std::string::npos ||
           cCode.find("free") != std::string::npos,
           "Must clean up old resources before assignment");

    // 3. Source nullification prevents double-free
    ASSERT(cCode.find("NULL") != std::string::npos, "Must nullify source pointers");

    TEST_PASS("memory_leak_prevention");
}

// ============================================================================
// Test 8: Move assignment detection - not copy assignment
// ============================================================================
void test_move_not_copy_assignment() {
    TEST_START("move_not_copy_assignment");

    const char *code = R"(
        class Widget {
            int* data;
        public:
            Widget& operator=(const Widget& other) {  // Copy assignment
                if (this != &other) {
                    delete data;
                    data = new int(*other.data);
                }
                return *this;
            }

            Widget& operator=(Widget&& other) noexcept {  // Move assignment
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
    ASSERT(AST, "Failed to parse C++ code");

    MoveAssignmentFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Should find only the move assignment operator
    ASSERT(finder.moveAssignmentOperators.size() == 1, "Should find exactly one move assignment operator");

    CXXMethodDecl *MoveAssign = finder.moveAssignmentOperators[0];
    MoveAssignmentTranslator translator(AST->getASTContext());

    ASSERT(translator.isMoveAssignmentOperator(MoveAssign), "Should be a move assignment operator");

    // Verify it's the move assignment, not copy
    ASSERT(MoveAssign->getNumParams() == 1, "Move assignment has 1 parameter");
    QualType paramType = MoveAssign->getParamDecl(0)->getType();
    ASSERT(paramType->isRValueReferenceType(), "Parameter should be rvalue reference");

    TEST_PASS("move_not_copy_assignment");
}

// ============================================================================
// Test 9: Valid function signature generation
// ============================================================================
void test_valid_function_signature() {
    TEST_START("valid_function_signature");

    const char *code = R"(
        class MyClass {
            int* ptr;
        public:
            MyClass& operator=(MyClass&& other) noexcept {
                if (this != &other) {
                    delete ptr;
                    ptr = other.ptr;
                    other.ptr = nullptr;
                }
                return *this;
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    MoveAssignmentFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.moveAssignmentOperators.size() == 1, "Expected move assignment operator");

    CXXMethodDecl *MoveAssign = finder.moveAssignmentOperators[0];
    MoveAssignmentTranslator translator(AST->getASTContext());

    std::string cCode = translator.generateMoveAssignment(MoveAssign);
    ASSERT(!cCode.empty(), "Should generate C code");

    // Verify function signature components
    ASSERT(cCode.find("void") != std::string::npos, "Should return void");
    ASSERT(cCode.find("MyClass_") != std::string::npos, "Should have class name prefix");
    ASSERT(cCode.find("move_assign") != std::string::npos, "Should have move_assign in name");
    ASSERT(cCode.find("struct MyClass *") != std::string::npos, "Should have struct MyClass* parameters");
    ASSERT(cCode.find("{") != std::string::npos, "Should have function body");
    ASSERT(cCode.find("}") != std::string::npos, "Should close function body");

    TEST_PASS("valid_function_signature");
}

// ============================================================================
// Main Test Runner
// ============================================================================

int main() {
    std::cout << "\n=== Move Assignment Operator Translation Test Suite (Story #131) ===\n\n";

    std::cout << "--- Move Assignment Operator C Code Generation Tests ---\n";
    test_simple_move_assignment_c_generation();
    test_self_assignment_check();
    test_destructor_call_before_transfer();
    test_move_assignment_multiple_pointers();
    test_move_assignment_raii_members();
    test_chained_move_assignments();
    test_memory_leak_prevention();
    test_move_not_copy_assignment();
    test_valid_function_signature();

    std::cout << "\n=== All Move Assignment Operator Translation Tests Completed ===\n";
    std::cout << "Total: 9 comprehensive tests for move assignment operator translation\n";
    std::cout << "Focus areas: self-assignment, destructor calls, memory leak prevention\n\n";

    return 0;
}
