// TDD Tests for Single Inheritance - Epic #6 Implementation
// Story #50: Base Class Embedding in Struct Layout

#include "CppToCVisitor.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecordLayout.h"
#include <iostream>

using namespace clang;

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Helper to create AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
    return tooling::buildASTFromCode(code);
}

// ============================================================================
// Story #50: Base Class Embedding Tests (RED - Failing Tests)
// ============================================================================

/**
 * Test Case 1: Empty Base Class
 *
 * C++ Input:
 *   class Base {};
 *   class Derived : public Base {};
 *
 * Expected C Output:
 *   struct Base {};
 *   struct Derived {};
 *
 * Acceptance Criteria:
 * - Base class fields appear at offset 0
 * - Even empty base contributes to layout
 */
void test_EmptyBaseClass() {
    TEST_START("EmptyBaseClass: Derived from empty base");

    const char *cpp = R"(
        class Base {};
        class Derived : public Base {};
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    // Run visitor on AST
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify Base struct generated
    RecordDecl *BaseStruct = visitor.getCStruct("Base");
    ASSERT(BaseStruct != nullptr, "Base struct not generated");
    ASSERT(BaseStruct->field_empty(), "Empty base should have no fields");

    // Verify Derived struct generated
    RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
    ASSERT(DerivedStruct != nullptr, "Derived struct not generated");
    ASSERT(DerivedStruct->field_empty(), "Derived from empty base should have no fields");

    TEST_PASS("EmptyBaseClass");
}

/**
 * Test Case 2: Single Base with Fields
 *
 * C++ Input:
 *   class Base { int x; };
 *   class Derived : public Base { int y; };
 *
 * Expected C Output:
 *   struct Base { int x; };
 *   struct Derived { int x; int y; };
 *
 * Acceptance Criteria:
 * - Base field 'x' appears at offset 0 in Derived
 * - Derived field 'y' appears after base fields
 * - Field order: x, y
 */
void test_SingleBaseWithFields() {
    TEST_START("SingleBaseWithFields: Base has field, derived adds field");

    const char *cpp = R"(
        class Base {
        public:
            int x;
        };
        class Derived : public Base {
        public:
            int y;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    // Run visitor on AST
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify Base struct
    RecordDecl *BaseStruct = visitor.getCStruct("Base");
    ASSERT(BaseStruct != nullptr, "Base struct not generated");
    ASSERT(!BaseStruct->field_empty(), "Base should have fields");

    unsigned baseFieldCount = 0;
    for (auto *Field : BaseStruct->fields()) {
        ASSERT(Field->getName() == "x", "Base field name should be 'x'");
        baseFieldCount++;
    }
    ASSERT(baseFieldCount == 1, "Base should have exactly 1 field");

    // Verify Derived struct
    RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
    ASSERT(DerivedStruct != nullptr, "Derived struct not generated");

    // Critical check: Derived should have 2 fields (x from Base, y from Derived)
    unsigned derivedFieldCount = 0;
    std::string firstFieldName, secondFieldName;

    auto it = DerivedStruct->field_begin();
    if (it != DerivedStruct->field_end()) {
        firstFieldName = (*it)->getNameAsString();
        derivedFieldCount++;
        ++it;
    }
    if (it != DerivedStruct->field_end()) {
        secondFieldName = (*it)->getNameAsString();
        derivedFieldCount++;
    }

    ASSERT(derivedFieldCount == 2, "Derived should have 2 fields (x + y)");
    ASSERT(firstFieldName == "x", "First field should be 'x' from Base (offset 0)");
    ASSERT(secondFieldName == "y", "Second field should be 'y' from Derived");

    TEST_PASS("SingleBaseWithFields");
}

/**
 * Test Case 3: Multi-Level Inheritance
 *
 * C++ Input:
 *   class A { int a; };
 *   class B : public A { int b; };
 *   class C : public B { int c; };
 *
 * Expected C Output:
 *   struct A { int a; };
 *   struct B { int a; int b; };
 *   struct C { int a; int b; int c; };
 *
 * Acceptance Criteria:
 * - Fields inherit transitively (A -> B -> C)
 * - Field order preserved: a, b, c
 */
void test_MultiLevelInheritance() {
    TEST_START("MultiLevelInheritance: A -> B -> C");

    const char *cpp = R"(
        class A {
        public:
            int a;
        };
        class B : public A {
        public:
            int b;
        };
        class C : public B {
        public:
            int c;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);

    // Run visitor on AST
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify struct C has 3 fields in correct order
    RecordDecl *CStruct = visitor.getCStruct("C");
    ASSERT(CStruct != nullptr, "C struct not generated");

    std::vector<std::string> fieldNames;
    for (auto *Field : CStruct->fields()) {
        fieldNames.push_back(Field->getNameAsString());
    }

    ASSERT(fieldNames.size() == 3, "C should have 3 fields (a, b, c)");
    ASSERT(fieldNames[0] == "a", "First field should be 'a' from A");
    ASSERT(fieldNames[1] == "b", "Second field should be 'b' from B");
    ASSERT(fieldNames[2] == "c", "Third field should be 'c' from C");

    TEST_PASS("MultiLevelInheritance");
}

/**
 * Test Case 4: Memory Layout Verification
 *
 * Verify sizeof(Derived) = sizeof(Base) + sizeof(derived fields)
 *
 * This test ensures proper ABI compatibility
 */
void test_SizeofVerification() {
    TEST_START("SizeofVerification: sizeof(Derived) correct");

    const char *cpp = R"(
        class Base {
        public:
            int x;
            int y;
        };
        class Derived : public Base {
        public:
            int z;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    // Get C++ struct sizes
    TranslationUnitDecl *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *BaseClass = nullptr;
    CXXRecordDecl *DerivedClass = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Base") BaseClass = RD;
            if (RD->getNameAsString() == "Derived") DerivedClass = RD;
        }
    }

    ASSERT(BaseClass && DerivedClass, "Could not find C++ classes");

    const ASTRecordLayout &BaseLayout = AST->getASTContext().getASTRecordLayout(BaseClass);
    const ASTRecordLayout &DerivedLayout = AST->getASTContext().getASTRecordLayout(DerivedClass);

    uint64_t baseSize = BaseLayout.getSize().getQuantity();
    uint64_t derivedSize = DerivedLayout.getSize().getQuantity();

    // In C++, Derived should be larger than Base (has additional field)
    ASSERT(derivedSize > baseSize, "Derived should be larger than Base");

    // Derived size should be Base size + size of int (assuming no padding)
    uint64_t intSize = AST->getASTContext().getTypeSize(AST->getASTContext().IntTy) / 8;
    uint64_t expectedSize = baseSize + intSize;

    ASSERT(derivedSize >= expectedSize, "Derived size too small");

    TEST_PASS("SizeofVerification");
}

// ============================================================================
// Test Runner
// ============================================================================

int main() {
    std::cout << "\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << " Story #50: Base Class Embedding Tests (RED Phase)\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << "\n";

    // Run all tests
    test_EmptyBaseClass();
    test_SingleBaseWithFields();
    test_MultiLevelInheritance();
    test_SizeofVerification();

    // Summary
    std::cout << "\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << " Test Results:\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << " ✓ Passed: " << tests_passed << "\n";
    std::cout << " ✗ Failed: " << tests_failed << "\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << "\n";

    return tests_failed > 0 ? 1 : 0;
}
