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
// Story #51: Constructor Chaining Tests (RED - Failing Tests)
// ============================================================================

/**
 * Test Case 5: Simple Constructor Chaining
 *
 * C++ Input:
 *   class Base {
 *   public:
 *       int x;
 *       Base(int x) : x(x) {}
 *   };
 *   class Derived : public Base {
 *   public:
 *       int y;
 *       Derived(int x, int y) : Base(x), y(y) {}
 *   };
 *
 * Expected C Output:
 *   void Derived__ctor(struct Derived *this, int x, int y) {
 *       Base__ctor((struct Base*)this, x);  // Base ctor called first
 *       this->y = y;
 *   }
 *
 * Acceptance Criteria:
 * - Base constructor call appears in derived constructor
 * - Base constructor call is BEFORE derived member initialization
 * - Base constructor receives correct arguments from member init list
 */
void test_SimpleConstructorChaining() {
    TEST_START("SimpleConstructorChaining: Base ctor called before derived");

    const char *cpp = R"(
        class Base {
        public:
            int x;
            Base(int x) : x(x) {}
        };
        class Derived : public Base {
        public:
            int y;
            Derived(int x, int y) : Base(x), y(y) {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get generated C constructor for Derived
    FunctionDecl *DerivedCtor = visitor.getCtor("Derived__ctor");
    ASSERT(DerivedCtor != nullptr, "Derived constructor not generated");

    // Constructor should have a body
    ASSERT(DerivedCtor->hasBody(), "Derived constructor has no body");

    CompoundStmt *Body = dyn_cast<CompoundStmt>(DerivedCtor->getBody());
    ASSERT(Body != nullptr, "Derived constructor body is not a CompoundStmt");

    // Body should have at least 2 statements:
    // 1. Base constructor call
    // 2. Derived member initialization
    ASSERT(Body->size() >= 2, "Derived constructor should have >= 2 statements");

    // First statement should be a call to Base__ctor
    Stmt *FirstStmt = *Body->body_begin();
    CallExpr *BaseCtorCall = dyn_cast<CallExpr>(FirstStmt);
    ASSERT(BaseCtorCall != nullptr, "First statement should be a CallExpr (Base ctor call)");

    // Verify the call is to Base__ctor
    if (FunctionDecl *Callee = BaseCtorCall->getDirectCallee()) {
        std::string calleeName = Callee->getNameAsString();
        ASSERT(calleeName == "Base__ctor", "First call should be to Base__ctor");
    }

    TEST_PASS("SimpleConstructorChaining");
}

/**
 * Test Case 6: Constructor Chaining with Member Init List
 *
 * C++ Input:
 *   class Base {
 *   public:
 *       Base(int x, int y) {}
 *   };
 *   class Derived : public Base {
 *   public:
 *       int z;
 *       Derived(int a, int b, int c) : Base(a, b), z(c) {}
 *   };
 *
 * Expected C Output:
 *   void Derived__ctor(struct Derived *this, int a, int b, int c) {
 *       Base__ctor((struct Base*)this, a, b);  // Pass correct args
 *       this->z = c;
 *   }
 *
 * Acceptance Criteria:
 * - Base constructor receives arguments from member init list
 * - Correct number of arguments passed
 * - Arguments in correct order
 */
void test_ConstructorChainingWithArgs() {
    TEST_START("ConstructorChainingWithArgs: Base ctor gets correct args");

    const char *cpp = R"(
        class Base {
        public:
            Base(int x, int y) {}
        };
        class Derived : public Base {
        public:
            int z;
            Derived(int a, int b, int c) : Base(a, b), z(c) {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *DerivedCtor = visitor.getCtor("Derived__ctor");
    ASSERT(DerivedCtor != nullptr, "Derived constructor not generated");

    CompoundStmt *Body = dyn_cast<CompoundStmt>(DerivedCtor->getBody());
    ASSERT(Body != nullptr, "Derived constructor has no body");

    // First statement should be Base__ctor call
    Stmt *FirstStmt = *Body->body_begin();
    CallExpr *BaseCtorCall = dyn_cast<CallExpr>(FirstStmt);
    ASSERT(BaseCtorCall != nullptr, "First statement should be Base ctor call");

    // Base__ctor should receive 3 arguments: this, a, b
    unsigned numArgs = BaseCtorCall->getNumArgs();
    ASSERT(numArgs == 3, "Base__ctor should receive 3 arguments (this, a, b)");

    TEST_PASS("ConstructorChainingWithArgs");
}

/**
 * Test Case 7: Multi-Level Constructor Chaining
 *
 * C++ Input:
 *   class Base { Base() {} };
 *   class Derived1 : public Base { Derived1() : Base() {} };
 *   class Derived2 : public Derived1 { Derived2() : Derived1() {} };
 *
 * Expected C Output:
 *   void Derived1__ctor(struct Derived1 *this) {
 *       Base__ctor((struct Base*)this);
 *   }
 *   void Derived2__ctor(struct Derived2 *this) {
 *       Derived1__ctor((struct Derived1*)this);
 *   }
 *
 * Acceptance Criteria:
 * - Derived2 calls Derived1 constructor (not Base directly)
 * - Constructor chain flows: Derived2 → Derived1 → Base
 */
void test_MultiLevelConstructorChaining() {
    TEST_START("MultiLevelConstructorChaining: 3-level inheritance chain");

    const char *cpp = R"(
        class Base {
        public:
            Base() {}
        };
        class Derived1 : public Base {
        public:
            Derived1() : Base() {}
        };
        class Derived2 : public Derived1 {
        public:
            Derived2() : Derived1() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Check Derived2 constructor calls Derived1 constructor (not Base)
    FunctionDecl *Derived2Ctor = visitor.getCtor("Derived2__ctor");
    ASSERT(Derived2Ctor != nullptr, "Derived2 constructor not generated");

    CompoundStmt *Body = dyn_cast<CompoundStmt>(Derived2Ctor->getBody());
    ASSERT(Body != nullptr && Body->size() >= 1, "Derived2 constructor should have body");

    Stmt *FirstStmt = *Body->body_begin();
    CallExpr *ParentCtorCall = dyn_cast<CallExpr>(FirstStmt);
    ASSERT(ParentCtorCall != nullptr, "First statement should be parent ctor call");

    // Verify it calls Derived1__ctor (not Base__ctor)
    if (FunctionDecl *Callee = ParentCtorCall->getDirectCallee()) {
        std::string calleeName = Callee->getNameAsString();
        ASSERT(calleeName == "Derived1__ctor",
               "Derived2 should call Derived1__ctor (not Base__ctor)");
    }

    TEST_PASS("MultiLevelConstructorChaining");
}

// ============================================================================
// Story #52: Destructor Chaining Tests (RED - Failing Tests)
// ============================================================================

/**
 * Test Case 8: Simple Destructor Chaining
 *
 * C++ Input:
 *   class Base {
 *   public:
 *       ~Base() {}
 *   };
 *   class Derived : public Base {
 *   public:
 *       ~Derived() {}
 *   };
 *
 * Expected C Output:
 *   void Derived__dtor(struct Derived *this) {
 *       // Derived destructor body (if any)
 *       Base__dtor((struct Base*)this);  // Base dtor called AFTER derived
 *   }
 *
 * Acceptance Criteria:
 * - Base destructor call appears in derived destructor
 * - Base destructor call is AFTER derived destructor body
 * - Destruction order is reverse of construction
 */
void test_SimpleDestructorChaining() {
    TEST_START("SimpleDestructorChaining: Base dtor called after derived");

    const char *cpp = R"(
        class Base {
        public:
            ~Base() {}
        };
        class Derived : public Base {
        public:
            ~Derived() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get generated C destructor for Derived
    FunctionDecl *DerivedDtor = visitor.getDtor("Derived__dtor");
    ASSERT(DerivedDtor != nullptr, "Derived destructor not generated");

    // Destructor should have a body
    ASSERT(DerivedDtor->hasBody(), "Derived destructor has no body");

    CompoundStmt *Body = dyn_cast<CompoundStmt>(DerivedDtor->getBody());
    ASSERT(Body != nullptr, "Derived destructor body is not a CompoundStmt");

    // Body should have at least 1 statement: Base destructor call
    ASSERT(Body->size() >= 1, "Derived destructor should have >= 1 statement");

    // Last statement should be a call to Base__dtor
    Stmt *LastStmt = *(Body->body_end() - 1);
    CallExpr *BaseDtorCall = dyn_cast<CallExpr>(LastStmt);
    ASSERT(BaseDtorCall != nullptr, "Last statement should be a CallExpr (Base dtor call)");

    // Verify the call is to Base__dtor
    if (FunctionDecl *Callee = BaseDtorCall->getDirectCallee()) {
        std::string calleeName = Callee->getNameAsString();
        ASSERT(calleeName == "Base__dtor", "Last call should be to Base__dtor");
    }

    TEST_PASS("SimpleDestructorChaining");
}

/**
 * Test Case 9: Destructor Chaining with Body
 *
 * C++ Input:
 *   class Base {
 *   public:
 *       int x;
 *       ~Base() { x = 0; }
 *   };
 *   class Derived : public Base {
 *   public:
 *       int y;
 *       ~Derived() { y = 0; }
 *   };
 *
 * Expected C Output:
 *   void Derived__dtor(struct Derived *this) {
 *       this->y = 0;                     // Derived dtor body FIRST
 *       Base__dtor((struct Base*)this);  // Base dtor AFTER
 *   }
 *
 * Acceptance Criteria:
 * - Derived destructor body executes first
 * - Base destructor called after derived body
 * - Order: Derived cleanup → Base cleanup
 */
void test_DestructorChainingWithBody() {
    TEST_START("DestructorChainingWithBody: Derived body then base dtor");

    const char *cpp = R"(
        class Base {
        public:
            int x;
            ~Base() { x = 0; }
        };
        class Derived : public Base {
        public:
            int y;
            ~Derived() { y = 0; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *DerivedDtor = visitor.getDtor("Derived__dtor");
    ASSERT(DerivedDtor != nullptr, "Derived destructor not generated");

    CompoundStmt *Body = dyn_cast<CompoundStmt>(DerivedDtor->getBody());
    ASSERT(Body != nullptr && Body->size() >= 2, "Derived destructor should have >= 2 statements");

    // Last statement should be Base__dtor call
    Stmt *LastStmt = *(Body->body_end() - 1);
    CallExpr *BaseDtorCall = dyn_cast<CallExpr>(LastStmt);
    ASSERT(BaseDtorCall != nullptr, "Last statement should be Base dtor call");

    if (FunctionDecl *Callee = BaseDtorCall->getDirectCallee()) {
        std::string calleeName = Callee->getNameAsString();
        ASSERT(calleeName == "Base__dtor", "Last call should be to Base__dtor");
    }

    TEST_PASS("DestructorChainingWithBody");
}

/**
 * Test Case 10: Multi-Level Destructor Chaining
 *
 * C++ Input:
 *   class Base { ~Base() {} };
 *   class Derived1 : public Base { ~Derived1() {} };
 *   class Derived2 : public Derived1 { ~Derived2() {} };
 *
 * Expected C Output:
 *   void Derived2__dtor(struct Derived2 *this) {
 *       // Derived2 body (if any)
 *       Derived1__dtor((struct Derived1*)this);  // NOT Base__dtor
 *   }
 *   void Derived1__dtor(struct Derived1 *this) {
 *       // Derived1 body (if any)
 *       Base__dtor((struct Base*)this);
 *   }
 *
 * Acceptance Criteria:
 * - Derived2 calls Derived1 destructor (not Base directly)
 * - Destruction chain flows: Derived2 → Derived1 → Base
 * - Mirror of construction order (reverse)
 */
void test_MultiLevelDestructorChaining() {
    TEST_START("MultiLevelDestructorChaining: 3-level inheritance chain");

    const char *cpp = R"(
        class Base {
        public:
            ~Base() {}
        };
        class Derived1 : public Base {
        public:
            ~Derived1() {}
        };
        class Derived2 : public Derived1 {
        public:
            ~Derived2() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Check Derived2 destructor calls Derived1 destructor (not Base)
    FunctionDecl *Derived2Dtor = visitor.getDtor("Derived2__dtor");
    ASSERT(Derived2Dtor != nullptr, "Derived2 destructor not generated");

    CompoundStmt *Body = dyn_cast<CompoundStmt>(Derived2Dtor->getBody());
    ASSERT(Body != nullptr && Body->size() >= 1, "Derived2 destructor should have body");

    // Last statement should be parent dtor call
    Stmt *LastStmt = *(Body->body_end() - 1);
    CallExpr *ParentDtorCall = dyn_cast<CallExpr>(LastStmt);
    ASSERT(ParentDtorCall != nullptr, "Last statement should be parent dtor call");

    // Verify it calls Derived1__dtor (not Base__dtor)
    if (FunctionDecl *Callee = ParentDtorCall->getDirectCallee()) {
        std::string calleeName = Callee->getNameAsString();
        ASSERT(calleeName == "Derived1__dtor",
               "Derived2 should call Derived1__dtor (not Base__dtor)");
    }

    TEST_PASS("MultiLevelDestructorChaining");
}

// ============================================================================
// Story #53: Member Access Through Inheritance Tests
// ============================================================================

/**
 * Test Case 11: Member Access in Derived Methods
 *
 * Verify that derived class methods can access base class members
 * through the embedded base fields (from Story #50).
 */
void test_MemberAccessInDerivedMethods() {
    TEST_START("MemberAccessInDerivedMethods: Derived accesses base fields");

    const char *cpp = R"(
        class Base {
        public:
            int x;
            Base(int val) : x(val) {}
        };
        class Derived : public Base {
        public:
            int y;
            Derived(int a, int b) : Base(a), y(b) {}
            int sum() { return x + y; }  // Access base member x
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT(AST, "Failed to parse C++ code");

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify Derived struct has both x and y fields
    RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
    ASSERT(DerivedStruct != nullptr, "Derived struct not generated");

    unsigned fieldCount = 0;
    for (auto *F : DerivedStruct->fields()) {
        fieldCount++;
    }
    ASSERT(fieldCount == 2, "Derived should have 2 fields (x from Base, y from Derived)");

    TEST_PASS("MemberAccessInDerivedMethods");
}

// ============================================================================
// Test Runner
// ============================================================================

int main() {
    std::cout << "\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << " Story #50: Base Class Embedding Tests\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << "\n";

    // Run Story #50 tests
    test_EmptyBaseClass();
    test_SingleBaseWithFields();
    test_MultiLevelInheritance();
    test_SizeofVerification();

    std::cout << "\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << " Story #51: Constructor Chaining Tests\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << "\n";

    // Run Story #51 tests
    test_SimpleConstructorChaining();
    test_ConstructorChainingWithArgs();
    test_MultiLevelConstructorChaining();

    std::cout << "\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << " Story #52: Destructor Chaining Tests (RED Phase)\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << "\n";

    // Run Story #52 tests
    test_SimpleDestructorChaining();
    test_DestructorChainingWithBody();
    test_MultiLevelDestructorChaining();

    std::cout << "\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << " Story #53: Member Access Tests\n";
    std::cout << "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━\n";
    std::cout << "\n";

    // Run Story #53 tests
    test_MemberAccessInDerivedMethods();

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
