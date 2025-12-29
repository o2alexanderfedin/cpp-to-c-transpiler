// tests/InheritanceTest_GTest.cpp
// Migrated from InheritanceTest.cpp to Google Test framework
// TDD Tests for Single Inheritance - Epic #6 Implementation
// Story #50-#64: Base Class Embedding, Constructor/Destructor Chaining,
//                Member Access, Upcasting, Method Overriding, and more

#include <gtest/gtest.h>
#include "CppToCVisitor.h"
#include "CNodeBuilder.h"
#include "FileOriginTracker.h"
#include <clang/AST/ASTContext.h>
#include <clang/AST/RecordLayout.h>
#include <clang/AST/Decl.h>
#include <clang/AST/Stmt.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include <memory>
#include <string>
#include <vector>

using namespace clang;

// ============================================================================
// Test Fixture
// ============================================================================

class InheritanceTestFixture : public ::testing::Test {
protected:
    // Helper to create AST from C++ code
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        std::vector<std::string> args = {"-std=c++17", "-xc++"};
        return tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
    }

    // Helper to find a CXXRecordDecl by name
    CXXRecordDecl* findCXXRecord(ASTContext &Ctx, const std::string &name) {
        for (auto *D : Ctx.getTranslationUnitDecl()->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == name) {
                    return RD;
                }
            }
        }
        return nullptr;
    }
};

// ============================================================================
// Story #50: Base Class Embedding Tests
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
TEST_F(InheritanceTestFixture, EmptyBaseClass) {
    const char *cpp = R"(
        class Base {};
        class Derived : public Base {};
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify Base struct generated
    RecordDecl *BaseStruct = visitor.getCStruct("Base");
    ASSERT_NE(BaseStruct, nullptr) << "Base struct not generated";
    EXPECT_TRUE(BaseStruct->field_empty()) << "Empty base should have no fields";

    // Verify Derived struct generated
    RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
    ASSERT_NE(DerivedStruct, nullptr) << "Derived struct not generated";
    EXPECT_TRUE(DerivedStruct->field_empty()) << "Derived from empty base should have no fields";
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
TEST_F(InheritanceTestFixture, SingleBaseWithFields) {
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
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify Base struct
    RecordDecl *BaseStruct = visitor.getCStruct("Base");
    ASSERT_NE(BaseStruct, nullptr) << "Base struct not generated";
    EXPECT_FALSE(BaseStruct->field_empty()) << "Base should have fields";

    unsigned baseFieldCount = 0;
    for (auto *Field : BaseStruct->fields()) {
        EXPECT_EQ(Field->getName(), "x") << "Base field name should be 'x'";
        baseFieldCount++;
    }
    EXPECT_EQ(baseFieldCount, 1u) << "Base should have exactly 1 field";

    // Verify Derived struct
    RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
    ASSERT_NE(DerivedStruct, nullptr) << "Derived struct not generated";

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

    EXPECT_EQ(derivedFieldCount, 2u) << "Derived should have 2 fields (x + y)";
    EXPECT_EQ(firstFieldName, "x") << "First field should be 'x' from Base (offset 0)";
    EXPECT_EQ(secondFieldName, "y") << "Second field should be 'y' from Derived";
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
TEST_F(InheritanceTestFixture, MultiLevelInheritance) {
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
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify struct C has 3 fields in correct order
    RecordDecl *CStruct = visitor.getCStruct("C");
    ASSERT_NE(CStruct, nullptr) << "C struct not generated";

    std::vector<std::string> fieldNames;
    for (auto *Field : CStruct->fields()) {
        fieldNames.push_back(Field->getNameAsString());
    }

    EXPECT_EQ(fieldNames.size(), 3u) << "C should have 3 fields (a, b, c)";
    EXPECT_EQ(fieldNames[0], "a") << "First field should be 'a' from A";
    EXPECT_EQ(fieldNames[1], "b") << "Second field should be 'b' from B";
    EXPECT_EQ(fieldNames[2], "c") << "Third field should be 'c' from C";
}

/**
 * Test Case 4: Memory Layout Verification
 *
 * Verify sizeof(Derived) = sizeof(Base) + sizeof(derived fields)
 * This test ensures proper ABI compatibility
 */
TEST_F(InheritanceTestFixture, SizeofVerification) {
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
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Get C++ struct sizes
    CXXRecordDecl *BaseClass = findCXXRecord(AST->getASTContext(), "Base");
    CXXRecordDecl *DerivedClass = findCXXRecord(AST->getASTContext(), "Derived");

    ASSERT_NE(BaseClass, nullptr) << "Could not find Base class";
    ASSERT_NE(DerivedClass, nullptr) << "Could not find Derived class";

    const ASTRecordLayout &BaseLayout = AST->getASTContext().getASTRecordLayout(BaseClass);
    const ASTRecordLayout &DerivedLayout = AST->getASTContext().getASTRecordLayout(DerivedClass);

    uint64_t baseSize = BaseLayout.getSize().getQuantity();
    uint64_t derivedSize = DerivedLayout.getSize().getQuantity();

    // In C++, Derived should be larger than Base (has additional field)
    EXPECT_GT(derivedSize, baseSize) << "Derived should be larger than Base";

    // Derived size should be Base size + size of int (assuming no padding)
    uint64_t intSize = AST->getASTContext().getTypeSize(AST->getASTContext().IntTy) / 8;
    uint64_t expectedSize = baseSize + intSize;

    EXPECT_GE(derivedSize, expectedSize) << "Derived size too small";
}

// ============================================================================
// Story #51: Constructor Chaining Tests
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
TEST_F(InheritanceTestFixture, SimpleConstructorChaining) {
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
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get generated C constructor for Derived
    FunctionDecl *DerivedCtor = visitor.getCtor("Derived__ctor");
    ASSERT_NE(DerivedCtor, nullptr) << "Derived constructor not generated";
    ASSERT_TRUE(DerivedCtor->hasBody()) << "Derived constructor has no body";

    CompoundStmt *Body = dyn_cast<CompoundStmt>(DerivedCtor->getBody());
    ASSERT_NE(Body, nullptr) << "Derived constructor body is not a CompoundStmt";

    // Body should have at least 2 statements:
    // 1. Base constructor call
    // 2. Derived member initialization
    EXPECT_GE(Body->size(), 2u) << "Derived constructor should have >= 2 statements";

    // First statement should be a call to Base__ctor
    Stmt *FirstStmt = *Body->body_begin();
    CallExpr *BaseCtorCall = dyn_cast<CallExpr>(FirstStmt);
    ASSERT_NE(BaseCtorCall, nullptr) << "First statement should be a CallExpr (Base ctor call)";

    // Verify the call is to Base__ctor
    if (FunctionDecl *Callee = BaseCtorCall->getDirectCallee()) {
        std::string calleeName = Callee->getNameAsString();
        EXPECT_EQ(calleeName, "Base__ctor") << "First call should be to Base__ctor";
    }
}

/**
 * Test Case 6: Constructor Chaining with Arguments
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
TEST_F(InheritanceTestFixture, ConstructorChainingWithArgs) {
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
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *DerivedCtor = visitor.getCtor("Derived__ctor");
    ASSERT_NE(DerivedCtor, nullptr) << "Derived constructor not generated";

    CompoundStmt *Body = dyn_cast<CompoundStmt>(DerivedCtor->getBody());
    ASSERT_NE(Body, nullptr) << "Derived constructor has no body";

    // First statement should be Base__ctor call
    Stmt *FirstStmt = *Body->body_begin();
    CallExpr *BaseCtorCall = dyn_cast<CallExpr>(FirstStmt);
    ASSERT_NE(BaseCtorCall, nullptr) << "First statement should be Base ctor call";

    // Base__ctor should receive 3 arguments: this, a, b
    unsigned numArgs = BaseCtorCall->getNumArgs();
    EXPECT_EQ(numArgs, 3u) << "Base__ctor should receive 3 arguments (this, a, b)";
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
TEST_F(InheritanceTestFixture, MultiLevelConstructorChaining) {
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
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Check Derived2 constructor calls Derived1 constructor (not Base)
    FunctionDecl *Derived2Ctor = visitor.getCtor("Derived2__ctor");
    ASSERT_NE(Derived2Ctor, nullptr) << "Derived2 constructor not generated";

    CompoundStmt *Body = dyn_cast<CompoundStmt>(Derived2Ctor->getBody());
    ASSERT_NE(Body, nullptr) << "Derived2 constructor should have body";
    EXPECT_GE(Body->size(), 1u) << "Derived2 constructor should have >= 1 statement";

    Stmt *FirstStmt = *Body->body_begin();
    CallExpr *ParentCtorCall = dyn_cast<CallExpr>(FirstStmt);
    ASSERT_NE(ParentCtorCall, nullptr) << "First statement should be parent ctor call";

    // Verify it calls Derived1__ctor (not Base__ctor)
    if (FunctionDecl *Callee = ParentCtorCall->getDirectCallee()) {
        std::string calleeName = Callee->getNameAsString();
        EXPECT_EQ(calleeName, "Derived1__ctor")
            << "Derived2 should call Derived1__ctor (not Base__ctor)";
    }
}

// ============================================================================
// Story #52: Destructor Chaining Tests
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
TEST_F(InheritanceTestFixture, SimpleDestructorChaining) {
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
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get generated C destructor for Derived
    FunctionDecl *DerivedDtor = visitor.getDtor("Derived__dtor");
    ASSERT_NE(DerivedDtor, nullptr) << "Derived destructor not generated";
    ASSERT_TRUE(DerivedDtor->hasBody()) << "Derived destructor has no body";

    CompoundStmt *Body = dyn_cast<CompoundStmt>(DerivedDtor->getBody());
    ASSERT_NE(Body, nullptr) << "Derived destructor body is not a CompoundStmt";

    // Body should have at least 1 statement: Base destructor call
    EXPECT_GE(Body->size(), 1u) << "Derived destructor should have >= 1 statement";

    // Last statement should be a call to Base__dtor
    Stmt *LastStmt = *(Body->body_end() - 1);
    CallExpr *BaseDtorCall = dyn_cast<CallExpr>(LastStmt);
    ASSERT_NE(BaseDtorCall, nullptr) << "Last statement should be a CallExpr (Base dtor call)";

    // Verify the call is to Base__dtor
    if (FunctionDecl *Callee = BaseDtorCall->getDirectCallee()) {
        std::string calleeName = Callee->getNameAsString();
        EXPECT_EQ(calleeName, "Base__dtor") << "Last call should be to Base__dtor";
    }
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
TEST_F(InheritanceTestFixture, DestructorChainingWithBody) {
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
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *DerivedDtor = visitor.getDtor("Derived__dtor");
    ASSERT_NE(DerivedDtor, nullptr) << "Derived destructor not generated";

    CompoundStmt *Body = dyn_cast<CompoundStmt>(DerivedDtor->getBody());
    ASSERT_NE(Body, nullptr) << "Derived destructor should have body";
    EXPECT_GE(Body->size(), 2u) << "Derived destructor should have >= 2 statements";

    // Last statement should be Base__dtor call
    Stmt *LastStmt = *(Body->body_end() - 1);
    CallExpr *BaseDtorCall = dyn_cast<CallExpr>(LastStmt);
    ASSERT_NE(BaseDtorCall, nullptr) << "Last statement should be Base dtor call";

    if (FunctionDecl *Callee = BaseDtorCall->getDirectCallee()) {
        std::string calleeName = Callee->getNameAsString();
        EXPECT_EQ(calleeName, "Base__dtor") << "Last call should be to Base__dtor";
    }
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
TEST_F(InheritanceTestFixture, MultiLevelDestructorChaining) {
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
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Check Derived2 destructor calls Derived1 destructor (not Base)
    FunctionDecl *Derived2Dtor = visitor.getDtor("Derived2__dtor");
    ASSERT_NE(Derived2Dtor, nullptr) << "Derived2 destructor not generated";

    CompoundStmt *Body = dyn_cast<CompoundStmt>(Derived2Dtor->getBody());
    ASSERT_NE(Body, nullptr) << "Derived2 destructor should have body";
    EXPECT_GE(Body->size(), 1u) << "Derived2 destructor should have >= 1 statement";

    // Last statement should be parent dtor call
    Stmt *LastStmt = *(Body->body_end() - 1);
    CallExpr *ParentDtorCall = dyn_cast<CallExpr>(LastStmt);
    ASSERT_NE(ParentDtorCall, nullptr) << "Last statement should be parent dtor call";

    // Verify it calls Derived1__dtor (not Base__dtor)
    if (FunctionDecl *Callee = ParentDtorCall->getDirectCallee()) {
        std::string calleeName = Callee->getNameAsString();
        EXPECT_EQ(calleeName, "Derived1__dtor")
            << "Derived2 should call Derived1__dtor (not Base__dtor)";
    }
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
TEST_F(InheritanceTestFixture, MemberAccessInDerivedMethods) {
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
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify Derived struct has both x and y fields
    RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
    ASSERT_NE(DerivedStruct, nullptr) << "Derived struct not generated";

    unsigned fieldCount = 0;
    for (auto *F : DerivedStruct->fields()) {
        fieldCount++;
    }
    EXPECT_EQ(fieldCount, 2u) << "Derived should have 2 fields (x from Base, y from Derived)";
}

// ============================================================================
// Story #54: Upcasting Tests
// ============================================================================

/**
 * Test Case 12: Basic Upcasting (Derived* to Base*)
 *
 * Verify that Derived* can be safely cast to Base* due to base fields
 * being embedded at offset 0 in the derived struct (from Story #50).
 *
 * In C, upcasting is implicit: (Base*)&derived works because Base fields
 * are at the beginning of the Derived struct.
 */
TEST_F(InheritanceTestFixture, BasicUpcasting) {
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
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify Base struct exists
    RecordDecl *BaseStruct = visitor.getCStruct("Base");
    ASSERT_NE(BaseStruct, nullptr) << "Base struct not generated";

    // Verify Derived struct exists
    RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
    ASSERT_NE(DerivedStruct, nullptr) << "Derived struct not generated";

    // CRITICAL: Verify field layout - base fields MUST be first for safe upcasting
    auto fields = DerivedStruct->fields();
    auto it = fields.begin();
    ASSERT_NE(it, fields.end()) << "Derived should have fields";

    // First field must be from Base class
    FieldDecl *firstField = *it;
    EXPECT_EQ(firstField->getNameAsString(), "x")
        << "First field must be 'x' from Base (offset 0 = safe upcasting)";

    // Second field should be from Derived class
    ++it;
    ASSERT_NE(it, fields.end()) << "Derived should have second field";
    FieldDecl *secondField = *it;
    EXPECT_EQ(secondField->getNameAsString(), "y")
        << "Second field must be 'y' from Derived";

    // With this layout, (Base*)&derived is safe because:
    // - Base fields are at offset 0
    // - Casting Derived* to Base* gives same address
    // - Base methods can access Base fields correctly
}

/**
 * Test Case 13: Upcasting with Multi-Level Inheritance
 *
 * Verify that upcasting works correctly in multi-level inheritance hierarchies.
 * GrandDerived -> Derived -> Base, where Base fields are at offset 0.
 */
TEST_F(InheritanceTestFixture, MultiLevelUpcasting) {
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
        };
        class GrandDerived : public Derived {
        public:
            int z;
            GrandDerived(int a, int b, int c) : Derived(a, b), z(c) {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify all structs exist
    RecordDecl *BaseStruct = visitor.getCStruct("Base");
    ASSERT_NE(BaseStruct, nullptr) << "Base struct not generated";

    RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
    ASSERT_NE(DerivedStruct, nullptr) << "Derived struct not generated";

    RecordDecl *GrandDerivedStruct = visitor.getCStruct("GrandDerived");
    ASSERT_NE(GrandDerivedStruct, nullptr) << "GrandDerived struct not generated";

    // CRITICAL: Verify GrandDerived has Base fields at offset 0 (for safe upcasting)
    auto fields = GrandDerivedStruct->fields();
    auto it = fields.begin();
    ASSERT_NE(it, fields.end()) << "GrandDerived should have fields";

    // First field must be 'x' from Base (offset 0)
    FieldDecl *firstField = *it;
    EXPECT_EQ(firstField->getNameAsString(), "x")
        << "First field must be 'x' from Base (offset 0 for upcasting)";

    // Second field must be 'y' from Derived
    ++it;
    ASSERT_NE(it, fields.end()) << "GrandDerived should have second field";
    FieldDecl *secondField = *it;
    EXPECT_EQ(secondField->getNameAsString(), "y")
        << "Second field must be 'y' from Derived";

    // Third field must be 'z' from GrandDerived
    ++it;
    ASSERT_NE(it, fields.end()) << "GrandDerived should have third field";
    FieldDecl *thirdField = *it;
    EXPECT_EQ(thirdField->getNameAsString(), "z")
        << "Third field must be 'z' from GrandDerived";

    // With this layout, both upcasts work:
    // - (Derived*)&grandDerived works (offset 0)
    // - (Base*)&grandDerived works (offset 0)
    // - (Base*)&derived works (offset 0)
}
/**
 * Test Case 14: Simple Method Overriding
 *
 * Verify that a derived class can override a base class method
 * and that name mangling creates distinct C functions.
 */
TEST_F(InheritanceTestFixture, SimpleMethodOverriding) {
    const char *cpp = R"(
        class Base {
        public:
            void print() { /* base implementation */ }
        };
        class Derived : public Base {
        public:
            void print() { /* derived implementation - overrides Base::print */ }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify Base::print exists as Base_print
    FunctionDecl *basePrint = visitor.getCFunc("Base_print");
    ASSERT_NE(basePrint, nullptr) << "Base_print function not generated";
    EXPECT_EQ(basePrint->getNumParams(), 1) << "Base_print should have 'this' parameter";

    // Verify Derived::print exists as Derived_print (separate function)
    FunctionDecl *derivedPrint = visitor.getCFunc("Derived_print");
    ASSERT_NE(derivedPrint, nullptr) << "Derived_print function not generated";
    EXPECT_EQ(derivedPrint->getNumParams(), 1) << "Derived_print should have 'this' parameter";

    // Verify they are different functions (name mangling distinguishes them)
    EXPECT_NE(basePrint, derivedPrint) << "Base_print and Derived_print must be distinct functions";

    // Verify parameter types are correct
    ParmVarDecl *baseParam = basePrint->getParamDecl(0);
    QualType baseParamType = baseParam->getType();
    ASSERT_TRUE(baseParamType->isPointerType()) << "Base_print parameter should be pointer";

    ParmVarDecl *derivedParam = derivedPrint->getParamDecl(0);
    QualType derivedParamType = derivedParam->getType();
    ASSERT_TRUE(derivedParamType->isPointerType()) << "Derived_print parameter should be pointer";
}



/**
 * Test Case 15: Method Overriding with Return Value
 *
 * Verify that overridden methods with return values work correctly.
 */
TEST_F(InheritanceTestFixture, MethodOverridingWithReturn) {
    const char *cpp = R"(
        class Animal {
        public:
            int getLegs() { return 4; }  // Default: 4 legs
        };
        class Bird : public Animal {
        public:
            int getLegs() { return 2; }  // Override: birds have 2 legs
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify Animal::getLegs exists
    FunctionDecl *animalGetLegs = visitor.getCFunc("Animal_getLegs");
    ASSERT_NE(animalGetLegs, nullptr) << "Animal_getLegs function not generated";

    // Verify Bird::getLegs exists (separate function)
    FunctionDecl *birdGetLegs = visitor.getCFunc("Bird_getLegs");
    ASSERT_NE(birdGetLegs, nullptr) << "Bird_getLegs function not generated";

    // Verify they are distinct functions
    EXPECT_NE(animalGetLegs, birdGetLegs) << "Animal_getLegs and Bird_getLegs must be distinct";

    // Verify both return int
    QualType animalRetType = animalGetLegs->getReturnType();
    ASSERT_TRUE(animalRetType->isIntegerType()) << "Animal_getLegs should return int";

    QualType birdRetType = birdGetLegs->getReturnType();
    ASSERT_TRUE(birdRetType->isIntegerType()) << "Bird_getLegs should return int";
}



/**
 * Test Case 16: Method Overriding with Parameters
 *
 * Verify that overridden methods with parameters work correctly.
 */
TEST_F(InheritanceTestFixture, MethodOverridingWithParameters) {
    const char *cpp = R"(
        class Shape {
        public:
            void setSize(int s) { /* base implementation */ }
        };
        class Circle : public Shape {
        public:
            void setSize(int s) { /* derived implementation - validates s > 0 */ }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify Shape::setSize exists
    FunctionDecl *shapeSetSize = visitor.getCFunc("Shape_setSize");
    ASSERT_NE(shapeSetSize, nullptr) << "Shape_setSize function not generated";
    EXPECT_EQ(shapeSetSize->getNumParams(), 2) << "Shape_setSize should have 2 parameters (this + s)";

    // Verify Circle::setSize exists
    FunctionDecl *circleSetSize = visitor.getCFunc("Circle_setSize");
    ASSERT_NE(circleSetSize, nullptr) << "Circle_setSize function not generated";
    EXPECT_EQ(circleSetSize->getNumParams(), 2) << "Circle_setSize should have 2 parameters (this + s)";

    // Verify they are distinct
    EXPECT_NE(shapeSetSize, circleSetSize) << "Shape_setSize and Circle_setSize must be distinct";
}



/**
 * Test Case 17: Comprehensive Multi-Level Inheritance Integration
 *
 * Verify that ALL aspects of multi-level inheritance work together:
 * - Memory layout (all ancestor fields in order)
 * - Constructor chaining (all levels)
 * - Destructor chaining (all levels)
 * - Member access (all levels)
 * - Method overriding (all levels)
 * - Upcasting (all levels)
 */
TEST_F(InheritanceTestFixture, ComprehensiveMultiLevelInheritance) {
    const char *cpp = R"(
        class Animal {
        protected:
            int age;
        public:
            Animal(int a) : age(a) {}
            ~Animal() {}
            void speak() { /* animal sound */ }  // Non-virtual for this story
        };

        class Mammal : public Animal {
        protected:
            int furColor;
        public:
            Mammal(int a, int f) : Animal(a), furColor(f) {}
            ~Mammal() {}
            void speak() { /* mammal sound */ }  // Override (non-virtual)
            int getFurColor() { return furColor; }
        };

        class Dog : public Mammal {
            int barkVolume;
        public:
            Dog(int a, int f, int v) : Mammal(a, f), barkVolume(v) {}
            ~Dog() {}
            void speak() { /* bark! */ }  // Override (non-virtual)
            int getAge() { return age; }  // Access grandparent member
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // ========================================================================
    // 1. MEMORY LAYOUT: Verify all ancestor fields embedded in order
    // ========================================================================

    RecordDecl *DogStruct = visitor.getCStruct("Dog");
    ASSERT_NE(DogStruct, nullptr) << "Dog struct not generated";

    auto fields = DogStruct->fields();
    std::vector<std::string> fieldNames;
    for (auto *F : fields) {
        fieldNames.push_back(F->getNameAsString());
    }

    EXPECT_EQ(fieldNames.size(), 3) << "Dog should have 3 fields (age, furColor, barkVolume)";
    EXPECT_EQ(fieldNames[0], "age") << "Field 0 must be 'age' from Animal (grandparent)";
    EXPECT_EQ(fieldNames[1], "furColor") << "Field 1 must be 'furColor' from Mammal (parent)";
    EXPECT_EQ(fieldNames[2], "barkVolume") << "Field 2 must be 'barkVolume' from Dog";

    // ========================================================================
    // 2. CONSTRUCTOR CHAINING: Verify all constructors exist and chain
    // ========================================================================

    FunctionDecl *animalCtor = visitor.getCtor("Animal__ctor");
    ASSERT_NE(animalCtor, nullptr) << "Animal__ctor not generated";
    EXPECT_EQ(animalCtor->getNumParams(), 2) << "Animal__ctor(this, age)";

    FunctionDecl *mammalCtor = visitor.getCtor("Mammal__ctor");
    ASSERT_NE(mammalCtor, nullptr) << "Mammal__ctor not generated";
    EXPECT_EQ(mammalCtor->getNumParams(), 3) << "Mammal__ctor(this, age, furColor)";

    FunctionDecl *dogCtor = visitor.getCtor("Dog__ctor");
    ASSERT_NE(dogCtor, nullptr) << "Dog__ctor not generated";
    EXPECT_EQ(dogCtor->getNumParams(), 4) << "Dog__ctor(this, age, furColor, barkVolume)";

    // ========================================================================
    // 3. DESTRUCTOR CHAINING: Verify all destructors exist
    // ========================================================================

    FunctionDecl *animalDtor = visitor.getDtor("Animal__dtor");
    ASSERT_NE(animalDtor, nullptr) << "Animal__dtor not generated";

    FunctionDecl *mammalDtor = visitor.getDtor("Mammal__dtor");
    ASSERT_NE(mammalDtor, nullptr) << "Mammal__dtor not generated";

    FunctionDecl *dogDtor = visitor.getDtor("Dog__dtor");
    ASSERT_NE(dogDtor, nullptr) << "Dog__dtor not generated";

    // ========================================================================
    // 4. METHOD OVERRIDING: Verify all speak() methods are distinct
    // ========================================================================

    FunctionDecl *animalSpeak = visitor.getCFunc("Animal_speak");
    ASSERT_NE(animalSpeak, nullptr) << "Animal_speak not generated";

    FunctionDecl *mammalSpeak = visitor.getCFunc("Mammal_speak");
    ASSERT_NE(mammalSpeak, nullptr) << "Mammal_speak not generated";

    FunctionDecl *dogSpeak = visitor.getCFunc("Dog_speak");
    ASSERT_NE(dogSpeak, nullptr) << "Dog_speak not generated";

    EXPECT_NE(animalSpeak, mammalSpeak) << "Animal_speak ≠ Mammal_speak";
    EXPECT_NE(mammalSpeak, dogSpeak) << "Mammal_speak ≠ Dog_speak";
    EXPECT_NE(animalSpeak, dogSpeak) << "Animal_speak ≠ Dog_speak";

    // ========================================================================
    // 5. MEMBER ACCESS: Verify Dog can access grandparent members
    // ========================================================================

    FunctionDecl *dogGetAge = visitor.getCFunc("Dog_getAge");
    ASSERT_NE(dogGetAge, nullptr) << "Dog_getAge not generated (accesses grandparent member)";

    // ========================================================================
    // 6. UPCASTING: Verify memory layout allows all upcasts
    // ========================================================================

    // With age at offset 0:
    // - (Mammal*)&dog works (age at offset 0)
    // - (Animal*)&dog works (age at offset 0)
    // - (Animal*)&mammal works (age at offset 0)

    RecordDecl *MammalStruct = visitor.getCStruct("Mammal");
    ASSERT_NE(MammalStruct, nullptr) << "Mammal struct not generated";

    auto mammalFields = MammalStruct->fields();
    auto mammalIt = mammalFields.begin();
    EXPECT_NE(mammalIt, mammalFields.end()) << "Mammal should have fields";
    EXPECT_EQ((*mammalIt)->getNameAsString(), "age") << "Mammal's first field must be 'age' for safe upcasting";
}



/**
 * Test Case 18: Member Init List Declaration Order
 *
 * This test verifies that member initialization lists are translated to C
 * assignments in DECLARATION order, not initializer list order.
 *
 * C++ Semantics: Members are initialized in the order they are DECLARED,
 * regardless of the order they appear in the member initializer list.
 *
 * Bug: Current implementation follows initializer list order (WRONG).
 * Fix: Should follow declaration order (CORRECT).
 */
TEST_F(InheritanceTestFixture, MemberInitListDeclarationOrder) {
    const char *code = R"(
        class Point {
            int x, y, z;  // Declaration order: x, y, z
        public:
            // Initializer list order: z, x, y (DIFFERENT from declaration!)
            Point(int a, int b, int c) : z(c), x(a), y(b) {}
        };
    )";

    // Parse and translate
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get the generated C constructor
    FunctionDecl *ctor = visitor.getCtor("Point__ctor");
    ASSERT_NE(ctor, nullptr) << "Point__ctor not generated";

    // Get constructor body
    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(ctor->getBody());
    ASSERT_NE(body, nullptr) << "Constructor body is null";

    // The body should have 3 assignment statements (one per member)
    std::vector<Stmt*> stmts;
    for (Stmt *S : body->body()) {
        stmts.push_back(S);
    }

    EXPECT_GE(stmts.size(), 3) << "Constructor should have at least 3 member assignments";

    // Extract field names from assignments to verify initialization order
    std::vector<std::string> initOrder;

    for (size_t i = 0; i < 3 && i < stmts.size(); ++i) {
        BinaryOperator *assign = dyn_cast<BinaryOperator>(stmts[i]);
        if (!assign || assign->getOpcode() != BO_Assign) {
            continue;
        }

        // Get LHS (this->field)
        MemberExpr *member = dyn_cast<MemberExpr>(assign->getLHS()->IgnoreImpCasts());
        if (member) {
            FieldDecl *field = dyn_cast<FieldDecl>(member->getMemberDecl());
            if (field) {
                initOrder.push_back(field->getNameAsString());
            }
        }
    }

    // Verify initialization order matches DECLARATION order (x, y, z)
    // NOT initializer list order (z, x, y)
    EXPECT_EQ(initOrder.size(), 3) << "Should have 3 member initializations";

    // Critical assertion: members initialized in declaration order
    ASSERT_EQ(initOrder[0], "x")
        << "First initialization must be 'x' (declared first), got: " << initOrder[0];
    ASSERT_EQ(initOrder[1], "y")
        << "Second initialization must be 'y' (declared second), got: " << initOrder[1];
    ASSERT_EQ(initOrder[2], "z")
        << "Third initialization must be 'z' (declared third), got: " << initOrder[2];

    // This test currently FAILS because the implementation follows
    // initializer list order (z, x, y) instead of declaration order (x, y, z)
}

/**
 * Test Case 19: Empty Member Init List
 *
 * Verifies that constructors with empty member init lists still work.
 */
TEST_F(InheritanceTestFixture, EmptyMemberInitList) {
    const char *code = R"(
        class Simple {
            int value;
        public:
            Simple() {}  // Empty init list - default initialization
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *ctor = visitor.getCtor("Simple__ctor");
    ASSERT_NE(ctor, nullptr) << "Simple__ctor should be generated";

    // Empty init list should generate constructor with no member assignments
    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(ctor->getBody());
    ASSERT_NE(body, nullptr) << "Constructor body should exist (even if empty)";
}



/**
 * Test Case 20: Implicit Default Constructor with Primitive Members
 *
 * Tests that a default constructor is generated when no constructors are defined.
 * The generated constructor should zero-initialize primitive members.
 */
TEST_F(InheritanceTestFixture, ImplicitDefaultConstructorPrimitives) {
    const char *code = R"(
        class Point {
            int x, y;
            // No constructor defined - implicit default constructor needed
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Should generate default constructor: Point__ctor_default
    FunctionDecl *ctor = visitor.getCtor("Point__ctor_default");
    ASSERT_NE(ctor, nullptr) << "Point__ctor_default should be generated";

    // Verify constructor has 'this' parameter
    EXPECT_EQ(ctor->parameters().size(), 1) << "Default ctor should have only 'this' parameter";

    // Get constructor body
    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(ctor->getBody());
    ASSERT_NE(body, nullptr) << "Constructor body should exist";

    // Should have 2 assignments: this->x = 0; this->y = 0;
    std::vector<BinaryOperator*> assignments;
    for (Stmt *S : body->body()) {
        if (BinaryOperator *assign = dyn_cast<BinaryOperator>(S)) {
            if (assign->getOpcode() == BO_Assign) {
                assignments.push_back(assign);
            }
        }
    }

    EXPECT_EQ(assignments.size(), 2) << "Should have 2 member zero-initializations";
}



/**
 * Test Case 21: Implicit Default Constructor with Class-Type Members
 *
 * Tests that default constructor calls default constructors of class-type members.
 */
TEST_F(InheritanceTestFixture, ImplicitDefaultConstructorWithClassMembers) {
    const char *code = R"(
        class Inner {
            int value;
        public:
            Inner() : value(0) {}
        };

        class Outer {
            int id;
            Inner inner;  // Class-type member
            // No constructor - implicit default needed
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Should generate Outer__ctor_default
    FunctionDecl *ctor = visitor.getCtor("Outer__ctor_default");
    ASSERT_NE(ctor, nullptr) << "Outer__ctor_default should be generated";

    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(ctor->getBody());
    ASSERT_NE(body, nullptr) << "Constructor body should exist";

    // Should have:
    // 1. this->id = 0; (primitive zero-init)
    // 2. Inner__ctor(&this->inner); (class member default ctor call)
    bool hasIdInit = false;
    bool hasInnerCtorCall = false;

    for (Stmt *S : body->body()) {
        // Check for primitive assignment
        if (BinaryOperator *assign = dyn_cast<BinaryOperator>(S)) {
            if (MemberExpr *member = dyn_cast<MemberExpr>(assign->getLHS()->IgnoreImpCasts())) {
                if (FieldDecl *field = dyn_cast<FieldDecl>(member->getMemberDecl())) {
                    if (field->getNameAsString() == "id") {
                        hasIdInit = true;
                    }
                }
            }
        }

        // Check for Inner constructor call
        if (CallExpr *call = dyn_cast<CallExpr>(S)) {
            if (FunctionDecl *callee = call->getDirectCallee()) {
                std::string calleeName = callee->getNameAsString();
                if (calleeName.find("Inner__ctor") != std::string::npos) {
                    hasInnerCtorCall = true;
                }
            }
        }
    }

    ASSERT_TRUE(hasIdInit) << "Should initialize primitive member 'id'";
    ASSERT_TRUE(hasInnerCtorCall) << "Should call Inner default constructor for 'inner' member";
}



/**
 * Test Case 22: No Implicit Default Constructor with Explicit Parameterized Constructor
 *
 * Tests that default constructor is NOT generated when user defines
 * a parameterized constructor.
 */
TEST_F(InheritanceTestFixture, NoImplicitDefaultWithExplicitCtor) {
    const char *code = R"(
        class Point {
            int x, y;
        public:
            Point(int a, int b) : x(a), y(b) {}  // User-defined parameterized ctor
            // No implicit default ctor should be generated
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Should NOT generate default constructor
    FunctionDecl *defaultCtor = visitor.getCtor("Point__ctor_default");
    EXPECT_EQ(defaultCtor, nullptr) << "Should NOT generate default ctor when user defines parameterized ctor";

    // But should generate the user-defined parameterized constructor
    FunctionDecl *paramCtor = visitor.getCtor("Point__ctor");
    ASSERT_NE(paramCtor, nullptr) << "Should generate user-defined parameterized ctor";
}

/**
 * Test Case 23: Implicit Copy Constructor with Primitive Members
 *
 * Tests that copy constructor is generated and performs memberwise copy
 * for primitive members.
 */
TEST_F(InheritanceTestFixture, ImplicitCopyConstructorPrimitives) {
    const char *code = R"(
        class Vector {
            double x, y, z;
        public:
            Vector(double a, double b, double c) : x(a), y(b), z(c) {}
            // No copy constructor defined - implicit copy ctor needed
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Should generate copy constructor: Vector__ctor_copy
    FunctionDecl *copyCtor = visitor.getCtor("Vector__ctor_copy");
    ASSERT_NE(copyCtor, nullptr) << "Vector__ctor_copy should be generated";

    // Verify parameters: (this, const Vector* other)
    EXPECT_EQ(copyCtor->parameters().size(), 2) << "Copy ctor should have 2 parameters";

    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(copyCtor->getBody());
    ASSERT_NE(body, nullptr) << "Copy constructor body should exist";

    // Should have 3 assignments: this->x = other->x; this->y = other->y; this->z = other->z;
    std::vector<BinaryOperator*> assignments;
    for (Stmt *S : body->body()) {
        if (BinaryOperator *assign = dyn_cast<BinaryOperator>(S)) {
            if (assign->getOpcode() == BO_Assign) {
                assignments.push_back(assign);
            }
        }
    }

    EXPECT_EQ(assignments.size(), 3) << "Should have 3 memberwise copy assignments";
}

/**
 * Test Case 24: Implicit Copy Constructor with Class-Type Members
 *
 * Tests that copy constructor calls copy constructors of class-type members.
 */
TEST_F(InheritanceTestFixture, ImplicitCopyConstructorWithClassMembers) {
    const char *code = R"(
        class Inner {
            int value;
        public:
            Inner(int v) : value(v) {}
            Inner(const Inner& other) : value(other.value) {}
        };

        class Outer {
            int id;
            Inner inner;
        public:
            Outer(int i, int v) : id(i), inner(v) {}
            // No copy constructor - implicit copy ctor needed
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Should generate Outer__ctor_copy
    FunctionDecl *copyCtor = visitor.getCtor("Outer__ctor_copy");
    ASSERT_NE(copyCtor, nullptr) << "Outer__ctor_copy should be generated";

    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(copyCtor->getBody());
    ASSERT_NE(body, nullptr) << "Copy constructor body should exist";

    // Should have:
    // 1. this->id = other->id; (primitive memberwise copy)
    // 2. Inner__ctor_copy(&this->inner, &other->inner); (class member copy ctor call)
    bool hasIdCopy = false;
    bool hasInnerCopyCall = false;

    for (Stmt *S : body->body()) {
        // Check for primitive copy assignment
        if (BinaryOperator *assign = dyn_cast<BinaryOperator>(S)) {
            if (MemberExpr *member = dyn_cast<MemberExpr>(assign->getLHS()->IgnoreImpCasts())) {
                if (FieldDecl *field = dyn_cast<FieldDecl>(member->getMemberDecl())) {
                    if (field->getNameAsString() == "id") {
                        hasIdCopy = true;
                    }
                }
            }
        }

        // Check for Inner copy constructor call
        // Could be Inner__ctor_copy (implicit) or Inner__ctor_X (explicit)
        if (CallExpr *call = dyn_cast<CallExpr>(S)) {
            if (FunctionDecl *callee = call->getDirectCallee()) {
                std::string calleeName = callee->getNameAsString();
                // Check for any Inner constructor with 2 params (this + other = copy ctor)
                if (calleeName.find("Inner__ctor") != std::string::npos &&
                    callee->param_size() == 2) {
                    hasInnerCopyCall = true;
                }
            }
        }
    }

    ASSERT_TRUE(hasIdCopy) << "Should copy primitive member 'id'";
    ASSERT_TRUE(hasInnerCopyCall) << "Should call Inner copy constructor for 'inner' member";
}



/**
 * Test Case 25: Implicit Copy Constructor with Pointer Members (Shallow Copy)
 *
 * Tests that copy constructor performs shallow copy for pointer members.
 */
TEST_F(InheritanceTestFixture, ImplicitCopyConstructorWithPointers) {
    const char *code = R"(
        class Buffer {
            int* data;
            int size;
        public:
            Buffer(int s) : data(new int[s]), size(s) {}
            // No copy constructor - implicit shallow copy needed
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Should generate Buffer__ctor_copy
    FunctionDecl *copyCtor = visitor.getCtor("Buffer__ctor_copy");
    ASSERT_NE(copyCtor, nullptr) << "Buffer__ctor_copy should be generated";

    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(copyCtor->getBody());
    ASSERT_NE(body, nullptr) << "Copy constructor body should exist";

    // Should have 2 assignments: this->data = other->data; this->size = other->size;
    // (shallow copy - just copy the pointer, not the data)
    std::vector<BinaryOperator*> assignments;
    for (Stmt *S : body->body()) {
        if (BinaryOperator *assign = dyn_cast<BinaryOperator>(S)) {
            if (assign->getOpcode() == BO_Assign) {
                assignments.push_back(assign);
            }
        }
    }

    EXPECT_EQ(assignments.size(), 2) << "Should have 2 memberwise (shallow) copy assignments";
}



/**
 * Test Case 26: Simple Member Constructor Calls
 *
 * This test verifies that class-type members get constructor calls in
 * explicit constructors (not just implicit ones from Story #62).
 *
 * C++ Semantics: When a constructor has a member initializer for a class-type
 * member like `inner(val)`, it should call the member's constructor, NOT
 * perform assignment.
 *
 * Current Bug: Member initializers translate to assignment (this->inner = val)
 * Expected: Should call constructor (Inner__ctor(&this->inner, val))
 */
TEST_F(InheritanceTestFixture, SimpleMemberConstructorCalls) {
    std::cout << "DEBUG: Entered test_SimpleMemberConstructorCalls\n";
    std::cout.flush();
    std::cout << "DEBUG: After TEST_START\n";
    std::cout.flush();

    const char *code = R"(
        class Inner {
            int value;
        public:
            Inner(int v) : value(v) {}
            int getValue() const { return value; }
        };

        class Outer {
            Inner inner;
        public:
            Outer(int v) : inner(v) {}
            int getInnerValue() const { return inner.getValue(); }
        };
    )";

    std::cout << "DEBUG: About to buildAST\n";
    std::cout.flush();
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    std::cout << "DEBUG: AST built successfully\n";
    std::cout.flush();
    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    std::cout << "DEBUG: About to TraverseDecl\n";
    std::cout.flush();
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    std::cout << "DEBUG: TraverseDecl completed\n";
    std::cout.flush();

    // Get Outer constructor
    FunctionDecl *outerCtor = visitor.getCtor("Outer__ctor");
    ASSERT_NE(outerCtor, nullptr) << "Outer__ctor not found";

    // Check constructor body
    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(outerCtor->getBody());
    ASSERT_NE(body, nullptr) << "Outer constructor body is null";

    // Should have 1 statement: Inner__ctor(&this->inner, v)
    EXPECT_GE(body->size(), 1) << "Expected at least 1 statement (member ctor call)";

    // Convert body to vector for safe access
    std::vector<Stmt*> stmts;
    for (Stmt *S : body->body()) {
        stmts.push_back(S);
    }

    // Verify first statement is a call expression (constructor call)
    CallExpr *memberCtorCall = dyn_cast<CallExpr>(stmts[0]);
    ASSERT_NE(memberCtorCall, nullptr) << "Expected member constructor call, not assignment";

    // Verify it's calling Inner__ctor
    FunctionDecl *callee = memberCtorCall->getDirectCallee();
    ASSERT_NE(callee, nullptr) << "Constructor call has no callee";

    std::string calleeName = callee->getNameAsString();
    ASSERT_NE(calleeName.find("Inner__ctor"), std::string::npos)
        << "Expected call to Inner__ctor, got: " << calleeName;
}



/**
 * Test Case 27: Member Destructor Calls
 *
 * This test verifies that class-type members get destructor calls.
 *
 * C++ Semantics: When a class has class-type members, the destructor
 * should call member destructors in reverse declaration order.
 *
 * Current Bug: Member destructors are not called at all
 * Expected: Should call Resource__dtor(&this->res)
 */
TEST_F(InheritanceTestFixture, MemberDestructorCalls) {
    const char *code = R"(
        class Resource {
            int value;
        public:
            Resource() : value(42) {}
            ~Resource() {}
            int getValue() const { return value; }
        };

        class Container {
            Resource res;
        public:
            Container() {}
            ~Container() {}
            int getResourceValue() const { return res.getValue(); }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get Container destructor
    FunctionDecl *containerDtor = visitor.getDtor("Container__dtor");
    ASSERT_NE(containerDtor, nullptr) << "Container__dtor not found";

    // Check destructor body
    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(containerDtor->getBody());
    ASSERT_NE(body, nullptr) << "Container destructor body is null";

    // Should have 1 statement: Resource__dtor(&this->res)
    // (derived body is empty, no base class)
    EXPECT_GE(body->size(), 1) << "Expected at least 1 statement (member dtor call)";

    // Convert body to vector for safe access
    std::vector<Stmt*> stmts;
    for (Stmt *S : body->body()) {
        stmts.push_back(S);
    }

    // Verify we have a call expression (destructor call)
    CallExpr *memberDtorCall = dyn_cast<CallExpr>(stmts[0]);
    ASSERT_NE(memberDtorCall, nullptr) << "Expected member destructor call";

    // Verify it's calling Resource__dtor
    FunctionDecl *callee = memberDtorCall->getDirectCallee();
    ASSERT_NE(callee, nullptr) << "Destructor call has no callee";

    std::string calleeName = callee->getNameAsString();
    ASSERT_NE(calleeName.find("Resource__dtor"), std::string::npos)
        << "Expected call to Resource__dtor, got: " << calleeName;
}



/**
 * Test Case 28: Complete Chaining - Base, Members, and Derived
 *
 * This test verifies complete constructor/destructor chaining with both
 * base classes and members.
 *
 * C++ Constructor Order: Base → Members → Derived body
 * C++ Destructor Order: Derived body → Members (reverse) → Base
 */
TEST_F(InheritanceTestFixture, CompleteChaining_BaseAndMembers) {
    const char *code = R"(
        class Base {
            int baseVal;
        public:
            Base(int v) : baseVal(v) {}
            ~Base() {}
            int getBaseVal() const { return baseVal; }
        };

        class Member {
            int memberVal;
        public:
            Member(int v) : memberVal(v) {}
            ~Member() {}
            int getMemberVal() const { return memberVal; }
        };

        class Derived : public Base {
            Member mem;
        public:
            Derived(int b, int m) : Base(b), mem(m) {}
            ~Derived() {}
            int getMemberValue() const { return mem.getMemberVal(); }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // === Test Constructor: Base → Member → Body ===
    FunctionDecl *derivedCtor = visitor.getCtor("Derived__ctor");
    ASSERT_NE(derivedCtor, nullptr) << "Derived__ctor not found";

    CompoundStmt *ctorBody = dyn_cast_or_null<CompoundStmt>(derivedCtor->getBody());
    ASSERT_NE(ctorBody, nullptr) << "Derived constructor body is null";

    // Should have 2 statements: Base__ctor, Member__ctor
    // (derived body is empty)
    EXPECT_GE(ctorBody->size(), 2) << "Expected at least 2 statements (base ctor, member ctor)";

    // Convert body to vector for indexed access
    std::vector<Stmt*> ctorStmts;
    for (Stmt *S : ctorBody->body()) {
        ctorStmts.push_back(S);
    }

    // Verify first call is to Base__ctor
    CallExpr *baseCtorCall = dyn_cast<CallExpr>(ctorStmts[0]);
    ASSERT_NE(baseCtorCall, nullptr) << "Expected base constructor call first";

    FunctionDecl *baseCallee = baseCtorCall->getDirectCallee();
    ASSERT_NE(baseCallee, nullptr) << "Base constructor call has no callee";
    EXPECT_NE(baseCallee->getNameAsString().find("Base__ctor"), std::string::npos) << "First call should be Base__ctor";

    // Verify second call is to Member__ctor
    CallExpr *memberCtorCall = dyn_cast<CallExpr>(ctorStmts[1]);
    ASSERT_NE(memberCtorCall, nullptr) << "Expected member constructor call second";

    FunctionDecl *memberCallee = memberCtorCall->getDirectCallee();
    ASSERT_NE(memberCallee, nullptr) << "Member constructor call has no callee";
    EXPECT_NE(memberCallee->getNameAsString().find("Member__ctor"), std::string::npos) << "Second call should be Member__ctor";

    // === Test Destructor: Body → Member → Base ===
    FunctionDecl *derivedDtor = visitor.getDtor("Derived__dtor");
    ASSERT_NE(derivedDtor, nullptr) << "Derived__dtor not found";

    CompoundStmt *dtorBody = dyn_cast_or_null<CompoundStmt>(derivedDtor->getBody());
    ASSERT_NE(dtorBody, nullptr) << "Derived destructor body is null";

    // Should have 2 statements: Member__dtor, Base__dtor
    // (derived body is empty)
    EXPECT_GE(dtorBody->size(), 2) << "Expected at least 2 statements (member dtor, base dtor)";

    // Convert body to vector for indexed access
    std::vector<Stmt*> dtorStmts;
    for (Stmt *S : dtorBody->body()) {
        dtorStmts.push_back(S);
    }

    // Verify first call is to Member__dtor
    CallExpr *memberDtorCall = dyn_cast<CallExpr>(dtorStmts[0]);
    ASSERT_NE(memberDtorCall, nullptr) << "Expected member destructor call first";

    FunctionDecl *memberDCallee = memberDtorCall->getDirectCallee();
    ASSERT_NE(memberDCallee, nullptr) << "Member destructor call has no callee";
    EXPECT_NE(memberDCallee->getNameAsString().find("Member__dtor"), std::string::npos) << "First call should be Member__dtor";

    // Verify second call is to Base__dtor
    CallExpr *baseDtorCall = dyn_cast<CallExpr>(dtorStmts[1]);
    ASSERT_NE(baseDtorCall, nullptr) << "Expected base destructor call second";

    FunctionDecl *baseDCallee = baseDtorCall->getDirectCallee();
    ASSERT_NE(baseDCallee, nullptr) << "Base destructor call has no callee";
    EXPECT_NE(baseDCallee->getNameAsString().find("Base__dtor"), std::string::npos) << "Second call should be Base__dtor";
}



/**
 * Test Case 29: Multiple Members - Declaration Order Verification
 *
 * This test verifies that multiple class-type members are constructed in
 * declaration order (not init list order) and destructed in reverse.
 *
 * C++ Semantics:
 * - Constructor: Members initialized in DECLARATION order (a, b, c)
 * - Destructor: Members destroyed in REVERSE declaration order (c, b, a)
 * - Init list order is IGNORED for construction
 */
TEST_F(InheritanceTestFixture, MultipleMembersOrderVerification) {
    const char *code = R"(
        class A {
        public:
            A() {}
            ~A() {}
        };

        class B {
        public:
            B() {}
            ~B() {}
        };

        class C {
        public:
            C() {}
            ~C() {}
        };

        class Multi {
            A a;
            B b;
            C c;
        public:
            // Init list order: c, b, a (DIFFERENT from declaration!)
            Multi() : c(), b(), a() {}
            ~Multi() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // === Test Constructor Order: a, b, c (declaration order) ===
    FunctionDecl *multiCtor = visitor.getCtor("Multi__ctor");
    ASSERT_NE(multiCtor, nullptr) << "Multi__ctor not found";

    CompoundStmt *ctorBody = dyn_cast_or_null<CompoundStmt>(multiCtor->getBody());
    ASSERT_NE(ctorBody, nullptr) << "Multi constructor body is null";

    // Should have 3 constructor calls
    EXPECT_GE(ctorBody->size(), 3) << "Expected at least 3 member constructor calls";

    // Convert body to vector for indexed access
    std::vector<Stmt*> ctorStmts;
    for (Stmt *S : ctorBody->body()) {
        ctorStmts.push_back(S);
    }

    // Extract constructor call names
    std::vector<std::string> ctorCallOrder;
    for (size_t i = 0; i < 3 && i < ctorStmts.size(); ++i) {
        if (CallExpr *call = dyn_cast<CallExpr>(ctorStmts[i])) {
            if (FunctionDecl *callee = call->getDirectCallee()) {
                ctorCallOrder.push_back(callee->getNameAsString());
            }
        }
    }

    // Verify construction order: A__ctor, B__ctor, C__ctor (declaration order)
    EXPECT_EQ(ctorCallOrder.size(), 3) << "Should have 3 constructor calls";
    ASSERT_NE(ctorCallOrder[0].find("A__ctor"), std::string::npos)
        << "First ctor should be A__ctor (declared first), got: " << ctorCallOrder[0];
    ASSERT_NE(ctorCallOrder[1].find("B__ctor"), std::string::npos)
        << "Second ctor should be B__ctor (declared second), got: " << ctorCallOrder[1];
    ASSERT_NE(ctorCallOrder[2].find("C__ctor"), std::string::npos)
        << "Third ctor should be C__ctor (declared third), got: " << ctorCallOrder[2];

    // === Test Destructor Order: c, b, a (reverse declaration order) ===
    FunctionDecl *multiDtor = visitor.getDtor("Multi__dtor");
    ASSERT_NE(multiDtor, nullptr) << "Multi__dtor not found";

    CompoundStmt *dtorBody = dyn_cast_or_null<CompoundStmt>(multiDtor->getBody());
    ASSERT_NE(dtorBody, nullptr) << "Multi destructor body is null";

    // Should have 3 destructor calls
    EXPECT_GE(dtorBody->size(), 3) << "Expected at least 3 member destructor calls";

    // Convert body to vector for indexed access
    std::vector<Stmt*> dtorStmts;
    for (Stmt *S : dtorBody->body()) {
        dtorStmts.push_back(S);
    }

    // Extract destructor call names
    std::vector<std::string> dtorCallOrder;
    for (size_t i = 0; i < 3 && i < dtorStmts.size(); ++i) {
        if (CallExpr *call = dyn_cast<CallExpr>(dtorStmts[i])) {
            if (FunctionDecl *callee = call->getDirectCallee()) {
                dtorCallOrder.push_back(callee->getNameAsString());
            }
        }
    }

    // Verify destruction order: C__dtor, B__dtor, A__dtor (reverse declaration order)
    EXPECT_EQ(dtorCallOrder.size(), 3) << "Should have 3 destructor calls";
    ASSERT_NE(dtorCallOrder[0].find("C__dtor"), std::string::npos)
        << "First dtor should be C__dtor (declared last), got: " << dtorCallOrder[0];
    ASSERT_NE(dtorCallOrder[1].find("B__dtor"), std::string::npos)
        << "Second dtor should be B__dtor (declared middle), got: " << dtorCallOrder[1];
    ASSERT_NE(dtorCallOrder[2].find("A__dtor"), std::string::npos)
        << "Third dtor should be A__dtor (declared first), got: " << dtorCallOrder[2];
}



/**
 * Test Case 32: Const Member Initialization
 *
 * This test verifies that const members can be initialized through init lists.
 *
 * C++ Semantics: Const members MUST be initialized via constructor init list
 * and cannot be assigned later. The translated C code must use const_cast or
 * special initialization to properly set const members.
 *
 * Story #64 - Category 1: Member Init Lists (Test 3/5)
 */
TEST_F(InheritanceTestFixture, ConstMemberInitialization) {
    const char *code = R"(
        class Immutable {
            const int id;
            int value;
        public:
            Immutable(int i, int v) : id(i), value(v) {}
            int getId() const { return id; }
            int getValue() const { return value; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get Immutable constructor
    FunctionDecl *immutableCtor = visitor.getCtor("Immutable__ctor");
    ASSERT_NE(immutableCtor, nullptr) << "Immutable__ctor not found";

    // Check constructor body has const member initialization
    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(immutableCtor->getBody());
    ASSERT_NE(body, nullptr) << "Immutable constructor body is null";

    // Should have 2 statements: id init (const member) + value init
    EXPECT_GE(body->size(), 2) << "Expected at least 2 initialization statements";

    // Convert body to vector
    std::vector<Stmt*> stmts;
    for (Stmt *S : body->body()) {
        stmts.push_back(S);
    }

    // Verify both members are initialized (we accept any valid initialization)
    // The key is that const members are handled without compilation errors
    EXPECT_GE(stmts.size(), 2) << "Expected at least 2 member initializations";
}



/**
 * Test Case 33: Reference Member Initialization
 *
 * This test verifies that reference members are initialized through init lists.
 *
 * C++ Semantics: Reference members MUST be initialized via constructor init list.
 * The translated C code must use pointer semantics to emulate references.
 *
 * Story #64 - Category 1: Member Init Lists (Test 4/5)
 */
TEST_F(InheritanceTestFixture, ReferenceMemberInitialization) {
    const char *code = R"(
        class RefHolder {
            int& ref;
            int value;
        public:
            RefHolder(int& r, int v) : ref(r), value(v) {}
            int getRef() const { return ref; }
            void setRef(int newVal) { ref = newVal; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get RefHolder constructor
    FunctionDecl *refHolderCtor = visitor.getCtor("RefHolder__ctor");
    ASSERT_NE(refHolderCtor, nullptr) << "RefHolder__ctor not found";

    // Check constructor body
    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(refHolderCtor->getBody());
    ASSERT_NE(body, nullptr) << "RefHolder constructor body is null";

    // Should have 2 statements: ref init (reference member) + value init
    EXPECT_GE(body->size(), 2) << "Expected at least 2 initialization statements";
}



/**
 * Test Case 34: Simple Delegating Constructor
 *
 * C++ Input:
 *   class Point {
 *       int x, y;
 *   public:
 *       Point(int x, int y) : x(x), y(y) {}
 *       Point(int val) : Point(val, val) {}  // Delegating
 *   };
 *
 * Expected C Output:
 *   void Point__ctor_int_int(struct Point *this, int x, int y) {
 *       this->x = x;
 *       this->y = y;
 *   }
 *   void Point__ctor_int(struct Point *this, int val) {
 *       Point__ctor_int_int(this, val, val);  // Delegate call
 *   }
 *
 * Acceptance Criteria:
 * - Delegating constructor detected
 * - Call to target constructor generated
 * - No member initialization in delegating constructor
 */
TEST_F(InheritanceTestFixture, SimpleDelegatingConstructor) {
    const char *code = R"(
        class Point {
            int x, y;
        public:
            Point(int x, int y) : x(x), y(y) {}
            Point(int val) : Point(val, val) {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get delegating constructor: Point(int) → Point__ctor_1
    FunctionDecl *delegatingCtor = visitor.getCtor("Point__ctor_1");
    ASSERT_NE(delegatingCtor, nullptr) << "Delegating constructor not generated";

    // Check body has exactly one statement: call to target constructor
    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(delegatingCtor->getBody());
    ASSERT_NE(body, nullptr) << "Delegating constructor body is null";
    EXPECT_EQ(body->size(), 1) << "Delegating constructor should have exactly 1 statement";

    // First statement should be call to Point__ctor (the two-param version)
    Stmt *firstStmt = *body->body_begin();
    CallExpr *targetCall = dyn_cast<CallExpr>(firstStmt);
    ASSERT_NE(targetCall, nullptr) << "First statement should be CallExpr to target constructor";

    // Verify it calls the target constructor
    if (FunctionDecl *callee = targetCall->getDirectCallee()) {
        std::string calleeName = callee->getNameAsString();
        EXPECT_EQ(calleeName, "Point__ctor") << "Should call Point__ctor";
    }
}

TEST_F(InheritanceTestFixture, DelegationChain) {
    const char *code = R"(
        class Data {
            int a, b, c;
        public:
            Data(int a, int b, int c) : a(a), b(b), c(c) {}
            Data(int a, int b) : Data(a, b, 0) {}
            Data(int a) : Data(a, 0) {}
            Data() : Data(0) {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Verify Data() delegates to Data(int) → Data__ctor_0 delegates to Data__ctor_1
    FunctionDecl *defaultCtor = visitor.getCtor("Data__ctor_0");
    ASSERT_NE(defaultCtor, nullptr) << "Default constructor not generated";

    CompoundStmt *defaultBody = dyn_cast_or_null<CompoundStmt>(defaultCtor->getBody());
    EXPECT_EQ(defaultBody != nullptr && defaultBody->size(), 1) << "Default constructor should have 1 delegation statement";

    // Verify Data(int) delegates to Data(int, int) → Data__ctor_1 delegates to Data__ctor_2
    FunctionDecl *oneCtor = visitor.getCtor("Data__ctor_1");
    ASSERT_NE(oneCtor, nullptr) << "One-param constructor not generated";

    CompoundStmt *oneBody = dyn_cast_or_null<CompoundStmt>(oneCtor->getBody());
    EXPECT_EQ(oneBody != nullptr && oneBody->size(), 1) << "One-param constructor should have 1 delegation statement";

    // Verify Data(int, int) delegates to Data(int, int, int) → Data__ctor_2 delegates to Data__ctor
    FunctionDecl *twoCtor = visitor.getCtor("Data__ctor_2");
    ASSERT_NE(twoCtor, nullptr) << "Two-param constructor not generated";

    CompoundStmt *twoBody = dyn_cast_or_null<CompoundStmt>(twoCtor->getBody());
    EXPECT_EQ(twoBody != nullptr && twoBody->size(), 1) << "Two-param constructor should have 1 delegation statement";
}



/**
 * Test Case 36: Entity System Scenario
 *
 * This test validates a complex real-world scenario: an entity system with
 * inheritance, RAII, and member constructors.
 *
 * C++ Semantics: This tests the complete object lifecycle:
 * - Base class construction (Component)
 * - Member construction (Transform)
 * - Derived class body execution
 * - Destruction in reverse order
 *
 * Story #64 - Category 5: Complex Scenarios (Test 1/3)
 */
TEST_F(InheritanceTestFixture, EntitySystemScenario) {
    const char *code = R"(
        class Transform {
            float x, y, z;
        public:
            Transform(float x, float y, float z) : x(x), y(y), z(z) {}
            ~Transform() {}
            float getX() const { return x; }
        };

        class Component {
        protected:
            int id;
        public:
            Component(int id) : id(id) {}
            virtual ~Component() {}
            int getId() const { return id; }
        };

        class MeshComponent : public Component {
            Transform transform;
            const int vertexCount;
        public:
            MeshComponent(int id, float x, float y, float z, int verts)
                : Component(id),
                  transform(x, y, z),
                  vertexCount(verts) {}

            ~MeshComponent() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get MeshComponent constructor
    FunctionDecl *meshCtor = visitor.getCtor("MeshComponent__ctor");
    ASSERT_NE(meshCtor, nullptr) << "MeshComponent__ctor not found";

    // Check constructor body
    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(meshCtor->getBody());
    ASSERT_NE(body, nullptr) << "MeshComponent constructor body is null";

    // Should have multiple statements:
    // 1. Base constructor call (Component__ctor)
    // 2. Member constructor call (Transform__ctor)
    // 3. Const member initialization (vertexCount)
    EXPECT_GE(body->size(), 3) << "Expected at least 3 initialization statements";

    // Get MeshComponent destructor
    FunctionDecl *meshDtor = visitor.getDtor("MeshComponent__dtor");
    ASSERT_NE(meshDtor, nullptr) << "MeshComponent__dtor not found";

    // Check destructor body
    CompoundStmt *dtorBody = dyn_cast_or_null<CompoundStmt>(meshDtor->getBody());
    ASSERT_NE(dtorBody, nullptr) << "MeshComponent destructor body is null";

    // Should have statements for member destructors and base destructor
    EXPECT_GE(dtorBody->size(), 2) << "Expected member + base destructor calls";
}



/**
 * Test Case 35: Container Class Scenario
 *
 * This test validates a container with dynamic allocation and copy semantics.
 *
 * C++ Semantics: Tests dynamic memory management with constructors/destructors.
 *
 * Story #64 - Category 5: Complex Scenarios (Test 2/3)
 */
TEST_F(InheritanceTestFixture, ContainerClassScenario) {
    const char *code = R"(
        class DynamicArray {
            int* data;
            int size;
        public:
            DynamicArray(int s) : size(s), data(new int[s]) {
                for (int i = 0; i < size; ++i) {
                    data[i] = 0;
                }
            }

            ~DynamicArray() {
                delete[] data;
            }

            int getSize() const { return size; }
            int* getData() { return data; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get DynamicArray constructor
    FunctionDecl *arrayCtor = visitor.getCtor("DynamicArray__ctor");
    ASSERT_NE(arrayCtor, nullptr) << "DynamicArray__ctor not found";

    // Check constructor body has initialization + loop
    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(arrayCtor->getBody());
    ASSERT_NE(body, nullptr) << "DynamicArray constructor body is null";

    // Should have member inits + for loop
    EXPECT_GE(body->size(), 3) << "Expected member inits + loop body";

    // Get DynamicArray destructor
    FunctionDecl *arrayDtor = visitor.getDtor("DynamicArray__dtor");
    ASSERT_NE(arrayDtor, nullptr) << "DynamicArray__dtor not found";

    // Check destructor has delete[] call
    CompoundStmt *dtorBody = dyn_cast_or_null<CompoundStmt>(arrayDtor->getBody());
    ASSERT_NE(dtorBody, nullptr) << "DynamicArray destructor body is null";

    EXPECT_GE(dtorBody->size(), 1) << "Expected delete[] statement";
}



/**
 * Test Case 36: Resource Manager Scenario
 *
 * This test validates a resource manager with inheritance, RAII, and complex initialization.
 *
 * C++ Semantics: Tests complete RAII pattern with base classes and member management.
 *
 * Story #64 - Category 5: Complex Scenarios (Test 3/3)
 */
TEST_F(InheritanceTestFixture, ResourceManagerScenario) {
    const char *code = R"(
        class Resource {
            int id;
        public:
            Resource(int i) : id(i) {}
            ~Resource() {}
            int getId() const { return id; }
        };

        class ResourceManager {
        protected:
            int maxResources;
        public:
            ResourceManager(int max) : maxResources(max) {}
            virtual ~ResourceManager() {}
        };

        class FileResourceManager : public ResourceManager {
            Resource defaultResource;
            const int bufferSize;
        public:
            FileResourceManager(int max, int bufSize)
                : ResourceManager(max),
                  defaultResource(0),
                  bufferSize(bufSize) {}

            ~FileResourceManager() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext& targetCtx = TargetContext::getInstance();
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);

    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get FileResourceManager constructor
    FunctionDecl *fileCtor = visitor.getCtor("FileResourceManager__ctor");
    ASSERT_NE(fileCtor, nullptr) << "FileResourceManager__ctor not found";

    // Check constructor body
    CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(fileCtor->getBody());
    ASSERT_NE(body, nullptr) << "FileResourceManager constructor body is null";

    // Should have:
    // 1. Base constructor call (ResourceManager__ctor)
    // 2. Member constructor call (Resource__ctor for defaultResource)
    // 3. Const member initialization (bufferSize)
    EXPECT_GE(body->size(), 3) << "Expected base + member + const initializations";

    // Get FileResourceManager destructor
    FunctionDecl *fileDtor = visitor.getDtor("FileResourceManager__dtor");
    ASSERT_NE(fileDtor, nullptr) << "FileResourceManager__dtor not found";

    // Check destructor body
    CompoundStmt *dtorBody = dyn_cast_or_null<CompoundStmt>(fileDtor->getBody());
    ASSERT_NE(dtorBody, nullptr) << "FileResourceManager destructor body is null";

    // Should have member destructor + base destructor calls
    EXPECT_GE(dtorBody->size(), 2) << "Expected member + base destructor calls";}
