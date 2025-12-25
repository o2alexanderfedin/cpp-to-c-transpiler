// TDD Tests for Single Inheritance - Epic #6 Implementation
// Story #50: Base Class Embedding in Struct Layout

#include <gtest/gtest.h>
#include "CppToCVisitor.h"
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecordLayout.h"

using namespace clang;

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

// Test fixture
class InheritanceTest : public ::testing::Test {
protected:
};

TEST_F(InheritanceTest, EmptyBaseClass) {
    const char *cpp = R"(
            class Base {};
            class Derived : public Base {};
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(cpp);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);

        // Run visitor on AST
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify Base struct generated
        RecordDecl *BaseStruct = visitor.getCStruct("Base");
        ASSERT_TRUE(BaseStruct != nullptr) << "Base struct not generated";
        ASSERT_TRUE(BaseStruct->field_empty()) << "Empty base should have no fields";

        // Verify Derived struct generated
        RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
        ASSERT_TRUE(DerivedStruct != nullptr) << "Derived struct not generated";
        ASSERT_TRUE(DerivedStruct->field_empty()) << "Derived from empty base should have no fields";
}

TEST_F(InheritanceTest, SingleBaseWithFields) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);

        // Run visitor on AST
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify Base struct
        RecordDecl *BaseStruct = visitor.getCStruct("Base");
        ASSERT_TRUE(BaseStruct != nullptr) << "Base struct not generated";
        ASSERT_TRUE(!BaseStruct->field_empty()) << "Base should have fields";

        unsigned baseFieldCount = 0;
        for (auto *Field : BaseStruct->fields()) {
            ASSERT_TRUE(Field->getName() == "x") << "Base field name should be 'x'";
            baseFieldCount++;
        }
        ASSERT_TRUE(baseFieldCount == 1) << "Base should have exactly 1 field";

        // Verify Derived struct
        RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
        ASSERT_TRUE(DerivedStruct != nullptr) << "Derived struct not generated";

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

        ASSERT_TRUE(derivedFieldCount == 2) << "Derived should have 2 fields (x + y)";
        ASSERT_TRUE(firstFieldName == "x") << "First field should be 'x' from Base (offset 0)";
        ASSERT_TRUE(secondFieldName == "y") << "Second field should be 'y' from Derived";
}

TEST_F(InheritanceTest, MultiLevelInheritance) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);

        // Run visitor on AST
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify struct C has 3 fields in correct order
        RecordDecl *CStruct = visitor.getCStruct("C");
        ASSERT_TRUE(CStruct != nullptr) << "C struct not generated";

        std::vector<std::string> fieldNames;
        for (auto *Field : CStruct->fields()) {
            fieldNames.push_back(Field->getNameAsString());
        }

        ASSERT_TRUE(fieldNames.size() == 3) << "C should have 3 fields (a, b, c)";
        ASSERT_TRUE(fieldNames[0] == "a") << "First field should be 'a' from A";
        ASSERT_TRUE(fieldNames[1] == "b") << "Second field should be 'b' from B";
        ASSERT_TRUE(fieldNames[2] == "c") << "Third field should be 'c' from C";
}

TEST_F(InheritanceTest, SizeofVerification) {
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
    TranslationUnitDecl *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *BaseClass = nullptr;
    CXXRecordDecl *DerivedClass = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Base") BaseClass = RD;
            if (RD->getNameAsString() == "Derived") DerivedClass = RD;
        }
    }

    ASSERT_TRUE(BaseClass && DerivedClass) << "Could not find C++ classes";

    const ASTRecordLayout &BaseLayout = AST->getASTContext().getASTRecordLayout(BaseClass);
    const ASTRecordLayout &DerivedLayout = AST->getASTContext().getASTRecordLayout(DerivedClass);

    uint64_t baseSize = BaseLayout.getSize().getQuantity();
    uint64_t derivedSize = DerivedLayout.getSize().getQuantity();

    // In C++, Derived should be larger than Base (has additional field)
    ASSERT_TRUE(derivedSize > baseSize) << "Derived should be larger than Base";

    // Derived size should be Base size + size of int (assuming no padding)
    uint64_t intSize = AST->getASTContext().getTypeSize(AST->getASTContext().IntTy) / 8;
    uint64_t expectedSize = baseSize + intSize;

    ASSERT_TRUE(derivedSize >= expectedSize) << "Derived size too small";
}

TEST_F(InheritanceTest, SimpleConstructorChaining) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Get generated C constructor for Derived
        FunctionDecl *DerivedCtor = visitor.getCtor("Derived__ctor");
        ASSERT_TRUE(DerivedCtor != nullptr) << "Derived constructor not generated";

        // Constructor should have a body
        ASSERT_TRUE(DerivedCtor->hasBody()) << "Derived constructor has no body";

        CompoundStmt *Body = dyn_cast<CompoundStmt>(DerivedCtor->getBody());
        ASSERT_TRUE(Body != nullptr) << "Derived constructor body is not a CompoundStmt";

        // Body should have at least 2 statements:
        // 1. Base constructor call
        // 2. Derived member initialization
        ASSERT_TRUE(Body->size() >= 2) << "Derived constructor should have >= 2 statements";

        // First statement should be a call to Base__ctor
        Stmt *FirstStmt = *Body->body_begin();
        CallExpr *BaseCtorCall = dyn_cast<CallExpr>(FirstStmt);
        ASSERT_TRUE(BaseCtorCall != nullptr) << "First statement should be a CallExpr (Base ctor call)";

        // Verify the call is to Base__ctor
        if (FunctionDecl *Callee = BaseCtorCall->getDirectCallee()) {
            std::string calleeName = Callee->getNameAsString();
            ASSERT_TRUE(calleeName == "Base__ctor") << "First call should be to Base__ctor";
        }
}

TEST_F(InheritanceTest, ConstructorChainingWithArgs) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        FunctionDecl *DerivedCtor = visitor.getCtor("Derived__ctor");
        ASSERT_TRUE(DerivedCtor != nullptr) << "Derived constructor not generated";

        CompoundStmt *Body = dyn_cast<CompoundStmt>(DerivedCtor->getBody());
        ASSERT_TRUE(Body != nullptr) << "Derived constructor has no body";

        // First statement should be Base__ctor call
        Stmt *FirstStmt = *Body->body_begin();
        CallExpr *BaseCtorCall = dyn_cast<CallExpr>(FirstStmt);
        ASSERT_TRUE(BaseCtorCall != nullptr) << "First statement should be Base ctor call";

        // Base__ctor should receive 3 arguments: this, a, b
        unsigned numArgs = BaseCtorCall->getNumArgs();
        ASSERT_TRUE(numArgs == 3) << "Base__ctor should receive 3 arguments (this, a, b)";
}

TEST_F(InheritanceTest, MultiLevelConstructorChaining) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Check Derived2 constructor calls Derived1 constructor (not Base)
        FunctionDecl *Derived2Ctor = visitor.getCtor("Derived2__ctor");
        ASSERT_TRUE(Derived2Ctor != nullptr) << "Derived2 constructor not generated";

        CompoundStmt *Body = dyn_cast<CompoundStmt>(Derived2Ctor->getBody());
        ASSERT_TRUE(Body != nullptr && Body->size() >= 1) << "Derived2 constructor should have body";

        Stmt *FirstStmt = *Body->body_begin();
        CallExpr *ParentCtorCall = dyn_cast<CallExpr>(FirstStmt);
        ASSERT_TRUE(ParentCtorCall != nullptr) << "First statement should be parent ctor call";

        // Verify it calls Derived1__ctor (not Base__ctor)
        if (FunctionDecl *Callee = ParentCtorCall->getDirectCallee()) {
            std::string calleeName = Callee->getNameAsString();
            ASSERT_TRUE(calleeName == "Derived1__ctor") << "Derived2 should call Derived1__ctor (not Base__ctor)";
        }
}

TEST_F(InheritanceTest, SimpleDestructorChaining) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Get generated C destructor for Derived
        FunctionDecl *DerivedDtor = visitor.getDtor("Derived__dtor");
        ASSERT_TRUE(DerivedDtor != nullptr) << "Derived destructor not generated";

        // Destructor should have a body
        ASSERT_TRUE(DerivedDtor->hasBody()) << "Derived destructor has no body";

        CompoundStmt *Body = dyn_cast<CompoundStmt>(DerivedDtor->getBody());
        ASSERT_TRUE(Body != nullptr) << "Derived destructor body is not a CompoundStmt";

        // Body should have at least 1 statement: Base destructor call
        ASSERT_TRUE(Body->size() >= 1) << "Derived destructor should have >= 1 statement";

        // Last statement should be a call to Base__dtor
        Stmt *LastStmt = *(Body->body_end() - 1);
        CallExpr *BaseDtorCall = dyn_cast<CallExpr>(LastStmt);
        ASSERT_TRUE(BaseDtorCall != nullptr) << "Last statement should be a CallExpr (Base dtor call)";

        // Verify the call is to Base__dtor
        if (FunctionDecl *Callee = BaseDtorCall->getDirectCallee()) {
            std::string calleeName = Callee->getNameAsString();
            ASSERT_TRUE(calleeName == "Base__dtor") << "Last call should be to Base__dtor";
        }
}

TEST_F(InheritanceTest, DestructorChainingWithBody) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        FunctionDecl *DerivedDtor = visitor.getDtor("Derived__dtor");
        ASSERT_TRUE(DerivedDtor != nullptr) << "Derived destructor not generated";

        CompoundStmt *Body = dyn_cast<CompoundStmt>(DerivedDtor->getBody());
        ASSERT_TRUE(Body != nullptr && Body->size() >= 2) << "Derived destructor should have >= 2 statements";

        // Last statement should be Base__dtor call
        Stmt *LastStmt = *(Body->body_end() - 1);
        CallExpr *BaseDtorCall = dyn_cast<CallExpr>(LastStmt);
        ASSERT_TRUE(BaseDtorCall != nullptr) << "Last statement should be Base dtor call";

        if (FunctionDecl *Callee = BaseDtorCall->getDirectCallee()) {
            std::string calleeName = Callee->getNameAsString();
            ASSERT_TRUE(calleeName == "Base__dtor") << "Last call should be to Base__dtor";
        }
}

TEST_F(InheritanceTest, MultiLevelDestructorChaining) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Check Derived2 destructor calls Derived1 destructor (not Base)
        FunctionDecl *Derived2Dtor = visitor.getDtor("Derived2__dtor");
        ASSERT_TRUE(Derived2Dtor != nullptr) << "Derived2 destructor not generated";

        CompoundStmt *Body = dyn_cast<CompoundStmt>(Derived2Dtor->getBody());
        ASSERT_TRUE(Body != nullptr && Body->size() >= 1) << "Derived2 destructor should have body";

        // Last statement should be parent dtor call
        Stmt *LastStmt = *(Body->body_end() - 1);
        CallExpr *ParentDtorCall = dyn_cast<CallExpr>(LastStmt);
        ASSERT_TRUE(ParentDtorCall != nullptr) << "Last statement should be parent dtor call";

        // Verify it calls Derived1__dtor (not Base__dtor)
        if (FunctionDecl *Callee = ParentDtorCall->getDirectCallee()) {
            std::string calleeName = Callee->getNameAsString();
            ASSERT_TRUE(calleeName == "Derived1__dtor") << "Derived2 should call Derived1__dtor (not Base__dtor)";
        }
}

TEST_F(InheritanceTest, MemberAccessInDerivedMethods) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify Derived struct has both x and y fields
        RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
        ASSERT_TRUE(DerivedStruct != nullptr) << "Derived struct not generated";

        unsigned fieldCount = 0;
        for (auto *F : DerivedStruct->fields()) {
            fieldCount++;
        }
        ASSERT_TRUE(fieldCount == 2) << "Derived should have 2 fields (x from Base, y from Derived)";
}

TEST_F(InheritanceTest, BasicUpcasting) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify Base struct exists
        RecordDecl *BaseStruct = visitor.getCStruct("Base");
        ASSERT_TRUE(BaseStruct != nullptr) << "Base struct not generated";

        // Verify Derived struct exists
        RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
        ASSERT_TRUE(DerivedStruct != nullptr) << "Derived struct not generated";

        // CRITICAL: Verify field layout - base fields MUST be first for safe upcasting
        auto fields = DerivedStruct->fields();
        auto it = fields.begin();
        ASSERT_TRUE(it != fields.end()) << "Derived should have fields";

        // First field must be from Base class
        FieldDecl *firstField = *it;
        ASSERT_TRUE(firstField->getNameAsString() == "x") << "First field must be 'x' from Base (offset 0 = safe upcasting)";

        // Second field should be from Derived class
        ++it;
        ASSERT_TRUE(it != fields.end()) << "Derived should have second field";
        FieldDecl *secondField = *it;
        ASSERT_TRUE(secondField->getNameAsString() == "y") << "Second field must be 'y' from Derived";

        // With this layout, (Base*)&derived is safe because:
        // - Base fields are at offset 0
        // - Casting Derived* to Base* gives same address
        // - Base methods can access Base fields correctly
}

TEST_F(InheritanceTest, MultiLevelUpcasting) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify all structs exist
        RecordDecl *BaseStruct = visitor.getCStruct("Base");
        ASSERT_TRUE(BaseStruct != nullptr) << "Base struct not generated";

        RecordDecl *DerivedStruct = visitor.getCStruct("Derived");
        ASSERT_TRUE(DerivedStruct != nullptr) << "Derived struct not generated";

        RecordDecl *GrandDerivedStruct = visitor.getCStruct("GrandDerived");
        ASSERT_TRUE(GrandDerivedStruct != nullptr) << "GrandDerived struct not generated";

        // CRITICAL: Verify GrandDerived has Base fields at offset 0 (for safe upcasting)
        auto fields = GrandDerivedStruct->fields();
        auto it = fields.begin();
        ASSERT_TRUE(it != fields.end()) << "GrandDerived should have fields";

        // First field must be 'x' from Base (offset 0)
        FieldDecl *firstField = *it;
        ASSERT_TRUE(firstField->getNameAsString() == "x") << "First field must be 'x' from Base (offset 0 for upcasting)";

        // Second field must be 'y' from Derived
        ++it;
        ASSERT_TRUE(it != fields.end()) << "GrandDerived should have second field";
        FieldDecl *secondField = *it;
        ASSERT_TRUE(secondField->getNameAsString() == "y") << "Second field must be 'y' from Derived";

        // Third field must be 'z' from GrandDerived
        ++it;
        ASSERT_TRUE(it != fields.end()) << "GrandDerived should have third field";
        FieldDecl *thirdField = *it;
        ASSERT_TRUE(thirdField->getNameAsString() == "z") << "Third field must be 'z' from GrandDerived";

        // With this layout, both upcasts work:
        // - (Derived*)&grandDerived works (offset 0)
        // - (Base*)&grandDerived works (offset 0)
        // - (Base*)&derived works (offset 0)
}

TEST_F(InheritanceTest, SimpleMethodOverriding) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify Base::print exists as Base_print
        FunctionDecl *basePrint = visitor.getCFunc("Base_print");
        ASSERT_TRUE(basePrint != nullptr) << "Base_print function not generated";
        ASSERT_TRUE(basePrint->getNumParams() == 1) << "Base_print should have 'this' parameter";

        // Verify Derived::print exists as Derived_print (separate function)
        FunctionDecl *derivedPrint = visitor.getCFunc("Derived_print");
        ASSERT_TRUE(derivedPrint != nullptr) << "Derived_print function not generated";
        ASSERT_TRUE(derivedPrint->getNumParams() == 1) << "Derived_print should have 'this' parameter";

        // Verify they are different functions (name mangling distinguishes them)
        ASSERT_TRUE(basePrint != derivedPrint) << "Base_print and Derived_print must be distinct functions";

        // Verify parameter types are correct
        ParmVarDecl *baseParam = basePrint->getParamDecl(0);
        QualType baseParamType = baseParam->getType();
        ASSERT_TRUE(baseParamType->isPointerType()) << "Base_print parameter should be pointer";

        ParmVarDecl *derivedParam = derivedPrint->getParamDecl(0);
        QualType derivedParamType = derivedParam->getType();
        ASSERT_TRUE(derivedParamType->isPointerType()) << "Derived_print parameter should be pointer";
}

TEST_F(InheritanceTest, MethodOverridingWithReturn) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify Animal::getLegs exists
        FunctionDecl *animalGetLegs = visitor.getCFunc("Animal_getLegs");
        ASSERT_TRUE(animalGetLegs != nullptr) << "Animal_getLegs function not generated";

        // Verify Bird::getLegs exists (separate function)
        FunctionDecl *birdGetLegs = visitor.getCFunc("Bird_getLegs");
        ASSERT_TRUE(birdGetLegs != nullptr) << "Bird_getLegs function not generated";

        // Verify they are distinct functions
        ASSERT_TRUE(animalGetLegs != birdGetLegs) << "Animal_getLegs and Bird_getLegs must be distinct";

        // Verify both return int
        QualType animalRetType = animalGetLegs->getReturnType();
        ASSERT_TRUE(animalRetType->isIntegerType()) << "Animal_getLegs should return int";

        QualType birdRetType = birdGetLegs->getReturnType();
        ASSERT_TRUE(birdRetType->isIntegerType()) << "Bird_getLegs should return int";
}

TEST_F(InheritanceTest, MethodOverridingWithParameters) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify Shape::setSize exists
        FunctionDecl *shapeSetSize = visitor.getCFunc("Shape_setSize");
        ASSERT_TRUE(shapeSetSize != nullptr) << "Shape_setSize function not generated";
        ASSERT_TRUE(shapeSetSize->getNumParams() == 2) << "Shape_setSize should have 2 parameters (this + s)";

        // Verify Circle::setSize exists
        FunctionDecl *circleSetSize = visitor.getCFunc("Circle_setSize");
        ASSERT_TRUE(circleSetSize != nullptr) << "Circle_setSize function not generated";
        ASSERT_TRUE(circleSetSize->getNumParams() == 2) << "Circle_setSize should have 2 parameters (this + s)";

        // Verify they are distinct
        ASSERT_TRUE(shapeSetSize != circleSetSize) << "Shape_setSize and Circle_setSize must be distinct";
}

TEST_F(InheritanceTest, ComprehensiveMultiLevelInheritance) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // ========================================================================
        // 1. MEMORY LAYOUT: Verify all ancestor fields embedded in order
        // ========================================================================

        RecordDecl *DogStruct = visitor.getCStruct("Dog");
        ASSERT_TRUE(DogStruct != nullptr) << "Dog struct not generated";

        auto fields = DogStruct->fields();
        std::vector<std::string> fieldNames;
        for (auto *F : fields) {
            fieldNames.push_back(F->getNameAsString());
        }

        ASSERT_TRUE(fieldNames.size() == 3) << "Dog should have 3 fields (age, furColor, barkVolume)";
        ASSERT_TRUE(fieldNames[0] == "age") << "Field 0 must be 'age' from Animal (grandparent)";
        ASSERT_TRUE(fieldNames[1] == "furColor") << "Field 1 must be 'furColor' from Mammal (parent)";
        ASSERT_TRUE(fieldNames[2] == "barkVolume") << "Field 2 must be 'barkVolume' from Dog";

        // ========================================================================
        // 2. CONSTRUCTOR CHAINING: Verify all constructors exist and chain
        // ========================================================================

        FunctionDecl *animalCtor = visitor.getCtor("Animal__ctor");
        ASSERT_TRUE(animalCtor != nullptr) << "Animal__ctor not generated";
        ASSERT_TRUE(animalCtor->getNumParams() == 2) << "Animal__ctor(this, age)";

        FunctionDecl *mammalCtor = visitor.getCtor("Mammal__ctor");
        ASSERT_TRUE(mammalCtor != nullptr) << "Mammal__ctor not generated";
        ASSERT_TRUE(mammalCtor->getNumParams() == 3) << "Mammal__ctor(this, age, furColor)";

        FunctionDecl *dogCtor = visitor.getCtor("Dog__ctor");
        ASSERT_TRUE(dogCtor != nullptr) << "Dog__ctor not generated";
        ASSERT_TRUE(dogCtor->getNumParams() == 4) << "Dog__ctor(this, age, furColor, barkVolume)";

        // ========================================================================
        // 3. DESTRUCTOR CHAINING: Verify all destructors exist
        // ========================================================================

        FunctionDecl *animalDtor = visitor.getDtor("Animal__dtor");
        ASSERT_TRUE(animalDtor != nullptr) << "Animal__dtor not generated";

        FunctionDecl *mammalDtor = visitor.getDtor("Mammal__dtor");
        ASSERT_TRUE(mammalDtor != nullptr) << "Mammal__dtor not generated";

        FunctionDecl *dogDtor = visitor.getDtor("Dog__dtor");
        ASSERT_TRUE(dogDtor != nullptr) << "Dog__dtor not generated";

        // ========================================================================
        // 4. METHOD OVERRIDING: Verify all speak() methods are distinct
        // ========================================================================

        FunctionDecl *animalSpeak = visitor.getCFunc("Animal_speak");
        ASSERT_TRUE(animalSpeak != nullptr) << "Animal_speak not generated";

        FunctionDecl *mammalSpeak = visitor.getCFunc("Mammal_speak");
        ASSERT_TRUE(mammalSpeak != nullptr) << "Mammal_speak not generated";

        FunctionDecl *dogSpeak = visitor.getCFunc("Dog_speak");
        ASSERT_TRUE(dogSpeak != nullptr) << "Dog_speak not generated";

        ASSERT_TRUE(animalSpeak != mammalSpeak) << "Animal_speak ≠ Mammal_speak";
        ASSERT_TRUE(mammalSpeak != dogSpeak) << "Mammal_speak ≠ Dog_speak";
        ASSERT_TRUE(animalSpeak != dogSpeak) << "Animal_speak ≠ Dog_speak";

        // ========================================================================
        // 5. MEMBER ACCESS: Verify Dog can access grandparent members
        // ========================================================================

        FunctionDecl *dogGetAge = visitor.getCFunc("Dog_getAge");
        ASSERT_TRUE(dogGetAge != nullptr) << "Dog_getAge not generated (accesses grandparent member)";

        // ========================================================================
        // 6. UPCASTING: Verify memory layout allows all upcasts
        // ========================================================================

        // With age at offset 0:
        // - (Mammal*)&dog works (age at offset 0)
        // - (Animal*)&dog works (age at offset 0)
        // - (Animal*)&mammal works (age at offset 0)

        RecordDecl *MammalStruct = visitor.getCStruct("Mammal");
        ASSERT_TRUE(MammalStruct != nullptr) << "Mammal struct not generated";

        auto mammalFields = MammalStruct->fields();
        auto mammalIt = mammalFields.begin();
        ASSERT_TRUE(mammalIt != mammalFields.end()) << "Mammal should have fields";
        ASSERT_TRUE((*mammalIt)->getNameAsString() == "age") << "Mammal's first field must be 'age' for safe upcasting";
}

TEST_F(InheritanceTest, EmptyMemberInitList) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        FunctionDecl *ctor = visitor.getCtor("Simple__ctor");
        ASSERT_TRUE(ctor != nullptr) << "Simple__ctor should be generated";

        // Empty init list should generate constructor with no member assignments
        CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(ctor->getBody());
        ASSERT_TRUE(body != nullptr) << "Constructor body should exist (even if empty)";
}

TEST_F(InheritanceTest, NoImplicitDefaultWithExplicitCtor) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Should NOT generate default constructor
        FunctionDecl *defaultCtor = visitor.getCtor("Point__ctor_default");
        ASSERT_TRUE(defaultCtor == nullptr) << "Should NOT generate default ctor when user defines parameterized ctor";

        // But should generate the user-defined parameterized constructor
        FunctionDecl *paramCtor = visitor.getCtor("Point__ctor");
        ASSERT_TRUE(paramCtor != nullptr) << "Should generate user-defined parameterized ctor";
}

TEST_F(InheritanceTest, SimpleMemberConstructorCalls) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);

        std::cout << "DEBUG: About to TraverseDecl\n";
        std::cout.flush();
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
        std::cout << "DEBUG: TraverseDecl completed\n";
        std::cout.flush();

        // Get Outer constructor
        FunctionDecl *outerCtor = visitor.getCtor("Outer__ctor");
        ASSERT_TRUE(outerCtor != nullptr) << "Outer__ctor not found";

        // Check constructor body
        CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(outerCtor->getBody());
        ASSERT_TRUE(body != nullptr) << "Outer constructor body is null";

        // Should have 1 statement: Inner__ctor(&this->inner, v)
        ASSERT_TRUE(body->size() >= 1) << "Expected at least 1 statement (member ctor call)";

        // Convert body to vector for safe access
        std::vector<Stmt*> stmts;
        for (Stmt *S : body->body()) {
            stmts.push_back(S);
        }

        // Verify first statement is a call expression (constructor call)
        CallExpr *memberCtorCall = dyn_cast<CallExpr>(stmts[0]);
        ASSERT_TRUE(memberCtorCall != nullptr) << "Expected member constructor call, not assignment";

        // Verify it's calling Inner__ctor
        FunctionDecl *callee = memberCtorCall->getDirectCallee();
        ASSERT_TRUE(callee != nullptr) << "Constructor call has no callee";

        std::string calleeName = callee->getNameAsString();
        ASSERT_TRUE(calleeName.find("Inner__ctor") != std::string::npos) << "Expected call to Inner__ctor, got: " + calleeName;
}

TEST_F(InheritanceTest, MemberDestructorCalls) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Get Container destructor
        FunctionDecl *containerDtor = visitor.getDtor("Container__dtor");
        ASSERT_TRUE(containerDtor != nullptr) << "Container__dtor not found";

        // Check destructor body
        CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(containerDtor->getBody());
        ASSERT_TRUE(body != nullptr) << "Container destructor body is null";

        // Should have 1 statement: Resource__dtor(&this->res)
        // (derived body is empty, no base class)
        ASSERT_TRUE(body->size() >= 1) << "Expected at least 1 statement (member dtor call)";

        // Convert body to vector for safe access
        std::vector<Stmt*> stmts;
        for (Stmt *S : body->body()) {
            stmts.push_back(S);
        }

        // Verify we have a call expression (destructor call)
        CallExpr *memberDtorCall = dyn_cast<CallExpr>(stmts[0]);
        ASSERT_TRUE(memberDtorCall != nullptr) << "Expected member destructor call";

        // Verify it's calling Resource__dtor
        FunctionDecl *callee = memberDtorCall->getDirectCallee();
        ASSERT_TRUE(callee != nullptr) << "Destructor call has no callee";

        std::string calleeName = callee->getNameAsString();
        ASSERT_TRUE(calleeName.find("Resource__dtor") != std::string::npos) << "Expected call to Resource__dtor, got: " + calleeName;
}

TEST_F(InheritanceTest, CompleteChaining_BaseAndMembers) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // === Test Constructor: Base → Member → Body ===
        FunctionDecl *derivedCtor = visitor.getCtor("Derived__ctor");
        ASSERT_TRUE(derivedCtor != nullptr) << "Derived__ctor not found";

        CompoundStmt *ctorBody = dyn_cast_or_null<CompoundStmt>(derivedCtor->getBody());
        ASSERT_TRUE(ctorBody != nullptr) << "Derived constructor body is null";

        // Should have 2 statements: Base__ctor, Member__ctor
        // (derived body is empty)
        ASSERT_TRUE(ctorBody->size() >= 2) << "Expected at least 2 statements (base ctor, member ctor)";

        // Convert body to vector for indexed access
        std::vector<Stmt*> ctorStmts;
        for (Stmt *S : ctorBody->body()) {
            ctorStmts.push_back(S);
        }

        // Verify first call is to Base__ctor
        CallExpr *baseCtorCall = dyn_cast<CallExpr>(ctorStmts[0]);
        ASSERT_TRUE(baseCtorCall != nullptr) << "Expected base constructor call first";

        FunctionDecl *baseCallee = baseCtorCall->getDirectCallee();
        ASSERT_TRUE(baseCallee != nullptr) << "Base constructor call has no callee";
        ASSERT_TRUE(baseCallee->getNameAsString().find("Base__ctor") != std::string::npos) << "First call should be Base__ctor";

        // Verify second call is to Member__ctor
        CallExpr *memberCtorCall = dyn_cast<CallExpr>(ctorStmts[1]);
        ASSERT_TRUE(memberCtorCall != nullptr) << "Expected member constructor call second";

        FunctionDecl *memberCallee = memberCtorCall->getDirectCallee();
        ASSERT_TRUE(memberCallee != nullptr) << "Member constructor call has no callee";
        ASSERT_TRUE(memberCallee->getNameAsString().find("Member__ctor") != std::string::npos) << "Second call should be Member__ctor";

        // === Test Destructor: Body → Member → Base ===
        FunctionDecl *derivedDtor = visitor.getDtor("Derived__dtor");
        ASSERT_TRUE(derivedDtor != nullptr) << "Derived__dtor not found";

        CompoundStmt *dtorBody = dyn_cast_or_null<CompoundStmt>(derivedDtor->getBody());
        ASSERT_TRUE(dtorBody != nullptr) << "Derived destructor body is null";

        // Should have 2 statements: Member__dtor, Base__dtor
        // (derived body is empty)
        ASSERT_TRUE(dtorBody->size() >= 2) << "Expected at least 2 statements (member dtor, base dtor)";

        // Convert body to vector for indexed access
        std::vector<Stmt*> dtorStmts;
        for (Stmt *S : dtorBody->body()) {
            dtorStmts.push_back(S);
        }

        // Verify first call is to Member__dtor
        CallExpr *memberDtorCall = dyn_cast<CallExpr>(dtorStmts[0]);
        ASSERT_TRUE(memberDtorCall != nullptr) << "Expected member destructor call first";

        FunctionDecl *memberDCallee = memberDtorCall->getDirectCallee();
        ASSERT_TRUE(memberDCallee != nullptr) << "Member destructor call has no callee";
        ASSERT_TRUE(memberDCallee->getNameAsString().find("Member__dtor") != std::string::npos) << "First call should be Member__dtor";

        // Verify second call is to Base__dtor
        CallExpr *baseDtorCall = dyn_cast<CallExpr>(dtorStmts[1]);
        ASSERT_TRUE(baseDtorCall != nullptr) << "Expected base destructor call second";

        FunctionDecl *baseDCallee = baseDtorCall->getDirectCallee();
        ASSERT_TRUE(baseDCallee != nullptr) << "Base destructor call has no callee";
        ASSERT_TRUE(baseDCallee->getNameAsString().find("Base__dtor") != std::string::npos) << "Second call should be Base__dtor";
}

TEST_F(InheritanceTest, ConstMemberInitialization) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Get Immutable constructor
        FunctionDecl *immutableCtor = visitor.getCtor("Immutable__ctor");
        ASSERT_TRUE(immutableCtor != nullptr) << "Immutable__ctor not found";

        // Check constructor body has const member initialization
        CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(immutableCtor->getBody());
        ASSERT_TRUE(body != nullptr) << "Immutable constructor body is null";

        // Should have 2 statements: id init (const member) + value init
        ASSERT_TRUE(body->size() >= 2) << "Expected at least 2 initialization statements";

        // Convert body to vector
        std::vector<Stmt*> stmts;
        for (Stmt *S : body->body()) {
            stmts.push_back(S);
        }

        // Verify both members are initialized (we accept any valid initialization)
        // The key is that const members are handled without compilation errors
        ASSERT_TRUE(stmts.size() >= 2) << "Expected at least 2 member initializations";
}

TEST_F(InheritanceTest, ReferenceMemberInitialization) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Get RefHolder constructor
        FunctionDecl *refHolderCtor = visitor.getCtor("RefHolder__ctor");
        ASSERT_TRUE(refHolderCtor != nullptr) << "RefHolder__ctor not found";

        // Check constructor body
        CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(refHolderCtor->getBody());
        ASSERT_TRUE(body != nullptr) << "RefHolder constructor body is null";

        // Should have 2 statements: ref init (reference member) + value init
        ASSERT_TRUE(body->size() >= 2) << "Expected at least 2 initialization statements";
}

TEST_F(InheritanceTest, SimpleDelegatingConstructor) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Get delegating constructor: Point(int) → Point__ctor_1
        FunctionDecl *delegatingCtor = visitor.getCtor("Point__ctor_1");
        ASSERT_TRUE(delegatingCtor != nullptr) << "Delegating constructor not generated";

        // Check body has exactly one statement: call to target constructor
        CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(delegatingCtor->getBody());
        ASSERT_TRUE(body != nullptr) << "Delegating constructor body is null";
        ASSERT_TRUE(body->size() == 1) << "Delegating constructor should have exactly 1 statement";

        // First statement should be call to Point__ctor (the two-param version)
        Stmt *firstStmt = *body->body_begin();
        CallExpr *targetCall = dyn_cast<CallExpr>(firstStmt);
        ASSERT_TRUE(targetCall != nullptr) << "First statement should be CallExpr to target constructor";

        // Verify it calls the target constructor
        if (FunctionDecl *callee = targetCall->getDirectCallee()) {
            std::string calleeName = callee->getNameAsString();
            ASSERT_TRUE(calleeName == "Point__ctor") << "Should call Point__ctor";
        }
}

TEST_F(InheritanceTest, DelegationChain) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Verify Data() delegates to Data(int) → Data__ctor_0 delegates to Data__ctor_1
        FunctionDecl *defaultCtor = visitor.getCtor("Data__ctor_0");
        ASSERT_TRUE(defaultCtor != nullptr) << "Default constructor not generated";

        CompoundStmt *defaultBody = dyn_cast_or_null<CompoundStmt>(defaultCtor->getBody());
        ASSERT_TRUE(defaultBody != nullptr && defaultBody->size() == 1) << "Default constructor should have 1 delegation statement";

        // Verify Data(int) delegates to Data(int, int) → Data__ctor_1 delegates to Data__ctor_2
        FunctionDecl *oneCtor = visitor.getCtor("Data__ctor_1");
        ASSERT_TRUE(oneCtor != nullptr) << "One-param constructor not generated";

        CompoundStmt *oneBody = dyn_cast_or_null<CompoundStmt>(oneCtor->getBody());
        ASSERT_TRUE(oneBody != nullptr && oneBody->size() == 1) << "One-param constructor should have 1 delegation statement";

        // Verify Data(int, int) delegates to Data(int, int, int) → Data__ctor_2 delegates to Data__ctor
        FunctionDecl *twoCtor = visitor.getCtor("Data__ctor_2");
        ASSERT_TRUE(twoCtor != nullptr) << "Two-param constructor not generated";

        CompoundStmt *twoBody = dyn_cast_or_null<CompoundStmt>(twoCtor->getBody());
        ASSERT_TRUE(twoBody != nullptr && twoBody->size() == 1) << "Two-param constructor should have 1 delegation statement";
}

TEST_F(InheritanceTest, EntitySystemScenario) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Get MeshComponent constructor
        FunctionDecl *meshCtor = visitor.getCtor("MeshComponent__ctor");
        ASSERT_TRUE(meshCtor != nullptr) << "MeshComponent__ctor not found";

        // Check constructor body
        CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(meshCtor->getBody());
        ASSERT_TRUE(body != nullptr) << "MeshComponent constructor body is null";

        // Should have multiple statements:
        // 1. Base constructor call (Component__ctor)
        // 2. Member constructor call (Transform__ctor)
        // 3. Const member initialization (vertexCount)
        ASSERT_TRUE(body->size() >= 3) << "Expected at least 3 initialization statements";

        // Get MeshComponent destructor
        FunctionDecl *meshDtor = visitor.getDtor("MeshComponent__dtor");
        ASSERT_TRUE(meshDtor != nullptr) << "MeshComponent__dtor not found";

        // Check destructor body
        CompoundStmt *dtorBody = dyn_cast_or_null<CompoundStmt>(meshDtor->getBody());
        ASSERT_TRUE(dtorBody != nullptr) << "MeshComponent destructor body is null";

        // Should have statements for member destructors and base destructor
        ASSERT_TRUE(dtorBody->size() >= 2) << "Expected member + base destructor calls";
}

TEST_F(InheritanceTest, ResourceManagerScenario) {
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
        CppToCVisitor visitor(AST->getASTContext(), builder);

        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Get FileResourceManager constructor
        FunctionDecl *fileCtor = visitor.getCtor("FileResourceManager__ctor");
        ASSERT_TRUE(fileCtor != nullptr) << "FileResourceManager__ctor not found";

        // Check constructor body
        CompoundStmt *body = dyn_cast_or_null<CompoundStmt>(fileCtor->getBody());
        ASSERT_TRUE(body != nullptr) << "FileResourceManager constructor body is null";

        // Should have:
        // 1. Base constructor call (ResourceManager__ctor)
        // 2. Member constructor call (Resource__ctor for defaultResource)
        // 3. Const member initialization (bufferSize)
        ASSERT_TRUE(body->size() >= 3) << "Expected base + member + const initializations";

        // Get FileResourceManager destructor
        FunctionDecl *fileDtor = visitor.getDtor("FileResourceManager__dtor");
        ASSERT_TRUE(fileDtor != nullptr) << "FileResourceManager__dtor not found";

        // Check destructor body
        CompoundStmt *dtorBody = dyn_cast_or_null<CompoundStmt>(fileDtor->getBody());
        ASSERT_TRUE(dtorBody != nullptr) << "FileResourceManager destructor body is null";

        // Should have member destructor + base destructor calls
        ASSERT_TRUE(dtorBody->size() >= 2) << "Expected member + base destructor calls";
}
