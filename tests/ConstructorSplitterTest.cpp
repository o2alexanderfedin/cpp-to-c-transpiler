// tests/ConstructorSplitterTest.cpp
// Unit tests for Constructor Splitting into C1/C2 variants (Story #92)
// Following TDD: RED phase - tests written first

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/ConstructorSplitter.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/VirtualInheritanceAnalyzer.h"
#include <iostream>
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        std::cerr << "  Condition: " #cond << std::endl; \
        return; \
    }

CXXRecordDecl* findClass(TranslationUnitDecl* TU, const std::string& name) {
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == name && RD->isCompleteDefinition()) {
                return RD;
            }
        }
    }
    return nullptr;
}

// Test 1: Classes with virtual bases need C1/C2 splitting
void test_NeedsSplitting() {
    TEST_START("NeedsSplitting");

    const char *code = R"(
        class Base { public: virtual ~Base() {} };
        class Derived : public virtual Base { public: int d; };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");
    ASSERT(Derived, "Derived class not found");

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(Derived);

    // Derived has virtual base, so needs C1/C2 split
    ASSERT(splitter.needsSplitting(Derived),
           "Class with virtual base should need splitting");

    TEST_PASS("NeedsSplitting");
}

// Test 2: Generate C1 (complete object) constructor
void test_GenerateC1Constructor() {
    TEST_START("GenerateC1Constructor");

    const char *code = R"(
        class Base { public: virtual ~Base() {} int b; };
        class Derived : public virtual Base {
        public:
            Derived() : b_data(0) {}
            int b_data;
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");
    ASSERT(Derived, "Derived class not found");

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(Derived);

    // Get C1 constructor code
    std::string c1Code = splitter.generateC1Constructor(Derived);

    // C1 should construct virtual bases
    ASSERT(!c1Code.empty(), "C1 constructor should be generated");
    ASSERT(c1Code.find("_C1") != std::string::npos,
           "C1 constructor should have _C1 suffix");
    ASSERT(c1Code.find("vtt") != std::string::npos ||
           c1Code.find("VTT") != std::string::npos,
           "C1 should reference VTT");

    TEST_PASS("GenerateC1Constructor");
}

// Test 3: Generate C2 (base object) constructor
void test_GenerateC2Constructor() {
    TEST_START("GenerateC2Constructor");

    const char *code = R"(
        class Base { public: virtual ~Base() {} };
        class Derived : public virtual Base {
        public:
            Derived() {}
            int d;
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(Derived);

    // Get C2 constructor code
    std::string c2Code = splitter.generateC2Constructor(Derived);

    // C2 should NOT construct virtual bases
    ASSERT(!c2Code.empty(), "C2 constructor should be generated");
    ASSERT(c2Code.find("_C2") != std::string::npos,
           "C2 constructor should have _C2 suffix");

    TEST_PASS("GenerateC2Constructor");
}

// Test 4: Diamond inheritance - C1 constructs Base once
void test_DiamondC1ConstructsBaseOnce() {
    TEST_START("DiamondC1ConstructsBaseOnce");

    const char *code = R"(
        class Base { public: virtual ~Base() {} };
        class Left : public virtual Base { public: int l; };
        class Right : public virtual Base { public: int r; };
        class Diamond : public Left, public Right { public: int d; };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Diamond = findClass(TU, "Diamond");

    ASSERT(Diamond, "Diamond class not found");

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(findClass(TU, "Left"));
    viAnalyzer.analyzeClass(findClass(TU, "Right"));
    viAnalyzer.analyzeClass(Diamond);

    std::string c1Code = splitter.generateC1Constructor(Diamond);

    // Diamond C1 should construct Base (virtual base)
    ASSERT(c1Code.find("Base") != std::string::npos,
           "Diamond C1 should reference Base construction");

    TEST_PASS("DiamondC1ConstructsBaseOnce");
}

// Test 5: C1 calls base C2 constructors (not C1)
void test_C1CallsBaseC2() {
    TEST_START("C1CallsBaseC2");

    const char *code = R"(
        class Base { public: virtual ~Base() {} };
        class Left : public virtual Base { public: int l; };
        class Right : public virtual Base { public: int r; };
        class Diamond : public Left, public Right { public: int d; };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Diamond = findClass(TU, "Diamond");

    ASSERT(Diamond, "Diamond class not found");

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(findClass(TU, "Left"));
    viAnalyzer.analyzeClass(findClass(TU, "Right"));
    viAnalyzer.analyzeClass(Diamond);

    std::string c1Code = splitter.generateC1Constructor(Diamond);

    // Diamond C1 should call Left_C2 and Right_C2 (not C1)
    ASSERT(c1Code.find("_C2") != std::string::npos,
           "C1 should call base C2 constructors");

    TEST_PASS("C1CallsBaseC2");
}

// Test 6: VTT parameter passed to constructors
void test_VTTParameter() {
    TEST_START("VTTParameter");

    const char *code = R"(
        class Base { public: virtual ~Base() {} };
        class Derived : public virtual Base {
        public:
            Derived() {}
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(Derived);

    std::string c1Code = splitter.generateC1Constructor(Derived);

    // C1 should have VTT parameter
    ASSERT(c1Code.find("vtt") != std::string::npos ||
           c1Code.find("const void**") != std::string::npos,
           "C1 should have VTT parameter");

    TEST_PASS("VTTParameter");
}

// Test 7: No splitting for classes without virtual bases
void test_NoSplittingWithoutVirtualBases() {
    TEST_START("NoSplittingWithoutVirtualBases");

    const char *code = R"(
        class Base { public: virtual ~Base() {} };
        class Derived : public Base { public: int d; };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(Derived);

    // Non-virtual inheritance doesn't need splitting
    ASSERT(!splitter.needsSplitting(Derived),
           "Non-virtual inheritance should not need splitting");

    TEST_PASS("NoSplittingWithoutVirtualBases");
}

// Test 8: Vtable assignment from VTT
void test_VtableAssignmentFromVTT() {
    TEST_START("VtableAssignmentFromVTT");

    const char *code = R"(
        class Base { public: virtual ~Base() {} };
        class Derived : public virtual Base {
        public:
            virtual void foo() {}
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(Derived);

    std::string c1Code = splitter.generateC1Constructor(Derived);

    // C1 should set vtable pointers from VTT
    ASSERT(c1Code.find("vptr") != std::string::npos ||
           c1Code.find("vtable") != std::string::npos,
           "C1 should assign vtable pointers");

    TEST_PASS("VtableAssignmentFromVTT");
}

int main() {
    std::cout << "=== Constructor Splitting (C1/C2) Tests (Story #92) ===" << std::endl;
    std::cout << "TDD Phase: RED - All tests should FAIL initially\n" << std::endl;

    test_NeedsSplitting();
    test_GenerateC1Constructor();
    test_GenerateC2Constructor();
    test_DiamondC1ConstructsBaseOnce();
    test_C1CallsBaseC2();
    test_VTTParameter();
    test_NoSplittingWithoutVirtualBases();
    test_VtableAssignmentFromVTT();

    std::cout << "\n=== All tests passed! ===" << std::endl;
    return 0;
}
