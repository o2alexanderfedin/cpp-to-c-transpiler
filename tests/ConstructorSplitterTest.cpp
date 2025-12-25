// tests/ConstructorSplitterTest.cpp
// Unit tests for Constructor Splitting into C1/C2 variants (Story #92)
// Following TDD: RED phase - tests written first

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/ConstructorSplitter.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/VirtualInheritanceAnalyzer.h"
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
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

// Test fixture
class ConstructorSplitterTest : public ::testing::Test {
protected:
};

TEST_F(ConstructorSplitterTest, NeedsSplitting) {
    const char *code = R"(
            class Base { public: virtual ~Base() {} };
            class Derived : public virtual Base { public: int d; };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(Derived);

        // Derived has virtual base, so needs C1/C2 split
        ASSERT_TRUE(splitter.needsSplitting(Derived)) << "Class with virtual base should need splitting";
}

TEST_F(ConstructorSplitterTest, GenerateC1Constructor) {
    const char *code = R"(
            class Base { public: virtual ~Base() {} int b; };
            class Derived : public virtual Base {
            public:
                Derived() : b_data(0) {}
                int b_data;
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(Derived);

        // Get C1 constructor code
        std::string c1Code = splitter.generateC1Constructor(Derived);

        // C1 should construct virtual bases
        ASSERT_TRUE(!c1Code.empty()) << "C1 constructor should be generated";
        ASSERT_TRUE(c1Code.find("_C1") != std::string::npos) << "C1 constructor should have _C1 suffix";
        ASSERT_TRUE(c1Code.find("vtt") != std::string::npos ||
               c1Code.find("VTT") != std::string::npos) << "C1 should reference VTT";
}

TEST_F(ConstructorSplitterTest, GenerateC2Constructor) {
    const char *code = R"(
            class Base { public: virtual ~Base() {} };
            class Derived : public virtual Base {
            public:
                Derived() {}
                int d;
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

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
        ASSERT_TRUE(!c2Code.empty()) << "C2 constructor should be generated";
        ASSERT_TRUE(c2Code.find("_C2") != std::string::npos) << "C2 constructor should have _C2 suffix";
}

TEST_F(ConstructorSplitterTest, DiamondC1ConstructsBaseOnce) {
    const char *code = R"(
            class Base { public: virtual ~Base() {} };
            class Left : public virtual Base { public: int l; };
            class Right : public virtual Base { public: int r; };
            class Diamond : public Left, public Right { public: int d; };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Diamond = findClass(TU, "Diamond");

        ASSERT_TRUE(Diamond) << "Diamond class not found";

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(findClass(TU, "Left"));
        viAnalyzer.analyzeClass(findClass(TU, "Right"));
        viAnalyzer.analyzeClass(Diamond);

        std::string c1Code = splitter.generateC1Constructor(Diamond);

        // Diamond C1 should construct Base (virtual base)
        ASSERT_TRUE(c1Code.find("Base") != std::string::npos) << "Diamond C1 should reference Base construction";
}

TEST_F(ConstructorSplitterTest, C1CallsBaseC2) {
    const char *code = R"(
            class Base { public: virtual ~Base() {} };
            class Left : public virtual Base { public: int l; };
            class Right : public virtual Base { public: int r; };
            class Diamond : public Left, public Right { public: int d; };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Diamond = findClass(TU, "Diamond");

        ASSERT_TRUE(Diamond) << "Diamond class not found";

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(findClass(TU, "Left"));
        viAnalyzer.analyzeClass(findClass(TU, "Right"));
        viAnalyzer.analyzeClass(Diamond);

        std::string c1Code = splitter.generateC1Constructor(Diamond);

        // Diamond C1 should call Left_C2 and Right_C2 (not C1)
        ASSERT_TRUE(c1Code.find("_C2") != std::string::npos) << "C1 should call base C2 constructors";
}

TEST_F(ConstructorSplitterTest, VTTParameter) {
    const char *code = R"(
            class Base { public: virtual ~Base() {} };
            class Derived : public virtual Base {
            public:
                Derived() {}
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(Derived);

        std::string c1Code = splitter.generateC1Constructor(Derived);

        // C1 should have VTT parameter
        ASSERT_TRUE(c1Code.find("vtt") != std::string::npos ||
               c1Code.find("const void**") != std::string::npos) << "C1 should have VTT parameter";
}

TEST_F(ConstructorSplitterTest, NoSplittingWithoutVirtualBases) {
    const char *code = R"(
            class Base { public: virtual ~Base() {} };
            class Derived : public Base { public: int d; };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(Derived);

        // Non-virtual inheritance doesn't need splitting
        ASSERT_TRUE(!splitter.needsSplitting(Derived)) << "Non-virtual inheritance should not need splitting";
}

TEST_F(ConstructorSplitterTest, VtableAssignmentFromVTT) {
    const char *code = R"(
            class Base { public: virtual ~Base() {} };
            class Derived : public virtual Base {
            public:
                virtual void foo() {}
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        ConstructorSplitter splitter(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(Derived);

        std::string c1Code = splitter.generateC1Constructor(Derived);

        // C1 should set vtable pointers from VTT
        ASSERT_TRUE(c1Code.find("vptr") != std::string::npos ||
               c1Code.find("vtable") != std::string::npos) << "C1 should assign vtable pointers";
}
