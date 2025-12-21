// tests/ConstructorSplitterTest_GTest.cpp
// Migrated from ConstructorSplitterTest.cpp to Google Test framework
// Unit tests for Constructor Splitting into C1/C2 variants (Story #92)

#include <gtest/gtest.h>
#include <clang/AST/ASTContext.h>
#include <clang/AST/Decl.h>
#include <clang/AST/DeclCXX.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include "../include/ConstructorSplitter.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/VirtualInheritanceAnalyzer.h"
#include <memory>
#include <string>

using namespace clang;

// Test fixture for Constructor Splitter tests
class ConstructorSplitterTestFixture : public ::testing::Test {
protected:
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
};

// Test 1: Classes with virtual bases need C1/C2 splitting
TEST_F(ConstructorSplitterTestFixture, NeedsSplitting) {
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
    ASSERT_NE(Derived, nullptr) << "Derived class not found";

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(Derived);

    EXPECT_TRUE(splitter.needsSplitting(Derived))
        << "Class with virtual base should need splitting";
}

// Test 2: Generate C1 (complete object) constructor
TEST_F(ConstructorSplitterTestFixture, GenerateC1Constructor) {
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
    ASSERT_NE(Derived, nullptr) << "Derived class not found";

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(Derived);

    std::string c1Code = splitter.generateC1Constructor(Derived);

    ASSERT_FALSE(c1Code.empty()) << "C1 constructor should be generated";
    EXPECT_NE(c1Code.find("_C1"), std::string::npos) << "C1 constructor should have _C1 suffix";
    EXPECT_TRUE(c1Code.find("vtt") != std::string::npos ||
                c1Code.find("VTT") != std::string::npos)
        << "C1 should reference VTT";
}

// Test 3: Generate C2 (base object) constructor
TEST_F(ConstructorSplitterTestFixture, GenerateC2Constructor) {
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

    std::string c2Code = splitter.generateC2Constructor(Derived);

    ASSERT_FALSE(c2Code.empty()) << "C2 constructor should be generated";
    EXPECT_NE(c2Code.find("_C2"), std::string::npos) << "C2 constructor should have _C2 suffix";
}

// Test 4: Diamond inheritance - C1 constructs Base once
TEST_F(ConstructorSplitterTestFixture, DiamondC1ConstructsBaseOnce) {
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
    ASSERT_NE(Diamond, nullptr) << "Diamond class not found";

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(findClass(TU, "Left"));
    viAnalyzer.analyzeClass(findClass(TU, "Right"));
    viAnalyzer.analyzeClass(Diamond);

    std::string c1Code = splitter.generateC1Constructor(Diamond);

    EXPECT_NE(c1Code.find("Base"), std::string::npos)
        << "Diamond C1 should reference Base construction";
}

// Test 5: C1 calls base C2 constructors (not C1)
TEST_F(ConstructorSplitterTestFixture, C1CallsBaseC2) {
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
    ASSERT_NE(Diamond, nullptr) << "Diamond class not found";

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(findClass(TU, "Left"));
    viAnalyzer.analyzeClass(findClass(TU, "Right"));
    viAnalyzer.analyzeClass(Diamond);

    std::string c1Code = splitter.generateC1Constructor(Diamond);

    EXPECT_NE(c1Code.find("_C2"), std::string::npos)
        << "C1 should call base C2 constructors";
}

// Test 6: VTT parameter passed to constructors
TEST_F(ConstructorSplitterTestFixture, VTTParameter) {
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

    EXPECT_TRUE(c1Code.find("vtt") != std::string::npos ||
                c1Code.find("const void**") != std::string::npos)
        << "C1 should have VTT parameter";
}

// Test 7: No splitting for classes without virtual bases
TEST_F(ConstructorSplitterTestFixture, NoSplittingWithoutVirtualBases) {
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

    EXPECT_FALSE(splitter.needsSplitting(Derived))
        << "Non-virtual inheritance should not need splitting";
}

// Test 8: Vtable assignment from VTT
TEST_F(ConstructorSplitterTestFixture, VtableAssignmentFromVTT) {
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

    EXPECT_TRUE(c1Code.find("vptr") != std::string::npos ||
                c1Code.find("vtable") != std::string::npos)
        << "C1 should assign vtable pointers";
}
