// tests/VTTGeneratorTest.cpp
// Unit tests for VTT (Virtual Table Tables) generation (Story #91)
// Following TDD: RED phase - tests written first

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VTTGenerator.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/VirtualInheritanceAnalyzer.h"
#include <cassert>
#include <sstream>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Test helper macros
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        std::cerr << "  Condition: " #cond << std::endl; \
        return; \
    }

// Helper function to find class by name
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

// Test 1: Simple virtual inheritance - VTT with basic entries

// Test fixture
class VTTGeneratorTest : public ::testing::Test {
protected:
};

TEST_F(VTTGeneratorTest, SimpleVTTGeneration) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
                int b;
            };

            class Derived : public virtual Base {
            public:
                int d;
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Base && Derived) << "Classes should be found";

        viAnalyzer.analyzeClass(Base);
        viAnalyzer.analyzeClass(Derived);

        // Generate VTT for Derived class
        std::string vttCode = vttGen.generateVTT(Derived);

        // Verify VTT array is generated
        ASSERT_TRUE(!vttCode.empty()) << "VTT code should not be empty";
        ASSERT_TRUE(vttCode.find("__vtt_Derived") != std::string::npos) << "VTT should have name __vtt_Derived";
        ASSERT_TRUE(vttCode.find("const void*") != std::string::npos ||
               vttCode.find("const void *") != std::string::npos) << "VTT should be array of const void*";
}

TEST_F(VTTGeneratorTest, DiamondVTTGeneration) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
                int b;
            };

            class Left : public virtual Base {
            public:
                int l;
            };

            class Right : public virtual Base {
            public:
                int r;
            };

            class Diamond : public Left, public Right {
            public:
                int d;
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Left = findClass(TU, "Left");
        auto *Right = findClass(TU, "Right");
        auto *Diamond = findClass(TU, "Diamond");

        ASSERT_TRUE(Base && Left && Right && Diamond) << "All classes should be found";

        viAnalyzer.analyzeClass(Base);
        viAnalyzer.analyzeClass(Left);
        viAnalyzer.analyzeClass(Right);
        viAnalyzer.analyzeClass(Diamond);

        // Generate VTT for Diamond class
        std::string vttCode = vttGen.generateVTT(Diamond);

        // Diamond VTT should have entries for:
        // - Primary vtable
        // - Left base constructor vtable
        // - Right base constructor vtable
        // - Base virtual base vtable
        ASSERT_TRUE(vttCode.find("__vtt_Diamond") != std::string::npos) << "VTT should be named __vtt_Diamond";
        ASSERT_TRUE(vttCode.find("vtable") != std::string::npos) << "VTT should reference vtables";
}

TEST_F(VTTGeneratorTest, VTTEntryCount) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
            };

            class Derived : public virtual Base {
            public:
                virtual void foo() {}
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Derived) << "Derived class not found";

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(Derived);

        // Get VTT entry count
        size_t entryCount = vttGen.getVTTEntryCount(Derived);

        // Derived with one virtual base should have at least 2 entries
        // (primary vtable + virtual base vtable)
        ASSERT_TRUE(entryCount >= 2) << "VTT should have at least 2 entries";
}

TEST_F(VTTGeneratorTest, PrimaryVtableEntry) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
            };

            class Derived : public virtual Base {
            public:
                int d;
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Derived) << "Derived class not found";

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(Derived);

        // Get VTT entries
        auto entries = vttGen.getVTTEntries(Derived);

        ASSERT_TRUE(!entries.empty()) << "VTT entries should not be empty";
        ASSERT_TRUE(entries[0].find("Derived") != std::string::npos) << "First entry should reference Derived's primary vtable";
}

TEST_F(VTTGeneratorTest, VTTOrdering) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
            };

            class Left : public virtual Base {
            public:
                int l;
            };

            class Right : public virtual Base {
            public:
                int r;
            };

            class Diamond : public Left, public Right {
            public:
                int d;
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Left = findClass(TU, "Left");
        auto *Right = findClass(TU, "Right");
        auto *Diamond = findClass(TU, "Diamond");

        ASSERT_TRUE(Base && Left && Right && Diamond) << "All classes should be found";

        viAnalyzer.analyzeClass(Base);
        viAnalyzer.analyzeClass(Left);
        viAnalyzer.analyzeClass(Right);
        viAnalyzer.analyzeClass(Diamond);

        // Get VTT entries
        auto entries = vttGen.getVTTEntries(Diamond);

        // Verify ordering: Primary, then base constructors, then virtual bases
        ASSERT_TRUE(entries.size() >= 3) << "Diamond VTT should have multiple entries";

        // First entry should be primary vtable
        ASSERT_TRUE(entries[0].find("Diamond") != std::string::npos) << "First entry should be Diamond primary vtable";
}

TEST_F(VTTGeneratorTest, VTTCodeGeneration) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
            };

            class Derived : public virtual Base {
            public:
                virtual void foo() {}
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Derived) << "Derived class not found";

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(Derived);

        // Generate VTT code
        std::string vttCode = vttGen.generateVTT(Derived);

        // Verify structure: const void* __vtt_ClassName[] = { ... };
        ASSERT_TRUE(vttCode.find("const void*") != std::string::npos ||
               vttCode.find("const void *") != std::string::npos) << "VTT should be const void* array";
        ASSERT_TRUE(vttCode.find("__vtt_Derived[]") != std::string::npos ||
               vttCode.find("__vtt_Derived[") != std::string::npos) << "VTT should be named __vtt_Derived";
        ASSERT_TRUE(vttCode.find("{") != std::string::npos &&
               vttCode.find("}") != std::string::npos) << "VTT should have array initializer";
}

TEST_F(VTTGeneratorTest, NoVirtualBasesNoVTT) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
            };

            class Derived : public Base {  // NOT virtual
            public:
                int d;
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Derived) << "Derived class not found";

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(Derived);

        // Should not generate VTT for non-virtual inheritance
        std::string vttCode = vttGen.generateVTT(Derived);

        ASSERT_TRUE(vttCode.empty() || vttCode.find("// No VTT needed") != std::string::npos) << "Non-virtual inheritance should not generate VTT";
}

TEST_F(VTTGeneratorTest, ComplexHierarchyVTT) {
    const char *code = R"(
            class Base1 {
            public:
                virtual ~Base1() {}
            };

            class Base2 {
            public:
                virtual ~Base2() {}
            };

            class Derived : public virtual Base1, public virtual Base2 {
            public:
                int d;
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base1 = findClass(TU, "Base1");
        auto *Base2 = findClass(TU, "Base2");
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Base1 && Base2 && Derived) << "All classes should be found";

        viAnalyzer.analyzeClass(Base1);
        viAnalyzer.analyzeClass(Base2);
        viAnalyzer.analyzeClass(Derived);

        // Generate VTT
        std::string vttCode = vttGen.generateVTT(Derived);

        // Should have entries for both virtual bases
        ASSERT_TRUE(!vttCode.empty()) << "VTT should be generated";

        auto entries = vttGen.getVTTEntries(Derived);
        ASSERT_TRUE(entries.size() >= 3) << "VTT should have entries for primary + 2 virtual bases";
}
