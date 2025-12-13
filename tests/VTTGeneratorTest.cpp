// tests/VTTGeneratorTest.cpp
// Unit tests for VTT (Virtual Table Tables) generation (Story #91)
// Following TDD: RED phase - tests written first

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VTTGenerator.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/VirtualInheritanceAnalyzer.h"
#include <iostream>
#include <cassert>
#include <sstream>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Test helper macros
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
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
void test_SimpleVTTGeneration() {
    TEST_START("SimpleVTTGeneration");

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
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    auto *Derived = findClass(TU, "Derived");

    ASSERT(Base && Derived, "Classes should be found");

    viAnalyzer.analyzeClass(Base);
    viAnalyzer.analyzeClass(Derived);

    // Generate VTT for Derived class
    std::string vttCode = vttGen.generateVTT(Derived);

    // Verify VTT array is generated
    ASSERT(!vttCode.empty(), "VTT code should not be empty");
    ASSERT(vttCode.find("__vtt_Derived") != std::string::npos,
           "VTT should have name __vtt_Derived");
    ASSERT(vttCode.find("const void*") != std::string::npos ||
           vttCode.find("const void *") != std::string::npos,
           "VTT should be array of const void*");

    TEST_PASS("SimpleVTTGeneration");
}

// Test 2: Diamond inheritance - VTT with multiple entries
void test_DiamondVTTGeneration() {
    TEST_START("DiamondVTTGeneration");

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
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    auto *Left = findClass(TU, "Left");
    auto *Right = findClass(TU, "Right");
    auto *Diamond = findClass(TU, "Diamond");

    ASSERT(Base && Left && Right && Diamond, "All classes should be found");

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
    ASSERT(vttCode.find("__vtt_Diamond") != std::string::npos,
           "VTT should be named __vtt_Diamond");
    ASSERT(vttCode.find("vtable") != std::string::npos,
           "VTT should reference vtables");

    TEST_PASS("DiamondVTTGeneration");
}

// Test 3: VTT entry count - verify correct number of entries
void test_VTTEntryCount() {
    TEST_START("VTTEntryCount");

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
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");

    ASSERT(Derived, "Derived class not found");

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(Derived);

    // Get VTT entry count
    size_t entryCount = vttGen.getVTTEntryCount(Derived);

    // Derived with one virtual base should have at least 2 entries
    // (primary vtable + virtual base vtable)
    ASSERT(entryCount >= 2, "VTT should have at least 2 entries");

    TEST_PASS("VTTEntryCount");
}

// Test 4: Primary vtable entry - first entry is primary vtable
void test_PrimaryVtableEntry() {
    TEST_START("PrimaryVtableEntry");

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
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");

    ASSERT(Derived, "Derived class not found");

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(Derived);

    // Get VTT entries
    auto entries = vttGen.getVTTEntries(Derived);

    ASSERT(!entries.empty(), "VTT entries should not be empty");
    ASSERT(entries[0].find("Derived") != std::string::npos,
           "First entry should reference Derived's primary vtable");

    TEST_PASS("PrimaryVtableEntry");
}

// Test 5: VTT ordering - verify Itanium ABI ordering
void test_VTTOrdering() {
    TEST_START("VTTOrdering");

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
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    auto *Left = findClass(TU, "Left");
    auto *Right = findClass(TU, "Right");
    auto *Diamond = findClass(TU, "Diamond");

    ASSERT(Base && Left && Right && Diamond, "All classes should be found");

    viAnalyzer.analyzeClass(Base);
    viAnalyzer.analyzeClass(Left);
    viAnalyzer.analyzeClass(Right);
    viAnalyzer.analyzeClass(Diamond);

    // Get VTT entries
    auto entries = vttGen.getVTTEntries(Diamond);

    // Verify ordering: Primary, then base constructors, then virtual bases
    ASSERT(entries.size() >= 3, "Diamond VTT should have multiple entries");

    // First entry should be primary vtable
    ASSERT(entries[0].find("Diamond") != std::string::npos,
           "First entry should be Diamond primary vtable");

    TEST_PASS("VTTOrdering");
}

// Test 6: VTT code generation - full C code output
void test_VTTCodeGeneration() {
    TEST_START("VTTCodeGeneration");

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
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");

    ASSERT(Derived, "Derived class not found");

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(Derived);

    // Generate VTT code
    std::string vttCode = vttGen.generateVTT(Derived);

    // Verify structure: const void* __vtt_ClassName[] = { ... };
    ASSERT(vttCode.find("const void*") != std::string::npos ||
           vttCode.find("const void *") != std::string::npos,
           "VTT should be const void* array");
    ASSERT(vttCode.find("__vtt_Derived[]") != std::string::npos ||
           vttCode.find("__vtt_Derived[") != std::string::npos,
           "VTT should be named __vtt_Derived");
    ASSERT(vttCode.find("{") != std::string::npos &&
           vttCode.find("}") != std::string::npos,
           "VTT should have array initializer");

    TEST_PASS("VTTCodeGeneration");
}

// Test 7: No virtual bases - should not generate VTT
void test_NoVirtualBasesNoVTT() {
    TEST_START("NoVirtualBasesNoVTT");

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
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");

    ASSERT(Derived, "Derived class not found");

    viAnalyzer.analyzeClass(findClass(TU, "Base"));
    viAnalyzer.analyzeClass(Derived);

    // Should not generate VTT for non-virtual inheritance
    std::string vttCode = vttGen.generateVTT(Derived);

    ASSERT(vttCode.empty() || vttCode.find("// No VTT needed") != std::string::npos,
           "Non-virtual inheritance should not generate VTT");

    TEST_PASS("NoVirtualBasesNoVTT");
}

// Test 8: Complex hierarchy - multiple virtual bases
void test_ComplexHierarchyVTT() {
    TEST_START("ComplexHierarchyVTT");

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
    ASSERT(AST, "Failed to build AST");

    VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
    VirtualInheritanceAnalyzer viAnalyzer;
    VTTGenerator vttGen(AST->getASTContext(), viAnalyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base1 = findClass(TU, "Base1");
    auto *Base2 = findClass(TU, "Base2");
    auto *Derived = findClass(TU, "Derived");

    ASSERT(Base1 && Base2 && Derived, "All classes should be found");

    viAnalyzer.analyzeClass(Base1);
    viAnalyzer.analyzeClass(Base2);
    viAnalyzer.analyzeClass(Derived);

    // Generate VTT
    std::string vttCode = vttGen.generateVTT(Derived);

    // Should have entries for both virtual bases
    ASSERT(!vttCode.empty(), "VTT should be generated");

    auto entries = vttGen.getVTTEntries(Derived);
    ASSERT(entries.size() >= 3, "VTT should have entries for primary + 2 virtual bases");

    TEST_PASS("ComplexHierarchyVTT");
}

int main() {
    std::cout << "=== VTT (Virtual Table Tables) Generation Tests (Story #91) ===" << std::endl;
    std::cout << "TDD Phase: RED - All tests should FAIL initially\n" << std::endl;

    test_SimpleVTTGeneration();
    test_DiamondVTTGeneration();
    test_VTTEntryCount();
    test_PrimaryVtableEntry();
    test_VTTOrdering();
    test_VTTCodeGeneration();
    test_NoVirtualBasesNoVTT();
    test_ComplexHierarchyVTT();

    std::cout << "\n=== All tests passed! ===" << std::endl;
    return 0;
}
