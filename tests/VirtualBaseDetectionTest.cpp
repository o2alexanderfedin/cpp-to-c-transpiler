// tests/VirtualBaseDetectionTest.cpp
// Unit tests for virtual base detection and analysis (Story #89)
// Following TDD: RED phase - tests written first

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualInheritanceAnalyzer.h"
#include <iostream>
#include <cassert>

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

// Test 1: Detect simple virtual inheritance
void test_DetectSimpleVirtualInheritance() {
    TEST_START("DetectSimpleVirtualInheritance");

    const char *code = R"(
        class Base {
            virtual ~Base() {}
            int x;
        };

        class Derived : public virtual Base {
            int y;
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    auto *Derived = findClass(TU, "Derived");

    ASSERT(Base, "Base class not found");
    ASSERT(Derived, "Derived class not found");

    VirtualInheritanceAnalyzer analyzer;
    analyzer.analyzeClass(Base);
    analyzer.analyzeClass(Derived);

    // Base has no virtual bases
    ASSERT(!analyzer.hasVirtualBases(Base), "Base should not have virtual bases");
    ASSERT(analyzer.getVirtualBases(Base).size() == 0, "Base should have 0 virtual bases");

    // Derived has Base as virtual base
    ASSERT(analyzer.hasVirtualBases(Derived), "Derived should have virtual bases");
    auto vbases = analyzer.getVirtualBases(Derived);
    ASSERT(vbases.size() == 1, "Derived should have 1 virtual base");
    ASSERT(vbases[0]->getNameAsString() == "Base", "Virtual base should be Base");

    // Derived needs VTT
    ASSERT(analyzer.needsVTT(Derived), "Derived should need VTT");

    TEST_PASS("DetectSimpleVirtualInheritance");
}

// Test 2: Detect diamond inheritance pattern
void test_DetectDiamondPattern() {
    TEST_START("DetectDiamondPattern");

    const char *code = R"(
        class Base {
            virtual ~Base() {}
            int b;
        };

        class Left : public virtual Base {
            int l;
        };

        class Right : public virtual Base {
            int r;
        };

        class Diamond : public Left, public Right {
            int d;
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    auto *Left = findClass(TU, "Left");
    auto *Right = findClass(TU, "Right");
    auto *Diamond = findClass(TU, "Diamond");

    ASSERT(Base, "Base class not found");
    ASSERT(Left, "Left class not found");
    ASSERT(Right, "Right class not found");
    ASSERT(Diamond, "Diamond class not found");

    VirtualInheritanceAnalyzer analyzer;
    analyzer.analyzeClass(Base);
    analyzer.analyzeClass(Left);
    analyzer.analyzeClass(Right);
    analyzer.analyzeClass(Diamond);

    // Left and Right both have Base as virtual base
    ASSERT(analyzer.hasVirtualBases(Left), "Left should have virtual bases");
    ASSERT(analyzer.hasVirtualBases(Right), "Right should have virtual bases");

    // Diamond inherits virtual base from Left and Right
    ASSERT(analyzer.hasVirtualBases(Diamond), "Diamond should have virtual bases");
    auto vbases = analyzer.getVirtualBases(Diamond);
    ASSERT(vbases.size() == 1, "Diamond should have 1 virtual base (shared Base)");
    ASSERT(vbases[0]->getNameAsString() == "Base", "Virtual base should be Base");

    // Diamond pattern detected
    ASSERT(analyzer.isDiamondPattern(Diamond), "Diamond should be detected as diamond pattern");

    // All classes except Base need VTT
    ASSERT(!analyzer.needsVTT(Base), "Base should not need VTT");
    ASSERT(analyzer.needsVTT(Left), "Left should need VTT");
    ASSERT(analyzer.needsVTT(Right), "Right should need VTT");
    ASSERT(analyzer.needsVTT(Diamond), "Diamond should need VTT");

    TEST_PASS("DetectDiamondPattern");
}

// Test 3: Non-virtual inheritance should not be detected as virtual
void test_IgnoreNonVirtualInheritance() {
    TEST_START("IgnoreNonVirtualInheritance");

    const char *code = R"(
        class Base {
            virtual ~Base() {}
            int x;
        };

        class Derived : public Base {  // NOT virtual
            int y;
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    auto *Derived = findClass(TU, "Derived");

    ASSERT(Base, "Base class not found");
    ASSERT(Derived, "Derived class not found");

    VirtualInheritanceAnalyzer analyzer;
    analyzer.analyzeClass(Base);
    analyzer.analyzeClass(Derived);

    // Derived does NOT have virtual bases
    ASSERT(!analyzer.hasVirtualBases(Derived), "Derived should not have virtual bases");
    ASSERT(analyzer.getVirtualBases(Derived).size() == 0, "Derived should have 0 virtual bases");

    // Derived does NOT need VTT
    ASSERT(!analyzer.needsVTT(Derived), "Derived should not need VTT");

    TEST_PASS("IgnoreNonVirtualInheritance");
}

// Test 4: Inheritance graph construction
void test_BuildInheritanceGraph() {
    TEST_START("BuildInheritanceGraph");

    const char *code = R"(
        class Base {
            virtual ~Base() {}
            int b;
        };

        class Left : public virtual Base {
            int l;
        };

        class Right : public virtual Base {
            int r;
        };

        class Diamond : public Left, public Right {
            int d;
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    auto *Left = findClass(TU, "Left");
    auto *Right = findClass(TU, "Right");
    auto *Diamond = findClass(TU, "Diamond");

    VirtualInheritanceAnalyzer analyzer;
    analyzer.analyzeClass(Base);
    analyzer.analyzeClass(Left);
    analyzer.analyzeClass(Right);
    analyzer.analyzeClass(Diamond);

    auto& graph = analyzer.getInheritanceGraph();

    // Base has no parents
    ASSERT(graph.getParents(Base).size() == 0, "Base should have no parents");

    // Left has Base as virtual parent
    auto leftParents = graph.getParents(Left);
    ASSERT(leftParents.size() == 1, "Left should have 1 parent");
    ASSERT(leftParents[0].baseClass->getNameAsString() == "Base", "Left's parent should be Base");
    ASSERT(leftParents[0].isVirtual, "Left->Base should be virtual");

    // Right has Base as virtual parent
    auto rightParents = graph.getParents(Right);
    ASSERT(rightParents.size() == 1, "Right should have 1 parent");
    ASSERT(rightParents[0].baseClass->getNameAsString() == "Base", "Right's parent should be Base");
    ASSERT(rightParents[0].isVirtual, "Right->Base should be virtual");

    // Diamond has Left and Right as non-virtual parents
    auto diamondParents = graph.getParents(Diamond);
    ASSERT(diamondParents.size() == 2, "Diamond should have 2 parents");

    // Find paths from Diamond to Base
    auto paths = graph.findPaths(Diamond, Base);
    ASSERT(paths.size() == 2, "Should be 2 paths from Diamond to Base");

    TEST_PASS("BuildInheritanceGraph");
}

// Test 5: Most-derived analysis
void test_MostDerivedAnalysis() {
    TEST_START("MostDerivedAnalysis");

    const char *code = R"(
        class Base {
            virtual ~Base() {}
        };

        class Derived : public virtual Base {
        };

        class MostDerived : public Derived {
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    auto *Derived = findClass(TU, "Derived");
    auto *MostDerived = findClass(TU, "MostDerived");

    VirtualInheritanceAnalyzer analyzer;
    analyzer.analyzeClass(Base);
    analyzer.analyzeClass(Derived);
    analyzer.analyzeClass(MostDerived);

    // When constructing Derived directly, it's most-derived
    ASSERT(analyzer.isMostDerived(Derived, Derived), "Derived should be most-derived when constructing Derived");

    // When constructing MostDerived, Derived is NOT most-derived
    ASSERT(!analyzer.isMostDerived(Derived, MostDerived), "Derived should not be most-derived when constructing MostDerived");

    // MostDerived is always most-derived when constructing itself
    ASSERT(analyzer.isMostDerived(MostDerived, MostDerived), "MostDerived should be most-derived when constructing MostDerived");

    TEST_PASS("MostDerivedAnalysis");
}

// Test 6: Multiple virtual bases
void test_MultipleVirtualBases() {
    TEST_START("MultipleVirtualBases");

    const char *code = R"(
        class Base1 {
            virtual ~Base1() {}
            int b1;
        };

        class Base2 {
            virtual ~Base2() {}
            int b2;
        };

        class Derived : public virtual Base1, public virtual Base2 {
            int d;
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base1 = findClass(TU, "Base1");
    auto *Base2 = findClass(TU, "Base2");
    auto *Derived = findClass(TU, "Derived");

    VirtualInheritanceAnalyzer analyzer;
    analyzer.analyzeClass(Base1);
    analyzer.analyzeClass(Base2);
    analyzer.analyzeClass(Derived);

    // Derived has two virtual bases
    ASSERT(analyzer.hasVirtualBases(Derived), "Derived should have virtual bases");
    auto vbases = analyzer.getVirtualBases(Derived);
    ASSERT(vbases.size() == 2, "Derived should have 2 virtual bases");

    // Derived needs VTT
    ASSERT(analyzer.needsVTT(Derived), "Derived should need VTT");

    TEST_PASS("MultipleVirtualBases");
}

// Test 7: Indirect virtual bases
void test_IndirectVirtualBases() {
    TEST_START("IndirectVirtualBases");

    const char *code = R"(
        class Base {
            virtual ~Base() {}
        };

        class Middle : public virtual Base {
        };

        class Derived : public Middle {
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    auto *Middle = findClass(TU, "Middle");
    auto *Derived = findClass(TU, "Derived");

    VirtualInheritanceAnalyzer analyzer;
    analyzer.analyzeClass(Base);
    analyzer.analyzeClass(Middle);
    analyzer.analyzeClass(Derived);

    // Middle has direct virtual base
    ASSERT(analyzer.hasVirtualBases(Middle), "Middle should have virtual bases");

    // Derived has indirect virtual base (through Middle)
    ASSERT(analyzer.hasVirtualBases(Derived), "Derived should have virtual bases");
    auto vbases = analyzer.getVirtualBases(Derived);
    ASSERT(vbases.size() == 1, "Derived should have 1 virtual base");
    ASSERT(vbases[0]->getNameAsString() == "Base", "Virtual base should be Base");

    // Both need VTT
    ASSERT(analyzer.needsVTT(Middle), "Middle should need VTT");
    ASSERT(analyzer.needsVTT(Derived), "Derived should need VTT");

    TEST_PASS("IndirectVirtualBases");
}

// Test 8: Mixed virtual and non-virtual inheritance
void test_MixedInheritance() {
    TEST_START("MixedInheritance");

    const char *code = R"(
        class VirtualBase {
            virtual ~VirtualBase() {}
            int vb;
        };

        class NonVirtualBase {
            virtual ~NonVirtualBase() {}
            int nvb;
        };

        class Derived : public virtual VirtualBase, public NonVirtualBase {
            int d;
        };
    )";

    auto AST = buildAST(code);
    ASSERT(AST, "Failed to build AST");

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *VirtualBase = findClass(TU, "VirtualBase");
    auto *NonVirtualBase = findClass(TU, "NonVirtualBase");
    auto *Derived = findClass(TU, "Derived");

    VirtualInheritanceAnalyzer analyzer;
    analyzer.analyzeClass(VirtualBase);
    analyzer.analyzeClass(NonVirtualBase);
    analyzer.analyzeClass(Derived);

    // Derived has one virtual base
    ASSERT(analyzer.hasVirtualBases(Derived), "Derived should have virtual bases");
    auto vbases = analyzer.getVirtualBases(Derived);
    ASSERT(vbases.size() == 1, "Derived should have 1 virtual base");
    ASSERT(vbases[0]->getNameAsString() == "VirtualBase", "Virtual base should be VirtualBase");

    // Verify inheritance graph distinguishes virtual from non-virtual
    auto& graph = analyzer.getInheritanceGraph();
    auto parents = graph.getParents(Derived);
    ASSERT(parents.size() == 2, "Derived should have 2 parents");

    bool foundVirtual = false;
    bool foundNonVirtual = false;
    for (const auto& parent : parents) {
        if (parent.baseClass->getNameAsString() == "VirtualBase") {
            ASSERT(parent.isVirtual, "VirtualBase should be virtual");
            foundVirtual = true;
        } else {
            ASSERT(!parent.isVirtual, "NonVirtualBase should not be virtual");
            foundNonVirtual = true;
        }
    }
    ASSERT(foundVirtual && foundNonVirtual, "Should find both virtual and non-virtual bases");

    // Derived needs VTT
    ASSERT(analyzer.needsVTT(Derived), "Derived should need VTT");

    TEST_PASS("MixedInheritance");
}

int main() {
    std::cout << "=== Virtual Base Detection Tests (Story #89) ===" << std::endl;

    test_DetectSimpleVirtualInheritance();
    test_DetectDiamondPattern();
    test_IgnoreNonVirtualInheritance();
    test_BuildInheritanceGraph();
    test_MostDerivedAnalysis();
    test_MultipleVirtualBases();
    test_IndirectVirtualBases();
    test_MixedInheritance();

    std::cout << "\n=== All tests passed! ===" << std::endl;
    return 0;
}
