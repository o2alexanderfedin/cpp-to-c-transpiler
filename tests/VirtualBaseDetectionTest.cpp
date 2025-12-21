// tests/VirtualBaseDetectionTest.cpp
// Unit tests for virtual base detection and analysis (Story #89)
// Following TDD: RED phase - tests written first

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualInheritanceAnalyzer.h"
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Test helper macros
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

// Test fixture
class VirtualBaseDetectionTest : public ::testing::Test {
protected:
};

TEST_F(VirtualBaseDetectionTest, DetectSimpleVirtualInheritance) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Base) << "Base class not found";
        ASSERT_TRUE(Derived) << "Derived class not found";

        VirtualInheritanceAnalyzer analyzer;
        analyzer.analyzeClass(Base);
        analyzer.analyzeClass(Derived);

        // Base has no virtual bases
        ASSERT_TRUE(!analyzer.hasVirtualBases(Base)) << "Base should not have virtual bases";
        ASSERT_TRUE(analyzer.getVirtualBases(Base).size() == 0) << "Base should have 0 virtual bases";

        // Derived has Base as virtual base
        ASSERT_TRUE(analyzer.hasVirtualBases(Derived)) << "Derived should have virtual bases";
        auto vbases = analyzer.getVirtualBases(Derived);
        ASSERT_TRUE(vbases.size() == 1) << "Derived should have 1 virtual base";
        ASSERT_TRUE(vbases[0]->getNameAsString() == "Base") << "Virtual base should be Base";

        // Derived needs VTT
        ASSERT_TRUE(analyzer.needsVTT(Derived)) << "Derived should need VTT";
}

TEST_F(VirtualBaseDetectionTest, DetectDiamondPattern) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Left = findClass(TU, "Left");
        auto *Right = findClass(TU, "Right");
        auto *Diamond = findClass(TU, "Diamond");

        ASSERT_TRUE(Base) << "Base class not found";
        ASSERT_TRUE(Left) << "Left class not found";
        ASSERT_TRUE(Right) << "Right class not found";
        ASSERT_TRUE(Diamond) << "Diamond class not found";

        VirtualInheritanceAnalyzer analyzer;
        analyzer.analyzeClass(Base);
        analyzer.analyzeClass(Left);
        analyzer.analyzeClass(Right);
        analyzer.analyzeClass(Diamond);

        // Left and Right both have Base as virtual base
        ASSERT_TRUE(analyzer.hasVirtualBases(Left)) << "Left should have virtual bases";
        ASSERT_TRUE(analyzer.hasVirtualBases(Right)) << "Right should have virtual bases";

        // Diamond inherits virtual base from Left and Right
        ASSERT_TRUE(analyzer.hasVirtualBases(Diamond)) << "Diamond should have virtual bases";
        auto vbases = analyzer.getVirtualBases(Diamond);
        ASSERT_TRUE(vbases.size() == 1) << "Diamond should have 1 virtual base (shared Base;");
        ASSERT_TRUE(vbases[0]->getNameAsString() == "Base") << "Virtual base should be Base";

        // Diamond pattern detected
        ASSERT_TRUE(analyzer.isDiamondPattern(Diamond)) << "Diamond should be detected as diamond pattern";

        // All classes except Base need VTT
        ASSERT_TRUE(!analyzer.needsVTT(Base)) << "Base should not need VTT";
        ASSERT_TRUE(analyzer.needsVTT(Left)) << "Left should need VTT";
        ASSERT_TRUE(analyzer.needsVTT(Right)) << "Right should need VTT";
        ASSERT_TRUE(analyzer.needsVTT(Diamond)) << "Diamond should need VTT";
}

TEST_F(VirtualBaseDetectionTest, IgnoreNonVirtualInheritance) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Base) << "Base class not found";
        ASSERT_TRUE(Derived) << "Derived class not found";

        VirtualInheritanceAnalyzer analyzer;
        analyzer.analyzeClass(Base);
        analyzer.analyzeClass(Derived);

        // Derived does NOT have virtual bases
        ASSERT_TRUE(!analyzer.hasVirtualBases(Derived)) << "Derived should not have virtual bases";
        ASSERT_TRUE(analyzer.getVirtualBases(Derived).size() == 0) << "Derived should have 0 virtual bases";

        // Derived does NOT need VTT
        ASSERT_TRUE(!analyzer.needsVTT(Derived)) << "Derived should not need VTT";
}

TEST_F(VirtualBaseDetectionTest, BuildInheritanceGraph) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

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
        ASSERT_TRUE(graph.getParents(Base).size() == 0) << "Base should have no parents";

        // Left has Base as virtual parent
        auto leftParents = graph.getParents(Left);
        ASSERT_TRUE(leftParents.size() == 1) << "Left should have 1 parent";
        ASSERT_TRUE(leftParents[0].baseClass->getNameAsString() == "Base") << "Left's parent should be Base";
        ASSERT_TRUE(leftParents[0].isVirtual) << "Left->Base should be virtual";

        // Right has Base as virtual parent
        auto rightParents = graph.getParents(Right);
        ASSERT_TRUE(rightParents.size() == 1) << "Right should have 1 parent";
        ASSERT_TRUE(rightParents[0].baseClass->getNameAsString() == "Base") << "Right's parent should be Base";
        ASSERT_TRUE(rightParents[0].isVirtual) << "Right->Base should be virtual";

        // Diamond has Left and Right as non-virtual parents
        auto diamondParents = graph.getParents(Diamond);
        ASSERT_TRUE(diamondParents.size() == 2) << "Diamond should have 2 parents";

        // Find paths from Diamond to Base
        auto paths = graph.findPaths(Diamond, Base);
        ASSERT_TRUE(paths.size() == 2) << "Should be 2 paths from Diamond to Base";
}

TEST_F(VirtualBaseDetectionTest, MostDerivedAnalysis) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Derived = findClass(TU, "Derived");
        auto *MostDerived = findClass(TU, "MostDerived");

        VirtualInheritanceAnalyzer analyzer;
        analyzer.analyzeClass(Base);
        analyzer.analyzeClass(Derived);
        analyzer.analyzeClass(MostDerived);

        // When constructing Derived directly, it's most-derived
        ASSERT_TRUE(analyzer.isMostDerived(Derived) << Derived;, "Derived should be most-derived when constructing Derived");

        // When constructing MostDerived, Derived is NOT most-derived
        ASSERT_TRUE(!analyzer.isMostDerived(Derived) << MostDerived;, "Derived should not be most-derived when constructing MostDerived");

        // MostDerived is always most-derived when constructing itself
        ASSERT_TRUE(analyzer.isMostDerived(MostDerived) << MostDerived;, "MostDerived should be most-derived when constructing MostDerived");
}

TEST_F(VirtualBaseDetectionTest, MultipleVirtualBases) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base1 = findClass(TU, "Base1");
        auto *Base2 = findClass(TU, "Base2");
        auto *Derived = findClass(TU, "Derived");

        VirtualInheritanceAnalyzer analyzer;
        analyzer.analyzeClass(Base1);
        analyzer.analyzeClass(Base2);
        analyzer.analyzeClass(Derived);

        // Derived has two virtual bases
        ASSERT_TRUE(analyzer.hasVirtualBases(Derived)) << "Derived should have virtual bases";
        auto vbases = analyzer.getVirtualBases(Derived);
        ASSERT_TRUE(vbases.size() == 2) << "Derived should have 2 virtual bases";

        // Derived needs VTT
        ASSERT_TRUE(analyzer.needsVTT(Derived)) << "Derived should need VTT";
}

TEST_F(VirtualBaseDetectionTest, IndirectVirtualBases) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Middle = findClass(TU, "Middle");
        auto *Derived = findClass(TU, "Derived");

        VirtualInheritanceAnalyzer analyzer;
        analyzer.analyzeClass(Base);
        analyzer.analyzeClass(Middle);
        analyzer.analyzeClass(Derived);

        // Middle has direct virtual base
        ASSERT_TRUE(analyzer.hasVirtualBases(Middle)) << "Middle should have virtual bases";

        // Derived has indirect virtual base (through Middle)
        ASSERT_TRUE(analyzer.hasVirtualBases(Derived)) << "Derived should have virtual bases";
        auto vbases = analyzer.getVirtualBases(Derived);
        ASSERT_TRUE(vbases.size() == 1) << "Derived should have 1 virtual base";
        ASSERT_TRUE(vbases[0]->getNameAsString() == "Base") << "Virtual base should be Base";

        // Both need VTT
        ASSERT_TRUE(analyzer.needsVTT(Middle)) << "Middle should need VTT";
        ASSERT_TRUE(analyzer.needsVTT(Derived)) << "Derived should need VTT";
}

TEST_F(VirtualBaseDetectionTest, MixedInheritance) {
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
        ASSERT_TRUE(AST) << "Failed to build AST";

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *VirtualBase = findClass(TU, "VirtualBase");
        auto *NonVirtualBase = findClass(TU, "NonVirtualBase");
        auto *Derived = findClass(TU, "Derived");

        VirtualInheritanceAnalyzer analyzer;
        analyzer.analyzeClass(VirtualBase);
        analyzer.analyzeClass(NonVirtualBase);
        analyzer.analyzeClass(Derived);

        // Derived has one virtual base
        ASSERT_TRUE(analyzer.hasVirtualBases(Derived)) << "Derived should have virtual bases";
        auto vbases = analyzer.getVirtualBases(Derived);
        ASSERT_TRUE(vbases.size() == 1) << "Derived should have 1 virtual base";
        ASSERT_TRUE(vbases[0]->getNameAsString() == "VirtualBase") << "Virtual base should be VirtualBase";

        // Verify inheritance graph distinguishes virtual from non-virtual
        auto& graph = analyzer.getInheritanceGraph();
        auto parents = graph.getParents(Derived);
        ASSERT_TRUE(parents.size() == 2) << "Derived should have 2 parents";

        bool foundVirtual = false;
        bool foundNonVirtual = false;
        for (const auto& parent : parents) {
            if (parent.baseClass->getNameAsString() == "VirtualBase") {
                ASSERT_TRUE(parent.isVirtual) << "VirtualBase should be virtual";
                foundVirtual = true;
            } else {
                ASSERT_TRUE(!parent.isVirtual) << "NonVirtualBase should not be virtual";
                foundNonVirtual = true;
            }
        }
        ASSERT_TRUE(foundVirtual && foundNonVirtual) << "Should find both virtual and non-virtual bases";

        // Derived needs VTT
        ASSERT_TRUE(analyzer.needsVTT(Derived)) << "Derived should need VTT";
}
