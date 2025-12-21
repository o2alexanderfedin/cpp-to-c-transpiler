// tests/VirtualBaseOffsetTableTest.cpp
// Unit tests for virtual base offset table generation (Story #90)
// Following TDD: RED phase - tests written first

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VtableGenerator.h"
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

// Test 1: Simple virtual inheritance - single virtual base offset

// Test fixture
class VirtualBaseOffsetTableTest : public ::testing::Test {
protected:
};

TEST_F(VirtualBaseOffsetTableTest, SimpleVirtualBaseOffset) {
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
        VtableGenerator generator(AST->getASTContext(), vmAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Base) << "Base class not found";
        ASSERT_TRUE(Derived) << "Derived class not found";

        viAnalyzer.analyzeClass(Base);
        viAnalyzer.analyzeClass(Derived);

        // Generate vtable with virtual base offsets
        std::string vtableCode = generator.generateVtableWithVirtualBaseOffsets(Derived, viAnalyzer);

        // Verify vtable contains virtual base offset table
        ASSERT_TRUE(!vtableCode.empty()) << "Vtable code should not be empty";
        ASSERT_TRUE(vtableCode.find("vbase_offset") != std::string::npos) << "Vtable should contain virtual base offset field";
        ASSERT_TRUE(vtableCode.find("Base") != std::string::npos) << "Vtable should reference Base class";
}

TEST_F(VirtualBaseOffsetTableTest, DiamondVirtualBaseOffset) {
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
        VtableGenerator generator(AST->getASTContext(), vmAnalyzer);

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

        // Generate vtable for Diamond class
        std::string vtableCode = generator.generateVtableWithVirtualBaseOffsets(Diamond, viAnalyzer);

        // Diamond should have virtual base offset for Base
        ASSERT_TRUE(vtableCode.find("vbase_offset") != std::string::npos) << "Diamond vtable should have virtual base offset";
        ASSERT_TRUE(vtableCode.find("Base") != std::string::npos) << "Diamond vtable should reference Base";
}

TEST_F(VirtualBaseOffsetTableTest, MultipleVirtualBaseOffsets) {
    const char *code = R"(
            class Base1 {
            public:
                virtual ~Base1() {}
                int b1;
            };

            class Base2 {
            public:
                virtual ~Base2() {}
                int b2;
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
        VtableGenerator generator(AST->getASTContext(), vmAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base1 = findClass(TU, "Base1");
        auto *Base2 = findClass(TU, "Base2");
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Base1 && Base2 && Derived) << "All classes should be found";

        viAnalyzer.analyzeClass(Base1);
        viAnalyzer.analyzeClass(Base2);
        viAnalyzer.analyzeClass(Derived);

        // Generate vtable with multiple virtual base offsets
        std::string vtableCode = generator.generateVtableWithVirtualBaseOffsets(Derived, viAnalyzer);

        // Should have offsets for both virtual bases
        ASSERT_TRUE(vtableCode.find("vbase_offset") != std::string::npos) << "Vtable should have virtual base offsets";

        // Count occurrences - should have at least 2 offset entries
        size_t count = 0;
        size_t pos = 0;
        while ((pos = vtableCode.find("Base", pos)) != std::string::npos) {
            count++;
            pos++;
        }
        ASSERT_TRUE(count >= 2) << "Should have references to both Base1 and Base2";
}

TEST_F(VirtualBaseOffsetTableTest, OffsetCalculation) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
                int b;
            };

            class Derived : public virtual Base {
            public:
                int d1;
                int d2;
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        VtableGenerator generator(AST->getASTContext(), vmAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Derived) << "Derived class not found";

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(Derived);

        // Calculate virtual base offset
        ptrdiff_t offset = generator.calculateVirtualBaseOffset(Derived, findClass(TU, "Base"),
                                                                 AST->getASTContext());

        // Offset should be non-zero (virtual base is at different location)
        ASSERT_TRUE(offset != 0) << "Virtual base offset should be non-zero";
}

TEST_F(VirtualBaseOffsetTableTest, NegativeOffsetArea) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
                int b;
            };

            class Derived : public virtual Base {
            public:
                virtual void foo() {}
                int d;
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        VtableGenerator generator(AST->getASTContext(), vmAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Derived) << "Derived class not found";

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(Derived);

        // Generate vtable structure
        std::string vtableCode = generator.generateVtableWithVirtualBaseOffsets(Derived, viAnalyzer);

        // According to Itanium ABI, virtual base offsets are stored before function pointers
        // In our C representation, we store them as fields before the function pointers
        ASSERT_TRUE(vtableCode.find("vbase_offset") != std::string::npos) << "Vtable should have vbase_offset field";

        // Verify offset comes before function pointers
        size_t offsetPos = vtableCode.find("vbase_offset");
        size_t funcPtrPos = vtableCode.find("(*destructor)");
        if (funcPtrPos == std::string::npos) {
            funcPtrPos = vtableCode.find("(*foo)");
        }

        ASSERT_TRUE(offsetPos < funcPtrPos) << "Virtual base offset should appear before function pointers";
}

TEST_F(VirtualBaseOffsetTableTest, VirtualBaseAccessHelper) {
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
        VtableGenerator generator(AST->getASTContext(), vmAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Base && Derived) << "Classes should be found";

        viAnalyzer.analyzeClass(Base);
        viAnalyzer.analyzeClass(Derived);

        // Generate helper function to access virtual base
        std::string helperCode = generator.generateVirtualBaseAccessHelper(Derived, Base);

        // Verify helper function signature
        ASSERT_TRUE(!helperCode.empty()) << "Helper function should be generated";
        ASSERT_TRUE(helperCode.find("Base") != std::string::npos) << "Helper should reference Base class";
        ASSERT_TRUE(helperCode.find("Derived") != std::string::npos) << "Helper should reference Derived class";
        ASSERT_TRUE(helperCode.find("vbase_offset") != std::string::npos ||
               helperCode.find("offset") != std::string::npos) << "Helper should use offset calculation";
}

TEST_F(VirtualBaseOffsetTableTest, NoVirtualBases) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
                int b;
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
        VtableGenerator generator(AST->getASTContext(), vmAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Derived) << "Derived class not found";

        viAnalyzer.analyzeClass(findClass(TU, "Base"));
        viAnalyzer.analyzeClass(Derived);

        // Generate vtable - should NOT have virtual base offsets
        std::string vtableCode = generator.generateVtableWithVirtualBaseOffsets(Derived, viAnalyzer);

        // Should not contain vbase_offset for non-virtual inheritance
        ASSERT_TRUE(vtableCode.find("vbase_offset") == std::string::npos ||
               vtableCode.find("// No virtual base offsets") != std::string::npos) << "Non-virtual inheritance should not have vbase_offset";
}

TEST_F(VirtualBaseOffsetTableTest, IndirectVirtualBaseOffset) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
                int b;
            };

            class Middle : public virtual Base {
            public:
                int m;
            };

            class Derived : public Middle {
            public:
                int d;
            };
        )";

        auto AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to build AST";

        VirtualMethodAnalyzer vmAnalyzer(AST->getASTContext());
        VirtualInheritanceAnalyzer viAnalyzer;
        VtableGenerator generator(AST->getASTContext(), vmAnalyzer);

        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Middle = findClass(TU, "Middle");
        auto *Derived = findClass(TU, "Derived");

        ASSERT_TRUE(Base && Middle && Derived) << "All classes should be found";

        viAnalyzer.analyzeClass(Base);
        viAnalyzer.analyzeClass(Middle);
        viAnalyzer.analyzeClass(Derived);

        // Derived indirectly inherits virtual base through Middle
        std::string vtableCode = generator.generateVtableWithVirtualBaseOffsets(Derived, viAnalyzer);

        // Should have virtual base offset for indirectly inherited Base
        ASSERT_TRUE(vtableCode.find("vbase_offset") != std::string::npos) << "Derived should have virtual base offset for indirect virtual base";
        ASSERT_TRUE(vtableCode.find("Base") != std::string::npos) << "Vtable should reference Base";
}
