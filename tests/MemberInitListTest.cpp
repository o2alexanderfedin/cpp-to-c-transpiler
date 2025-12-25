// TDD Tests for Member Initialization List Translation - Story #178
// Epic #7: Advanced Constructor/Destructor Features
//
// Acceptance Criteria:
// - Member init lists parsed from C++ constructors
// - Translated to C assignments in correct declaration order
// - Handles all basic types (int, double, char*, etc.)
// - Unit tests verify correct translation

#include <gtest/gtest.h>
#include "CppToCVisitor.h"
#include "CNodeBuilder.h"
#include "CodeGenerator.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <string>
#include <sstream>

using namespace clang;

bool contains(const std::string &haystack, const std::string &needle) {
    return haystack.find(needle) != std::string::npos;
}

TEST(MemberInitList, BasicMemberInitListSimplePrimitiveMemberInitialization) {
    const char *cpp = R"(
            class Vector {
                double x, y, z;
            public:
                Vector(double x, double y, double z) : x(x), y(y), z(z) {}
            };
        )";

        auto AST = tooling::buildASTFromCode(cpp);
        if (!AST) {
            FAIL() << "Failed to parse C++ code";
        }

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        // Get the generated constructor function
        FunctionDecl *CtorFunc = visitor.getCtor("Vector__ctor");
        if (!CtorFunc) {
            FAIL() << "Constructor function not generated";
        }

        // Generate C code from the function
        std::string output;
        llvm::raw_string_ostream OS(output);
        CodeGenerator gen(OS, AST->getASTContext());
        gen.printDecl(CtorFunc);
        OS.flush();

        // Verify member assignments in correct order
        if (!contains(output, "this->x = x")) {
            FAIL() << "Member x not initialized";
        }
        if (!contains(output, "this->y = y")) {
            FAIL() << "Member y not initialized";
        }
        if (!contains(output, "this->z = z")) {
            FAIL() << "Member z not initialized";
        }

        // Verify declaration order preserved (x before y before z)
        size_t x_pos = output.find("this->x = x");
        size_t y_pos = output.find("this->y = y");
        size_t z_pos = output.find("this->z = z");

        if (x_pos == std::string::npos || y_pos == std::string::npos || z_pos == std::string::npos) {
            FAIL() << "Not all members found";
        }

        if (!(x_pos < y_pos && y_pos < z_pos)) {
            FAIL() << "Declaration order not preserved";
        }
}

TEST(MemberInitList, MixedTypesMemberInitListIntDoubleCharPtrInitialization) {
    const char *cpp = R"(
            class Entity {
                int id;
                double health;
                char *name;
            public:
                Entity(int id, double health, char *name)
                    : id(id), health(health), name(name) {}
            };
        )";

        auto AST = tooling::buildASTFromCode(cpp);
        if (!AST) {
            FAIL() << "Failed to parse C++ code";
        }

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        FunctionDecl *CtorFunc = visitor.getCtor("Entity__ctor");
        if (!CtorFunc) {
            FAIL() << "Constructor function not generated";
        }

        std::string output;
        llvm::raw_string_ostream OS(output);
        CodeGenerator gen(OS, AST->getASTContext());
        gen.printDecl(CtorFunc);
        OS.flush();

        // Verify all three types initialized
        if (!contains(output, "this->id = id")) {
            FAIL() << "int member not initialized";
        }
        if (!contains(output, "this->health = health")) {
            FAIL() << "double member not initialized";
        }
        if (!contains(output, "this->name = name")) {
            FAIL() << "pointer member not initialized";
        }
}

TEST(MemberInitList, PartialMemberInitListOnlySomeMembersInitialized) {
    const char *cpp = R"(
            class Particle {
                double x, y;
                int type;
            public:
                Particle(double x, double y) : x(x), y(y) {}
            };
        )";

        auto AST = tooling::buildASTFromCode(cpp);
        if (!AST) {
            FAIL() << "Failed to parse C++ code";
        }

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        FunctionDecl *CtorFunc = visitor.getCtor("Particle__ctor");
        if (!CtorFunc) {
            FAIL() << "Constructor function not generated";
        }

        std::string output;
        llvm::raw_string_ostream OS(output);
        CodeGenerator gen(OS, AST->getASTContext());
        gen.printDecl(CtorFunc);
        OS.flush();

        // Verify initialized members
        if (!contains(output, "this->x = x")) {
            FAIL() << "Member x not initialized";
        }
        if (!contains(output, "this->y = y")) {
            FAIL() << "Member y not initialized";
        }

        // Verify type is NOT initialized (should not have assignment)
        // Note: We check that if "type" appears, it's only in the struct, not in assignment
        size_t type_assign = output.find("this->type =");
        if (type_assign != std::string::npos) {
            FAIL() << "Uninitialized member 'type' should not have assignment";
        }
}

TEST(MemberInitList, MemberInitListWithConstantsConstantValueInitialization) {
    const char *cpp = R"(
            class Config {
                int version;
                bool enabled;
            public:
                Config() : version(1), enabled(true) {}
            };
        )";

        auto AST = tooling::buildASTFromCode(cpp);
        if (!AST) {
            FAIL() << "Failed to parse C++ code";
        }

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        FunctionDecl *CtorFunc = visitor.getCtor("Config__ctor");
        if (!CtorFunc) {
            FAIL() << "Constructor function not generated";
        }

        std::string output;
        llvm::raw_string_ostream OS(output);
        CodeGenerator gen(OS, AST->getASTContext());
        gen.printDecl(CtorFunc);
        OS.flush();

        // Verify constant initialization
        if (!contains(output, "this->version = 1")) {
            FAIL() << "version not initialized to 1";
        }

        // Check for boolean (could be 1 or true depending on translation)
        if (!contains(output, "this->enabled = ")) {
            FAIL() << "enabled not initialized";
        }
}

TEST(MemberInitList, DeclarationOrderPreservedInitOrderFollowsDeclarationNotInitList) {
    const char *cpp = R"(
            class Test {
                int a, b, c;
            public:
                Test() : c(3), a(1), b(2) {}
            };
        )";

        auto AST = tooling::buildASTFromCode(cpp);
        if (!AST) {
            FAIL() << "Failed to parse C++ code";
        }

        CNodeBuilder builder(AST->getASTContext());
        CppToCVisitor visitor(AST->getASTContext(), builder);
        visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        FunctionDecl *CtorFunc = visitor.getCtor("Test__ctor");
        if (!CtorFunc) {
            FAIL() << "Constructor function not generated";
        }

        std::string output;
        llvm::raw_string_ostream OS(output);
        CodeGenerator gen(OS, AST->getASTContext());
        gen.printDecl(CtorFunc);
        OS.flush();

        // Verify all members initialized
        if (!contains(output, "this->a = 1") ||
            !contains(output, "this->b = 2") ||
            !contains(output, "this->c = 3")) {
            FAIL() << "Not all members initialized";
        }

        // Verify order: a before b before c
        size_t a_pos = output.find("this->a = 1");
        size_t b_pos = output.find("this->b = 2");
        size_t c_pos = output.find("this->c = 3");

        if (!(a_pos < b_pos && b_pos < c_pos)) {
            FAIL() << "Members not in declaration order (should be a, b, c)";
        }
}
