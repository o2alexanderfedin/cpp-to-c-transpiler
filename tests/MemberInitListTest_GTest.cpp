// tests/MemberInitListTest_GTest.cpp
// Migrated from MemberInitListTest.cpp to Google Test framework
// Story #178: Member Initialization List Translation
// Epic #7: Advanced Constructor/Destructor Features

#include <gtest/gtest.h>
#include "CNodeBuilder.h"
#include "FileOriginTracker.h"
#include "CodeGenerator.h"
#include <clang/AST/ASTContext.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include <llvm/Support/raw_ostream.h>
#include <memory>
#include <string>
#include <sstream>

using namespace clang;
using namespace llvm;

// Test fixture for Member Init List tests
class MemberInitListTestFixture : public ::testing::Test {
protected:
    bool contains(const std::string &haystack, const std::string &needle) {
        return haystack.find(needle) != std::string::npos;
    }
};

// Test Case 1: Basic Member Init List with Primitive Types
TEST_F(MemberInitListTestFixture, BasicMemberInitList) {
    const char *cpp = R"(
        class Vector {
            double x, y, z;
        public:
            Vector(double x, double y, double z) : x(x), y(y), z(z) {}
        };
    )";

    auto AST = tooling::buildASTFromCode(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext targetCtx;
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CtorFunc = visitor.getCtor("Vector__ctor");
    ASSERT_NE(CtorFunc, nullptr) << "Constructor function not generated";

    std::string output;
    raw_string_ostream OS(output);
    CodeGenerator gen(OS, AST->getASTContext());
    gen.printDecl(CtorFunc);
    OS.flush();

    EXPECT_TRUE(contains(output, "this->x = x")) << "Member x not initialized";
    EXPECT_TRUE(contains(output, "this->y = y")) << "Member y not initialized";
    EXPECT_TRUE(contains(output, "this->z = z")) << "Member z not initialized";

    size_t x_pos = output.find("this->x = x");
    size_t y_pos = output.find("this->y = y");
    size_t z_pos = output.find("this->z = z");

    ASSERT_NE(x_pos, std::string::npos);
    ASSERT_NE(y_pos, std::string::npos);
    ASSERT_NE(z_pos, std::string::npos);
    EXPECT_TRUE(x_pos < y_pos && y_pos < z_pos) << "Declaration order not preserved";
}

// Test Case 2: Mixed Types Member Init List
TEST_F(MemberInitListTestFixture, MixedTypesMemberInitList) {
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
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext targetCtx;
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CtorFunc = visitor.getCtor("Entity__ctor");
    ASSERT_NE(CtorFunc, nullptr) << "Constructor function not generated";

    std::string output;
    raw_string_ostream OS(output);
    CodeGenerator gen(OS, AST->getASTContext());
    gen.printDecl(CtorFunc);
    OS.flush();

    EXPECT_TRUE(contains(output, "this->id = id")) << "int member not initialized";
    EXPECT_TRUE(contains(output, "this->health = health")) << "double member not initialized";
    EXPECT_TRUE(contains(output, "this->name = name")) << "pointer member not initialized";
}

// Test Case 3: Partial Member Init List
TEST_F(MemberInitListTestFixture, PartialMemberInitList) {
    const char *cpp = R"(
        class Particle {
            double x, y;
            int type;
        public:
            Particle(double x, double y) : x(x), y(y) {}
        };
    )";

    auto AST = tooling::buildASTFromCode(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext targetCtx;
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CtorFunc = visitor.getCtor("Particle__ctor");
    ASSERT_NE(CtorFunc, nullptr) << "Constructor function not generated";

    std::string output;
    raw_string_ostream OS(output);
    CodeGenerator gen(OS, AST->getASTContext());
    gen.printDecl(CtorFunc);
    OS.flush();

    EXPECT_TRUE(contains(output, "this->x = x")) << "Member x not initialized";
    EXPECT_TRUE(contains(output, "this->y = y")) << "Member y not initialized";

    size_t type_assign = output.find("this->type =");
    EXPECT_EQ(type_assign, std::string::npos)
        << "Uninitialized member 'type' should not have assignment";
}

// Test Case 4: Member Init List with Constant Values
TEST_F(MemberInitListTestFixture, MemberInitListWithConstants) {
    const char *cpp = R"(
        class Config {
            int version;
            bool enabled;
        public:
            Config() : version(1), enabled(true) {}
        };
    )";

    auto AST = tooling::buildASTFromCode(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext targetCtx;
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CtorFunc = visitor.getCtor("Config__ctor");
    ASSERT_NE(CtorFunc, nullptr) << "Constructor function not generated";

    std::string output;
    raw_string_ostream OS(output);
    CodeGenerator gen(OS, AST->getASTContext());
    gen.printDecl(CtorFunc);
    OS.flush();

    EXPECT_TRUE(contains(output, "this->version = 1")) << "version not initialized to 1";
    EXPECT_TRUE(contains(output, "this->enabled = ")) << "enabled not initialized";
}

// Test Case 5: Declaration Order Verification
TEST_F(MemberInitListTestFixture, DeclarationOrderPreserved) {
    const char *cpp = R"(
        class Test {
            int a, b, c;
        public:
            Test() : c(3), a(1), b(2) {}
        };
    )";

    auto AST = tooling::buildASTFromCode(cpp);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    CNodeBuilder builder(AST->getASTContext());
    cpptoc::FileOriginTracker tracker(AST->getASTContext().getSourceManager());
    tracker.addUserHeaderPath("<stdin>");
    clang::TranslationUnitDecl *C_TU = clang::TranslationUnitDecl::Create(AST->getASTContext());
    TargetContext targetCtx;
    CppToCVisitor visitor(AST->getASTContext(), builder, targetCtx, tracker, C_TU, nullptr);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CtorFunc = visitor.getCtor("Test__ctor");
    ASSERT_NE(CtorFunc, nullptr) << "Constructor function not generated";

    std::string output;
    raw_string_ostream OS(output);
    CodeGenerator gen(OS, AST->getASTContext());
    gen.printDecl(CtorFunc);
    OS.flush();

    EXPECT_TRUE(contains(output, "this->a = 1") &&
                contains(output, "this->b = 2") &&
                contains(output, "this->c = 3"))
        << "Not all members initialized";

    size_t a_pos = output.find("this->a = 1");
    size_t b_pos = output.find("this->b = 2");
    size_t c_pos = output.find("this->c = 3");

    EXPECT_TRUE(a_pos < b_pos && b_pos < c_pos)
        << "Members not in declaration order (should be a, b, c)";
}
