/**
 * @file NameManglerV2SimpleTest.cpp
 * @brief Simple compilation test for new functional NameMangler implementation
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/DeclCXX.h"
#include "../include/NameMangler_v2.h"
#include <iostream>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    return tooling::buildASTFromCode(code);
}

// Test fixture
class NameManglerV2Test : public ::testing::Test {
protected:
};

TEST_F(NameManglerV2Test, SimpleMethodMangling) {
    const char *code = R"(
        class MyClass {
        public:
            void method();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    auto &Ctx = AST->getASTContext();

    // Find MyClass::method
    auto *TU = Ctx.getTranslationUnitDecl();
    CXXMethodDecl *method = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "MyClass") {
                for (auto *M : RD->methods()) {
                    if (M->getNameAsString() == "method") {
                        method = M;
                        break;
                    }
                }
            }
        }
    }

    ASSERT_TRUE(method != nullptr) << "MyClass::method not found";

    std::string mangled = cpptoc::mangle_method(method);
    std::cout << "Mangled name: " << mangled << std::endl;
    EXPECT_EQ(mangled, "MyClass__method__void");  // __ separator everywhere, void for empty params
}

TEST_F(NameManglerV2Test, NamespaceFunction) {
    const char *code = R"(
        namespace ns {
            void func();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    auto &Ctx = AST->getASTContext();

    // Find ns::func
    auto *TU = Ctx.getTranslationUnitDecl();
    FunctionDecl *func = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
            if (ND->getNameAsString() == "ns") {
                for (auto *Inner : ND->decls()) {
                    if (auto *FD = dyn_cast<FunctionDecl>(Inner)) {
                        if (FD->getNameAsString() == "func") {
                            func = FD;
                            break;
                        }
                    }
                }
            }
        }
    }

    ASSERT_TRUE(func != nullptr) << "ns::func not found";

    std::string mangled = cpptoc::mangle_function(func);
    std::cout << "Mangled name: " << mangled << std::endl;
    EXPECT_EQ(mangled, "ns__func__void");  // __ separator everywhere, void for empty params
}

TEST_F(NameManglerV2Test, NestedClass) {
    const char *code = R"(
        class Outer {
        public:
            class Inner {
            public:
                void method();
            };
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    auto &Ctx = AST->getASTContext();

    // Find Outer::Inner
    auto *TU = Ctx.getTranslationUnitDecl();
    CXXRecordDecl *innerClass = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Outer") {
                for (auto *Nested : RD->decls()) {
                    if (auto *InnerRD = dyn_cast<CXXRecordDecl>(Nested)) {
                        if (InnerRD->getNameAsString() == "Inner") {
                            innerClass = InnerRD;
                            break;
                        }
                    }
                }
            }
        }
    }

    ASSERT_TRUE(innerClass != nullptr) << "Outer::Inner not found";

    std::string mangled = cpptoc::mangle_class(innerClass);
    std::cout << "Mangled class name: " << mangled << std::endl;
    // Should use __ for all separators per reference implementation
    EXPECT_EQ(mangled, "Outer__Inner");
}
