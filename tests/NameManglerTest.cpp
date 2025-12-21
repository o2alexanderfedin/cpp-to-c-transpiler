#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/NameMangler.h"
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    return tooling::buildASTFromCode(code);
}

    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

// Test fixture
class NameManglerTest : public ::testing::Test {
protected:
};

TEST_F(NameManglerTest, SimpleClassName) {
    const char *code = R"(
            class MyClass {
            public:
                void method();
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find MyClass
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        CXXRecordDecl *MyClass = nullptr;
        for (auto *D : TU->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == "MyClass") {
                    MyClass = RD;
                    break;
                }
            }
        }

        ASSERT_TRUE(MyClass != nullptr) << "MyClass not found";

        std::string mangled = mangler.mangleClassName(MyClass);
        ASSERT_TRUE(mangled == "MyClass") << "Expected 'MyClass', got: " + mangled;
}

TEST_F(NameManglerTest, ClassMethod) {
    const char *code = R"(
            class MyClass {
            public:
                void method();
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find MyClass::method
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
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

        std::string mangled = mangler.mangleMethodName(method);
        ASSERT_TRUE(mangled == "MyClass_method") << "Expected 'MyClass_method', got: " + mangled;
}

TEST_F(NameManglerTest, NamespaceFunction) {
    const char *code = R"(
            namespace ns {
                void func();
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find ns::func
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
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

        std::string mangled = mangler.mangleFunctionName(func);
        ASSERT_TRUE(mangled == "ns_func") << "Expected 'ns_func', got: " + mangled;
}

TEST_F(NameManglerTest, NestedNamespaces) {
    const char *code = R"(
            namespace ns1 {
                namespace ns2 {
                    void func();
                }
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find ns1::ns2::func
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        FunctionDecl *func = nullptr;
        for (auto *D : TU->decls()) {
            if (auto *ND1 = dyn_cast<NamespaceDecl>(D)) {
                if (ND1->getNameAsString() == "ns1") {
                    for (auto *Inner1 : ND1->decls()) {
                        if (auto *ND2 = dyn_cast<NamespaceDecl>(Inner1)) {
                            if (ND2->getNameAsString() == "ns2") {
                                for (auto *Inner2 : ND2->decls()) {
                                    if (auto *FD = dyn_cast<FunctionDecl>(Inner2)) {
                                        if (FD->getNameAsString() == "func") {
                                            func = FD;
                                            break;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        ASSERT_TRUE(func != nullptr) << "ns1::ns2::func not found";

        std::string mangled = mangler.mangleFunctionName(func);
        ASSERT_TRUE(mangled == "ns1_ns2_func") << "Expected 'ns1_ns2_func', got: " + mangled;
}

TEST_F(NameManglerTest, NamespaceClassMethod) {
    const char *code = R"(
            namespace ns {
                class MyClass {
                public:
                    void method();
                };
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find ns::MyClass::method
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        CXXMethodDecl *method = nullptr;
        for (auto *D : TU->decls()) {
            if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
                if (ND->getNameAsString() == "ns") {
                    for (auto *Inner : ND->decls()) {
                        if (auto *RD = dyn_cast<CXXRecordDecl>(Inner)) {
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
                }
            }
        }

        ASSERT_TRUE(method != nullptr) << "ns::MyClass::method not found";

        std::string mangled = mangler.mangleMethodName(method);
        ASSERT_TRUE(mangled == "ns_MyClass_method") << "Expected 'ns_MyClass_method', got: " + mangled;
}
