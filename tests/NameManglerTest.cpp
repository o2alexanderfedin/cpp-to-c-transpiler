#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/NameMangler.h"
#include <iostream>
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    return tooling::buildASTFromCode(code);
}

// Test helper macros
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

// Test 1: Simple class name
void test_SimpleClassName() {
    TEST_START("SimpleClassName");

    const char *code = R"(
        class MyClass {
        public:
            void method();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(MyClass != nullptr, "MyClass not found");

    std::string mangled = mangler.mangleClassName(MyClass);
    ASSERT(mangled == "MyClass", "Expected 'MyClass', got: " + mangled);

    TEST_PASS("SimpleClassName");
}

// Test 2: Class method
void test_ClassMethod() {
    TEST_START("ClassMethod");

    const char *code = R"(
        class MyClass {
        public:
            void method();
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(method != nullptr, "MyClass::method not found");

    std::string mangled = mangler.mangleMethodName(method);
    ASSERT(mangled == "MyClass_method", "Expected 'MyClass_method', got: " + mangled);

    TEST_PASS("ClassMethod");
}

// Test 3: Namespace function
void test_NamespaceFunction() {
    TEST_START("NamespaceFunction");

    const char *code = R"(
        namespace ns {
            void func();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(func != nullptr, "ns::func not found");

    std::string mangled = mangler.mangleFunctionName(func);
    ASSERT(mangled == "ns_func", "Expected 'ns_func', got: " + mangled);

    TEST_PASS("NamespaceFunction");
}

// Test 4: Nested namespaces
void test_NestedNamespaces() {
    TEST_START("NestedNamespaces");

    const char *code = R"(
        namespace ns1 {
            namespace ns2 {
                void func();
            }
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(func != nullptr, "ns1::ns2::func not found");

    std::string mangled = mangler.mangleFunctionName(func);
    ASSERT(mangled == "ns1_ns2_func", "Expected 'ns1_ns2_func', got: " + mangled);

    TEST_PASS("NestedNamespaces");
}

// Test 5: Namespace + class + method
void test_NamespaceClassMethod() {
    TEST_START("NamespaceClassMethod");

    const char *code = R"(
        namespace ns {
            class MyClass {
            public:
                void method();
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

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

    ASSERT(method != nullptr, "ns::MyClass::method not found");

    std::string mangled = mangler.mangleMethodName(method);
    ASSERT(mangled == "ns_MyClass_method", "Expected 'ns_MyClass_method', got: " + mangled);

    TEST_PASS("NamespaceClassMethod");
}

int main() {
    std::cout << "Running NameMangler Tests...\n" << std::endl;

    test_SimpleClassName();
    test_ClassMethod();
    test_NamespaceFunction();
    test_NestedNamespaces();
    test_NamespaceClassMethod();

    std::cout << "\nAll tests passed!" << std::endl;
    return 0;
}
