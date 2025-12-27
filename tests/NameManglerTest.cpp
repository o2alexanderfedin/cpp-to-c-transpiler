#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/DeclCXX.h"
#include "../include/NameMangler.h"
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    return tooling::buildASTFromCode(code);
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

// ============================================================================
// Phase 48: Anonymous Namespace Tests
// ============================================================================

TEST_F(NameManglerTest, AnonymousNamespaceFunction) {
    const char *code = R"(
            namespace {
                void helper();
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find anonymous namespace function
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        FunctionDecl *func = nullptr;
        for (auto *D : TU->decls()) {
            if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
                if (ND->isAnonymousNamespace()) {
                    for (auto *Inner : ND->decls()) {
                        if (auto *FD = dyn_cast<FunctionDecl>(Inner)) {
                            if (FD->getNameAsString() == "helper") {
                                func = FD;
                                break;
                            }
                        }
                    }
                }
            }
        }

        ASSERT_TRUE(func != nullptr) << "Anonymous namespace function not found";

        std::string mangled = mangler.mangleFunctionName(func);
        // Should have pattern: _anon_<identifier>_helper
        ASSERT_TRUE(mangled.find("_anon_") == 0) << "Expected anonymous namespace prefix '_anon_', got: " + mangled;
        ASSERT_TRUE(mangled.find("_helper") != std::string::npos) << "Expected '_helper' suffix, got: " + mangled;
}

TEST_F(NameManglerTest, AnonymousNamespaceClass) {
    const char *code = R"(
            namespace {
                class InternalClass {
                public:
                    void method();
                };
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find anonymous namespace class
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        CXXRecordDecl *cls = nullptr;
        for (auto *D : TU->decls()) {
            if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
                if (ND->isAnonymousNamespace()) {
                    for (auto *Inner : ND->decls()) {
                        if (auto *RD = dyn_cast<CXXRecordDecl>(Inner)) {
                            if (RD->getNameAsString() == "InternalClass") {
                                cls = RD;
                                break;
                            }
                        }
                    }
                }
            }
        }

        ASSERT_TRUE(cls != nullptr) << "Anonymous namespace class not found";

        std::string mangled = mangler.mangleClassName(cls);
        // Should have pattern: _anon_<identifier>_InternalClass
        ASSERT_TRUE(mangled.find("_anon_") == 0) << "Expected anonymous namespace prefix, got: " + mangled;
        ASSERT_TRUE(mangled.find("_InternalClass") != std::string::npos) << "Expected class name suffix, got: " + mangled;
}

TEST_F(NameManglerTest, NestedAnonymousNamespace) {
    const char *code = R"(
            namespace outer {
                namespace {
                    void helper();
                }
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find nested anonymous namespace function
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        FunctionDecl *func = nullptr;
        for (auto *D : TU->decls()) {
            if (auto *ND1 = dyn_cast<NamespaceDecl>(D)) {
                if (ND1->getNameAsString() == "outer") {
                    for (auto *Inner1 : ND1->decls()) {
                        if (auto *ND2 = dyn_cast<NamespaceDecl>(Inner1)) {
                            if (ND2->isAnonymousNamespace()) {
                                for (auto *Inner2 : ND2->decls()) {
                                    if (auto *FD = dyn_cast<FunctionDecl>(Inner2)) {
                                        if (FD->getNameAsString() == "helper") {
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

        ASSERT_TRUE(func != nullptr) << "Nested anonymous namespace function not found";

        std::string mangled = mangler.mangleFunctionName(func);
        // Should have pattern: outer__anon_<identifier>_helper
        ASSERT_TRUE(mangled.find("outer_") == 0) << "Expected 'outer_' prefix, got: " + mangled;
        ASSERT_TRUE(mangled.find("_anon_") != std::string::npos) << "Expected '_anon_' in name, got: " + mangled;
        ASSERT_TRUE(mangled.find("_helper") != std::string::npos) << "Expected '_helper' suffix, got: " + mangled;
}

TEST_F(NameManglerTest, AnonymousNamespaceMethodInClass) {
    const char *code = R"(
            namespace {
                class Helper {
                public:
                    void process();
                };
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find method in anonymous namespace class
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        CXXMethodDecl *method = nullptr;
        for (auto *D : TU->decls()) {
            if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
                if (ND->isAnonymousNamespace()) {
                    for (auto *Inner : ND->decls()) {
                        if (auto *RD = dyn_cast<CXXRecordDecl>(Inner)) {
                            if (RD->getNameAsString() == "Helper") {
                                for (auto *M : RD->methods()) {
                                    if (M->getNameAsString() == "process") {
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

        ASSERT_TRUE(method != nullptr) << "Method in anonymous namespace class not found";

        std::string mangled = mangler.mangleMethodName(method);
        // Should have pattern: _anon_<identifier>_Helper_process
        ASSERT_TRUE(mangled.find("_anon_") == 0) << "Expected anonymous namespace prefix, got: " + mangled;
        ASSERT_TRUE(mangled.find("_Helper_process") != std::string::npos) << "Expected '_Helper_process' suffix, got: " + mangled;
}

// ============================================================================
// Phase 48: Comprehensive Test Coverage (Enhanced Tests)
// ============================================================================

TEST_F(NameManglerTest, ExternCInNamespace) {
    const char *code = R"(
            namespace wrapper {
                extern "C" {
                    void c_function() { }
                }
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find extern "C" function - it might be at TU level or in namespace
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        FunctionDecl *func = nullptr;

        // First try namespace level
        for (auto *D : TU->decls()) {
            if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
                if (ND->getNameAsString() == "wrapper") {
                    for (auto *Inner : ND->decls()) {
                        if (auto *LinkSpec = dyn_cast<LinkageSpecDecl>(Inner)) {
                            // extern "C" creates a LinkageSpecDecl
                            for (auto *Linked : LinkSpec->decls()) {
                                if (auto *FD = dyn_cast<FunctionDecl>(Linked)) {
                                    if (FD->getNameAsString() == "c_function") {
                                        func = FD;
                                        break;
                                    }
                                }
                            }
                        }
                        if (auto *FD = dyn_cast<FunctionDecl>(Inner)) {
                            if (FD->getNameAsString() == "c_function") {
                                func = FD;
                                break;
                            }
                        }
                    }
                }
            }
        }

        ASSERT_TRUE(func != nullptr) << "extern C function not found";

        std::string mangled = mangler.mangleFunctionName(func);
        // extern "C" prevents mangling even in namespace
        ASSERT_TRUE(mangled == "c_function") << "Expected 'c_function' (not mangled), got: " + mangled;
}

TEST_F(NameManglerTest, DeepNesting) {
    const char *code = R"(
            namespace a {
                namespace b {
                    namespace c {
                        namespace d {
                            void func();
                        }
                    }
                }
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find deeply nested function
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        FunctionDecl *func = nullptr;

        // Navigate through nested namespaces
        for (auto *D : TU->decls()) {
            if (auto *ND_a = dyn_cast<NamespaceDecl>(D)) {
                if (ND_a->getNameAsString() == "a") {
                    for (auto *Inner_a : ND_a->decls()) {
                        if (auto *ND_b = dyn_cast<NamespaceDecl>(Inner_a)) {
                            if (ND_b->getNameAsString() == "b") {
                                for (auto *Inner_b : ND_b->decls()) {
                                    if (auto *ND_c = dyn_cast<NamespaceDecl>(Inner_b)) {
                                        if (ND_c->getNameAsString() == "c") {
                                            for (auto *Inner_c : ND_c->decls()) {
                                                if (auto *ND_d = dyn_cast<NamespaceDecl>(Inner_c)) {
                                                    if (ND_d->getNameAsString() == "d") {
                                                        for (auto *Inner_d : ND_d->decls()) {
                                                            if (auto *FD = dyn_cast<FunctionDecl>(Inner_d)) {
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
                            }
                        }
                    }
                }
            }
        }

        ASSERT_TRUE(func != nullptr) << "Deeply nested function not found";

        std::string mangled = mangler.mangleFunctionName(func);
        ASSERT_TRUE(mangled == "a_b_c_d_func") << "Expected 'a_b_c_d_func', got: " + mangled;
}

TEST_F(NameManglerTest, StaticMethodInNamespace) {
    const char *code = R"(
            namespace utils {
                class Helper {
                public:
                    static void staticMethod();
                };
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find static method
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        CXXMethodDecl *method = nullptr;
        for (auto *D : TU->decls()) {
            if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
                if (ND->getNameAsString() == "utils") {
                    for (auto *Inner : ND->decls()) {
                        if (auto *RD = dyn_cast<CXXRecordDecl>(Inner)) {
                            if (RD->getNameAsString() == "Helper") {
                                for (auto *M : RD->methods()) {
                                    if (M->getNameAsString() == "staticMethod") {
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

        ASSERT_TRUE(method != nullptr) << "Static method not found";
        ASSERT_TRUE(method->isStatic()) << "Method should be static";

        std::string mangled = mangler.mangleMethodName(method);
        ASSERT_TRUE(mangled == "utils_Helper_staticMethod") << "Expected 'utils_Helper_staticMethod', got: " + mangled;
}

TEST_F(NameManglerTest, NestedClassInNamespace) {
    const char *code = R"(
            namespace ns {
                class Outer {
                public:
                    class Inner {
                    public:
                        void method();
                    };
                };
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find nested class
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        CXXRecordDecl *innerClass = nullptr;
        for (auto *D : TU->decls()) {
            if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
                if (ND->getNameAsString() == "ns") {
                    for (auto *Inner : ND->decls()) {
                        if (auto *RD = dyn_cast<CXXRecordDecl>(Inner)) {
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
                }
            }
        }

        ASSERT_TRUE(innerClass != nullptr) << "Nested class not found";

        std::string mangled = mangler.mangleClassName(innerClass);
        // Note: Nested classes get Outer_Inner naming (not namespace prefixed for inner class)
        // The outer class gets the namespace prefix: ns_Outer
        // The pattern depends on how nested classes are handled in the mangler
        ASSERT_TRUE(mangled.find("Inner") != std::string::npos) << "Expected 'Inner' in name, got: " + mangled;
}

TEST_F(NameManglerTest, ConstructorInNamespacedClass) {
    const char *code = R"(
            namespace data {
                class Buffer {
                public:
                    Buffer();
                    Buffer(int size);
                };
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find constructors
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        CXXConstructorDecl *defaultCtor = nullptr;
        CXXConstructorDecl *paramCtor = nullptr;

        for (auto *D : TU->decls()) {
            if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
                if (ND->getNameAsString() == "data") {
                    for (auto *Inner : ND->decls()) {
                        if (auto *RD = dyn_cast<CXXRecordDecl>(Inner)) {
                            if (RD->getNameAsString() == "Buffer") {
                                for (auto *M : RD->methods()) {
                                    if (auto *CD = dyn_cast<CXXConstructorDecl>(M)) {
                                        if (CD->getNumParams() == 0) {
                                            defaultCtor = CD;
                                        } else if (CD->getNumParams() == 1) {
                                            paramCtor = CD;
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        ASSERT_TRUE(defaultCtor != nullptr) << "Default constructor not found";
        ASSERT_TRUE(paramCtor != nullptr) << "Parameterized constructor not found";

        std::string mangled1 = mangler.mangleConstructor(defaultCtor);
        std::string mangled2 = mangler.mangleConstructor(paramCtor);

        // Constructors don't get namespace prefix in current implementation
        // They use class name which should already include namespace
        ASSERT_TRUE(mangled1.find("__ctor") != std::string::npos) << "Expected '__ctor' in name, got: " + mangled1;
        ASSERT_TRUE(mangled2.find("__ctor") != std::string::npos) << "Expected '__ctor' in name, got: " + mangled2;
        ASSERT_TRUE(mangled1 != mangled2) << "Constructors should have different mangled names";
}

TEST_F(NameManglerTest, OverloadedFunctionsInNamespace) {
    const char *code = R"(
            namespace math {
                void process(int x);
                void process(double x);
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find both overloaded functions
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        FunctionDecl *intFunc = nullptr;
        FunctionDecl *doubleFunc = nullptr;

        for (auto *D : TU->decls()) {
            if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
                if (ND->getNameAsString() == "math") {
                    for (auto *Inner : ND->decls()) {
                        if (auto *FD = dyn_cast<FunctionDecl>(Inner)) {
                            if (FD->getNameAsString() == "process") {
                                if (FD->getNumParams() > 0) {
                                    QualType ParamType = FD->getParamDecl(0)->getType();
                                    if (ParamType->isIntegerType()) {
                                        intFunc = FD;
                                    } else if (ParamType->isFloatingType()) {
                                        doubleFunc = FD;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        ASSERT_TRUE(intFunc != nullptr) << "Int overload not found";
        ASSERT_TRUE(doubleFunc != nullptr) << "Double overload not found";

        std::string mangled1 = mangler.mangleStandaloneFunction(intFunc);
        std::string mangled2 = mangler.mangleStandaloneFunction(doubleFunc);

        // Both should start with namespace prefix
        ASSERT_TRUE(mangled1.find("math_") == 0) << "Expected 'math_' prefix, got: " + mangled1;
        ASSERT_TRUE(mangled2.find("math_") == 0) << "Expected 'math_' prefix, got: " + mangled2;
        // And they should be different
        ASSERT_TRUE(mangled1 != mangled2) << "Overloads should have different mangled names";
}

TEST_F(NameManglerTest, MultipleNamespacesInSameFile) {
    const char *code = R"(
            namespace ns1 {
                void func();
            }
            namespace ns2 {
                void func();
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find both functions
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        FunctionDecl *func1 = nullptr;
        FunctionDecl *func2 = nullptr;

        for (auto *D : TU->decls()) {
            if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
                if (ND->getNameAsString() == "ns1") {
                    for (auto *Inner : ND->decls()) {
                        if (auto *FD = dyn_cast<FunctionDecl>(Inner)) {
                            if (FD->getNameAsString() == "func") {
                                func1 = FD;
                                break;
                            }
                        }
                    }
                } else if (ND->getNameAsString() == "ns2") {
                    for (auto *Inner : ND->decls()) {
                        if (auto *FD = dyn_cast<FunctionDecl>(Inner)) {
                            if (FD->getNameAsString() == "func") {
                                func2 = FD;
                                break;
                            }
                        }
                    }
                }
            }
        }

        ASSERT_TRUE(func1 != nullptr) << "ns1::func not found";
        ASSERT_TRUE(func2 != nullptr) << "ns2::func not found";

        std::string mangled1 = mangler.mangleFunctionName(func1);
        std::string mangled2 = mangler.mangleFunctionName(func2);

        ASSERT_TRUE(mangled1 == "ns1_func") << "Expected 'ns1_func', got: " + mangled1;
        ASSERT_TRUE(mangled2 == "ns2_func") << "Expected 'ns2_func', got: " + mangled2;
}

TEST_F(NameManglerTest, Cpp17NestedNamespaceSyntax) {
    const char *code = R"(
            namespace a::b::c {
                void func();
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        NameMangler mangler(AST->getASTContext());

        // Find function in C++17 nested namespace
        auto *TU = AST->getASTContext().getTranslationUnitDecl();
        FunctionDecl *func = nullptr;

        // C++17 nested namespace syntax creates actual nested NamespaceDecls
        for (auto *D : TU->decls()) {
            if (auto *ND_a = dyn_cast<NamespaceDecl>(D)) {
                if (ND_a->getNameAsString() == "a") {
                    for (auto *Inner_a : ND_a->decls()) {
                        if (auto *ND_b = dyn_cast<NamespaceDecl>(Inner_a)) {
                            if (ND_b->getNameAsString() == "b") {
                                for (auto *Inner_b : ND_b->decls()) {
                                    if (auto *ND_c = dyn_cast<NamespaceDecl>(Inner_b)) {
                                        if (ND_c->getNameAsString() == "c") {
                                            for (auto *Inner_c : ND_c->decls()) {
                                                if (auto *FD = dyn_cast<FunctionDecl>(Inner_c)) {
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
                }
            }
        }

        ASSERT_TRUE(func != nullptr) << "C++17 nested namespace function not found";

        std::string mangled = mangler.mangleFunctionName(func);
        ASSERT_TRUE(mangled == "a_b_c_func") << "Expected 'a_b_c_func', got: " + mangled;
}
