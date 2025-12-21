/**
 * @file OverrideResolverTest.cpp
 * @brief Tests for Story #170: Virtual Function Override Resolution
 *
 * Acceptance Criteria:
 * - Overridden methods resolved correctly
 * - Inherited methods tracked
 * - Multi-level inheritance works
 * - Method slot consistency maintained
 * - Unit tests pass (8+ test cases)
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/OverrideResolver.h"
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

// Test 1: Single method override

// Test fixture
class OverrideResolverTest : public ::testing::Test {
protected:
};

TEST_F(OverrideResolverTest, SingleMethodOverride) {
    const char *code = R"(
            class Base {
            public:
                virtual void foo();
            };

            class Derived : public Base {
            public:
                void foo() override;
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        // Resolve overrides for Derived
        auto vtableMethods = resolver.resolveVtableLayout(Derived);

        // Test: Should have 1 method (foo from Derived, not Base)
        // Destructor is implicit, so might be 1 or 2 depending on implementation
        ASSERT_TRUE(vtableMethods.size() >= 1) << "Expected at least 1 method";

        // Find foo in vtable
        CXXMethodDecl* fooMethod = nullptr;
        for (auto* method : vtableMethods) {
            if (!isa<CXXDestructorDecl>(method) && method->getNameAsString() == "foo") {
                fooMethod = method;
                break;
            }
        }

        ASSERT_TRUE(fooMethod) << "foo method not found in vtable";

        // Test: foo should be from Derived, not Base
        ASSERT_TRUE(fooMethod->getParent()->getNameAsString() == "Derived") << "foo should be from Derived class (override;");
}

TEST_F(OverrideResolverTest, InheritedMethod) {
    const char *code = R"(
            class Base {
            public:
                virtual void foo();
                virtual void bar();
            };

            class Derived : public Base {
            public:
                void foo() override;
                // bar is NOT overridden
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        auto vtableMethods = resolver.resolveVtableLayout(Derived);

        // Find foo and bar
        CXXMethodDecl* fooMethod = nullptr;
        CXXMethodDecl* barMethod = nullptr;

        for (auto* method : vtableMethods) {
            if (isa<CXXDestructorDecl>(method)) continue;

            if (method->getNameAsString() == "foo") {
                fooMethod = method;
            } else if (method->getNameAsString() == "bar") {
                barMethod = method;
            }
        }

        ASSERT_TRUE(fooMethod) << "foo not found in vtable";
        ASSERT_TRUE(barMethod) << "bar not found in vtable";

        // Test: foo should be overridden (from Derived)
        ASSERT_TRUE(fooMethod->getParent()->getNameAsString() == "Derived") << "foo should be from Derived (overridden;");

        // Test: bar should be inherited (from Base)
        ASSERT_TRUE(barMethod->getParent()->getNameAsString() == "Base") << "bar should be from Base (inherited;");
}

TEST_F(OverrideResolverTest, MultiLevelInheritance) {
    const char *code = R"(
            class Base {
            public:
                virtual void foo();
            };

            class Middle : public Base {
            public:
                void foo() override;
                virtual void bar();
            };

            class Derived : public Middle {
            public:
                void bar() override;
                // foo inherited from Middle
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        auto vtableMethods = resolver.resolveVtableLayout(Derived);

        // Find foo and bar
        CXXMethodDecl* fooMethod = nullptr;
        CXXMethodDecl* barMethod = nullptr;

        for (auto* method : vtableMethods) {
            if (isa<CXXDestructorDecl>(method)) continue;

            if (method->getNameAsString() == "foo") {
                fooMethod = method;
            } else if (method->getNameAsString() == "bar") {
                barMethod = method;
            }
        }

        ASSERT_TRUE(fooMethod) << "foo not found in vtable";
        ASSERT_TRUE(barMethod) << "bar not found in vtable";

        // Test: foo should be from Middle (overrode Base, inherited by Derived)
        ASSERT_TRUE(fooMethod->getParent()->getNameAsString() == "Middle") << "foo should be from Middle";

        // Test: bar should be from Derived (overrode Middle)
        ASSERT_TRUE(barMethod->getParent()->getNameAsString() == "Derived") << "bar should be from Derived";
}

TEST_F(OverrideResolverTest, VtableSlotConsistency) {
    const char *code = R"(
            class Base {
            public:
                virtual void first();
                virtual void second();
                virtual void third();
            };

            class Derived : public Base {
            public:
                void second() override;  // Override middle method
                // first and third inherited
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Base = findClass(TU, "Base");
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Base) << "Base class not found";
        ASSERT_TRUE(Derived) << "Derived class not found";

        auto baseMethods = resolver.resolveVtableLayout(Base);
        auto derivedMethods = resolver.resolveVtableLayout(Derived);

        // Test: Both should have same number of methods (slots)
        ASSERT_TRUE(baseMethods.size() == derivedMethods.size()) << "Base and Derived should have same vtable size";

        // Test: Method order should be preserved (first, second, third)
        // Skip destructor (first if present)
        size_t baseStart = 0;
        size_t derivedStart = 0;

        if (!baseMethods.empty() && isa<CXXDestructorDecl>(baseMethods[0])) {
            baseStart = 1;
        }
        if (!derivedMethods.empty() && isa<CXXDestructorDecl>(derivedMethods[0])) {
            derivedStart = 1;
        }

        // Check method names are in same order
        for (size_t i = 0; i < baseMethods.size() - baseStart; ++i) {
            auto* baseMethod = baseMethods[baseStart + i];
            auto* derivedMethod = derivedMethods[derivedStart + i];

            ASSERT_TRUE(baseMethod->getNameAsString() == derivedMethod->getNameAsString()) << "Method order must be consistent: " +
                   baseMethod->getNameAsString(;+ " vs " +
                   derivedMethod->getNameAsString());
        }
}

TEST_F(OverrideResolverTest, MultipleOverrides) {
    const char *code = R"(
            class Base {
            public:
                virtual void a();
                virtual void b();
                virtual void c();
            };

            class Derived : public Base {
            public:
                void a() override;
                void b() override;
                void c() override;
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        auto vtableMethods = resolver.resolveVtableLayout(Derived);

        // Count methods from Derived
        int derivedMethodCount = 0;
        for (auto* method : vtableMethods) {
            if (!isa<CXXDestructorDecl>(method) &&
                method->getParent()->getNameAsString() == "Derived") {
                derivedMethodCount++;
            }
        }

        // Test: All 3 methods should be from Derived (all overridden)
        ASSERT_TRUE(derivedMethodCount == 3) << "Expected 3 methods from Derived, got: " + std::to_string(derivedMethodCount;);
}

TEST_F(OverrideResolverTest, PartialOverride) {
    const char *code = R"(
            class Base {
            public:
                virtual void a();
                virtual void b();
                virtual void c();
            };

            class Derived : public Base {
            public:
                void b() override;  // Only override b
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        auto vtableMethods = resolver.resolveVtableLayout(Derived);

        // Count methods from each class
        int baseCount = 0;
        int derivedCount = 0;

        for (auto* method : vtableMethods) {
            if (isa<CXXDestructorDecl>(method)) continue;

            if (method->getParent()->getNameAsString() == "Base") {
                baseCount++;
            } else if (method->getParent()->getNameAsString() == "Derived") {
                derivedCount++;
            }
        }

        // Test: 1 from Derived (b), 2 from Base (a, c)
        ASSERT_TRUE(derivedCount == 1) << "Expected 1 method from Derived";
        ASSERT_TRUE(baseCount == 2) << "Expected 2 methods from Base";
}

TEST_F(OverrideResolverTest, CovariantReturnTypes) {
    const char *code = R"(
            class Base {
            public:
                virtual Base* clone();
            };

            class Derived : public Base {
            public:
                Derived* clone() override;  // Covariant return type
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        auto vtableMethods = resolver.resolveVtableLayout(Derived);

        // Find clone method
        CXXMethodDecl* cloneMethod = nullptr;
        for (auto* method : vtableMethods) {
            if (!isa<CXXDestructorDecl>(method) &&
                method->getNameAsString() == "clone") {
                cloneMethod = method;
                break;
            }
        }

        ASSERT_TRUE(cloneMethod) << "clone method not found";

        // Test: clone should be from Derived (covariant override)
        ASSERT_TRUE(cloneMethod->getParent()->getNameAsString() == "Derived") << "clone should be from Derived (covariant override;");
}

TEST_F(OverrideResolverTest, MethodWithParameters) {
    const char *code = R"(
            class Base {
            public:
                virtual void process(int x, double y);
            };

            class Derived : public Base {
            public:
                void process(int x, double y) override;
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        VirtualMethodAnalyzer analyzer(Context);
        OverrideResolver resolver(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        auto vtableMethods = resolver.resolveVtableLayout(Derived);

        // Find process method
        CXXMethodDecl* processMethod = nullptr;
        for (auto* method : vtableMethods) {
            if (!isa<CXXDestructorDecl>(method) &&
                method->getNameAsString() == "process") {
                processMethod = method;
                break;
            }
        }

        ASSERT_TRUE(processMethod) << "process method not found";

        // Test: process should be from Derived
        ASSERT_TRUE(processMethod->getParent()->getNameAsString() == "Derived") << "process should be from Derived";

        // Test: Should have correct parameter count
        ASSERT_TRUE(processMethod->getNumParams() == 2) << "process should have 2 parameters";
}
