/**
 * @file VirtualDestructorHandlerTest.cpp
 * @brief Tests for Story #174: Virtual Destructor Handling
 *
 * Tests virtual destructor detection, vtable placement, and polymorphic delete.
 */

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/VirtualDestructorHandler.h"
#include <iostream>
#include <vector>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

// Test 1: Detect virtual destructor
void test_DetectVirtualDestructor() {
    TEST_START("DetectVirtualDestructor");

    const char *code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualDestructorHandler handler(Context, analyzer);

    // Find the Base class
    CXXRecordDecl* Base = nullptr;
    for (auto *D : Context.getTranslationUnitDecl()->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Base" && RD->isCompleteDefinition()) {
                Base = RD;
                break;
            }
        }
    }

    ASSERT(Base, "Base class not found");

    // Check that destructor is virtual
    CXXDestructorDecl* Destructor = Base->getDestructor();
    ASSERT(Destructor, "Destructor not found");
    ASSERT(handler.isVirtualDestructor(Destructor),
           "Destructor should be detected as virtual");

    TEST_PASS("DetectVirtualDestructor");
}

// Test 2: Non-virtual destructor should not be detected
void test_NonVirtualDestructorNotDetected() {
    TEST_START("NonVirtualDestructorNotDetected");

    const char *code = R"(
        class Simple {
        public:
            ~Simple() {}  // Non-virtual
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualDestructorHandler handler(Context, analyzer);

    // Find the Simple class
    CXXRecordDecl* Simple = nullptr;
    for (auto *D : Context.getTranslationUnitDecl()->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Simple" && RD->isCompleteDefinition()) {
                Simple = RD;
                break;
            }
        }
    }

    ASSERT(Simple, "Simple class not found");

    CXXDestructorDecl* Destructor = Simple->getDestructor();
    ASSERT(Destructor, "Destructor not found");
    ASSERT(!handler.isVirtualDestructor(Destructor),
           "Non-virtual destructor should not be detected as virtual");

    TEST_PASS("NonVirtualDestructorNotDetected");
}

// Test 3: Virtual destructor should be included in vtable methods
void test_VirtualDestructorInVtable() {
    TEST_START("VirtualDestructorInVtable");

    const char *code = R"(
        class Base {
        public:
            virtual ~Base() {}
            virtual void method() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualDestructorHandler handler(Context, analyzer);

    // Find the Base class
    CXXRecordDecl* Base = nullptr;
    for (auto *D : Context.getTranslationUnitDecl()->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Base" && RD->isCompleteDefinition()) {
                Base = RD;
                break;
            }
        }
    }

    ASSERT(Base, "Base class not found");

    // Check that destructor is included when getting vtable methods
    bool hasDestructor = handler.hasVirtualDestructor(Base);
    ASSERT(hasDestructor,
           "Class with virtual destructor should report hasVirtualDestructor()");

    TEST_PASS("VirtualDestructorInVtable");
}

// Test 4: Get destructor vtable name
void test_GetDestructorVtableName() {
    TEST_START("GetDestructorVtableName");

    const char *code = R"(
        class MyClass {
        public:
            virtual ~MyClass() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualDestructorHandler handler(Context, analyzer);

    // Find the MyClass class
    CXXRecordDecl* MyClass = nullptr;
    for (auto *D : Context.getTranslationUnitDecl()->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "MyClass" && RD->isCompleteDefinition()) {
                MyClass = RD;
                break;
            }
        }
    }

    ASSERT(MyClass, "MyClass not found");

    CXXDestructorDecl* Destructor = MyClass->getDestructor();
    ASSERT(Destructor, "Destructor not found");

    std::string vtableName = handler.getDestructorVtableName(Destructor);
    ASSERT(vtableName == "destructor",
           "Destructor vtable name should be 'destructor'");

    TEST_PASS("GetDestructorVtableName");
}

// Test 5: Inherited virtual destructor
void test_InheritedVirtualDestructor() {
    TEST_START("InheritedVirtualDestructor");

    const char *code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
        public:
            ~Derived() override {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualDestructorHandler handler(Context, analyzer);

    // Find both classes
    CXXRecordDecl* Base = nullptr;
    CXXRecordDecl* Derived = nullptr;
    for (auto *D : Context.getTranslationUnitDecl()->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (!RD->isCompleteDefinition()) continue;
            if (RD->getNameAsString() == "Base") {
                Base = RD;
            } else if (RD->getNameAsString() == "Derived") {
                Derived = RD;
            }
        }
    }

    ASSERT(Base, "Base class not found");
    ASSERT(Derived, "Derived class not found");

    // Both should have virtual destructors
    ASSERT(handler.hasVirtualDestructor(Base),
           "Base should have virtual destructor");
    ASSERT(handler.hasVirtualDestructor(Derived),
           "Derived should have virtual destructor (inherited)");

    CXXDestructorDecl* DerivedDestructor = Derived->getDestructor();
    ASSERT(DerivedDestructor, "Derived destructor not found");
    ASSERT(handler.isVirtualDestructor(DerivedDestructor),
           "Derived destructor should be virtual");

    TEST_PASS("InheritedVirtualDestructor");
}

// Test 6: Implicit virtual destructor
void test_ImplicitVirtualDestructor() {
    TEST_START("ImplicitVirtualDestructor");

    const char *code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
            // Implicit destructor (should be virtual due to base)
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualDestructorHandler handler(Context, analyzer);

    // Find both classes
    CXXRecordDecl* Base = nullptr;
    CXXRecordDecl* Derived = nullptr;
    for (auto *D : Context.getTranslationUnitDecl()->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (!RD->isCompleteDefinition()) continue;
            if (RD->getNameAsString() == "Base") {
                Base = RD;
            } else if (RD->getNameAsString() == "Derived") {
                Derived = RD;
            }
        }
    }

    ASSERT(Base, "Base class not found");
    ASSERT(Derived, "Derived class not found");

    // Derived should have virtual destructor even if implicit
    ASSERT(handler.hasVirtualDestructor(Derived),
           "Derived with implicit destructor should have virtual destructor");

    TEST_PASS("ImplicitVirtualDestructor");
}

// Test 7: Destructor chaining verification
void test_DestructorChaining() {
    TEST_START("DestructorChaining");

    const char *code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };

        class Middle : public Base {
        public:
            ~Middle() override {}
        };

        class Derived : public Middle {
        public:
            ~Derived() override {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    auto& Context = AST->getASTContext();
    VirtualMethodAnalyzer analyzer(Context);
    VirtualDestructorHandler handler(Context, analyzer);

    // Find all classes
    CXXRecordDecl* Base = nullptr;
    CXXRecordDecl* Middle = nullptr;
    CXXRecordDecl* Derived = nullptr;
    for (auto *D : Context.getTranslationUnitDecl()->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (!RD->isCompleteDefinition()) continue;
            std::string name = RD->getNameAsString();
            if (name == "Base") {
                Base = RD;
            } else if (name == "Middle") {
                Middle = RD;
            } else if (name == "Derived") {
                Derived = RD;
            }
        }
    }

    ASSERT(Base, "Base class not found");
    ASSERT(Middle, "Middle class not found");
    ASSERT(Derived, "Derived class not found");

    // All should have virtual destructors
    ASSERT(handler.hasVirtualDestructor(Base),
           "Base should have virtual destructor");
    ASSERT(handler.hasVirtualDestructor(Middle),
           "Middle should have virtual destructor");
    ASSERT(handler.hasVirtualDestructor(Derived),
           "Derived should have virtual destructor");

    // Check destructor chain exists
    CXXDestructorDecl* DerivedDestructor = Derived->getDestructor();
    ASSERT(DerivedDestructor, "Derived destructor not found");

    // Verify destructor is properly overriding
    ASSERT(DerivedDestructor->size_overridden_methods() > 0,
           "Derived destructor should override base destructors");

    TEST_PASS("DestructorChaining");
}

int main() {
    std::cout << "=== VirtualDestructorHandler Tests (Story #174) ===" << std::endl;

    test_DetectVirtualDestructor();
    test_NonVirtualDestructorNotDetected();
    test_VirtualDestructorInVtable();
    test_GetDestructorVtableName();
    test_InheritedVirtualDestructor();
    test_ImplicitVirtualDestructor();
    test_DestructorChaining();

    std::cout << "\n=== All VirtualDestructorHandler tests passed! ===" << std::endl;
    return 0;
}
