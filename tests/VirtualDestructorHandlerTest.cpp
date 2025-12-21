/**
 * @file VirtualDestructorHandlerTest.cpp
 * @brief Tests for Story #174: Virtual Destructor Handling
 *
 * Tests virtual destructor detection, vtable placement, and polymorphic delete.
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/VirtualDestructorHandler.h"
#include <vector>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

// Test fixture
class VirtualDestructorHandlerTest : public ::testing::Test {
protected:
};

TEST_F(VirtualDestructorHandlerTest, DetectVirtualDestructor) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

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

        ASSERT_TRUE(Base) << "Base class not found";

        // Check that destructor is virtual
        CXXDestructorDecl* Destructor = Base->getDestructor();
        ASSERT_TRUE(Destructor) << "Destructor not found";
        ASSERT_TRUE(handler.isVirtualDestructor(Destructor)) << "Destructor should be detected as virtual";
}

TEST_F(VirtualDestructorHandlerTest, NonVirtualDestructorNotDetected) {
    const char *code = R"(
            class Simple {
            public:
                ~Simple() {}  // Non-virtual
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

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

        ASSERT_TRUE(Simple) << "Simple class not found";

        CXXDestructorDecl* Destructor = Simple->getDestructor();
        ASSERT_TRUE(Destructor) << "Destructor not found";
        ASSERT_TRUE(!handler.isVirtualDestructor(Destructor)) << "Non-virtual destructor should not be detected as virtual";
}

TEST_F(VirtualDestructorHandlerTest, VirtualDestructorInVtable) {
    const char *code = R"(
            class Base {
            public:
                virtual ~Base() {}
                virtual void method() {}
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

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

        ASSERT_TRUE(Base) << "Base class not found";

        // Check that destructor is included when getting vtable methods
        bool hasDestructor = handler.hasVirtualDestructor(Base);
        ASSERT_TRUE(hasDestructor) << "Class with virtual destructor should report hasVirtualDestructor(;");
}

TEST_F(VirtualDestructorHandlerTest, GetDestructorVtableName) {
    const char *code = R"(
            class MyClass {
            public:
                virtual ~MyClass() {}
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

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

        ASSERT_TRUE(MyClass) << "MyClass not found";

        CXXDestructorDecl* Destructor = MyClass->getDestructor();
        ASSERT_TRUE(Destructor) << "Destructor not found";

        std::string vtableName = handler.getDestructorVtableName(Destructor);
        ASSERT_TRUE(vtableName == "destructor") << "Destructor vtable name should be 'destructor'";
}

TEST_F(VirtualDestructorHandlerTest, InheritedVirtualDestructor) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

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

        ASSERT_TRUE(Base) << "Base class not found";
        ASSERT_TRUE(Derived) << "Derived class not found";

        // Both should have virtual destructors
        ASSERT_TRUE(handler.hasVirtualDestructor(Base)) << "Base should have virtual destructor";
        ASSERT_TRUE(handler.hasVirtualDestructor(Derived)) << "Derived should have virtual destructor (inherited;");

        CXXDestructorDecl* DerivedDestructor = Derived->getDestructor();
        ASSERT_TRUE(DerivedDestructor) << "Derived destructor not found";
        ASSERT_TRUE(handler.isVirtualDestructor(DerivedDestructor)) << "Derived destructor should be virtual";
}

TEST_F(VirtualDestructorHandlerTest, ImplicitVirtualDestructor) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

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

        ASSERT_TRUE(Base) << "Base class not found";
        ASSERT_TRUE(Derived) << "Derived class not found";

        // Derived should have virtual destructor even if implicit
        ASSERT_TRUE(handler.hasVirtualDestructor(Derived)) << "Derived with implicit destructor should have virtual destructor";
}

TEST_F(VirtualDestructorHandlerTest, DestructorChaining) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

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

        ASSERT_TRUE(Base) << "Base class not found";
        ASSERT_TRUE(Middle) << "Middle class not found";
        ASSERT_TRUE(Derived) << "Derived class not found";

        // All should have virtual destructors
        ASSERT_TRUE(handler.hasVirtualDestructor(Base)) << "Base should have virtual destructor";
        ASSERT_TRUE(handler.hasVirtualDestructor(Middle)) << "Middle should have virtual destructor";
        ASSERT_TRUE(handler.hasVirtualDestructor(Derived)) << "Derived should have virtual destructor";

        // Check destructor chain exists
        CXXDestructorDecl* DerivedDestructor = Derived->getDestructor();
        ASSERT_TRUE(DerivedDestructor) << "Derived destructor not found";

        // Verify destructor is properly overriding
        ASSERT_TRUE(DerivedDestructor->size_overridden_methods() > 0) << "Derived destructor should override base destructors";
}
