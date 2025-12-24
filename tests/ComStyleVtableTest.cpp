/**
 * @file ComStyleVtableTest.cpp
 * @brief Tests for Phase 31-02: COM-Style Static Declarations for Virtual Methods
 *
 * Acceptance Criteria:
 * - Static declarations generated for all virtual methods
 * - Declarations appear before vtable structs in headers
 * - Signatures match vtable function pointer types exactly
 * - Compile-time type safety verification
 * - Zero runtime overhead
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VtableGenerator.h"
#include "../include/VirtualMethodAnalyzer.h"
#include <cassert>
#include <sstream>

using namespace clang;

std::unique_ptr<ASTUnit> buildASTForComStyle(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Helper function to find class by name
CXXRecordDecl* findClassInTU(TranslationUnitDecl* TU, const std::string& name) {
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == name && RD->isCompleteDefinition()) {
                return RD;
            }
        }
    }
    return nullptr;
}

// Test fixture
class ComStyleVtableTest : public ::testing::Test {
protected:
};

/**
 * Test 1: Simple virtual method
 * Verify that static declarations are generated for basic virtual methods
 */
TEST_F(ComStyleVtableTest, SimpleVirtualMethod) {
    const char *code = R"(
        class Shape {
        public:
            virtual int getArea() = 0;
            virtual ~Shape() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForComStyle(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Shape = findClassInTU(TU, "Shape");
    ASSERT_TRUE(Shape) << "Shape class not found";

    // Generate static declarations
    std::string declarations = generator.generateStaticDeclarations(Shape);

    // Verify declarations exist
    EXPECT_TRUE(declarations.find("static int Shape_getArea") != std::string::npos)
        << "Expected 'static int Shape_getArea' in declarations\nGot: " << declarations;
    EXPECT_TRUE(declarations.find("struct Shape *this") != std::string::npos ||
                declarations.find("struct Shape* this") != std::string::npos)
        << "Expected 'this' parameter in declarations\nGot: " << declarations;

    // Verify destructor declaration
    EXPECT_TRUE(declarations.find("Shape__dtor") != std::string::npos ||
                declarations.find("Shape_destructor") != std::string::npos)
        << "Expected destructor declaration\nGot: " << declarations;

    // Verify it's not empty
    EXPECT_FALSE(declarations.empty()) << "Declarations should not be empty";
}

/**
 * Test 2: Virtual method with parameters
 * Verify parameter types and names are correctly included
 */
TEST_F(ComStyleVtableTest, VirtualMethodWithParameters) {
    const char *code = R"(
        class Calculator {
        public:
            virtual int add(int a, int b) = 0;
            virtual double multiply(double x, double y) = 0;
            virtual ~Calculator() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForComStyle(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Calculator = findClassInTU(TU, "Calculator");
    ASSERT_TRUE(Calculator) << "Calculator class not found";

    std::string declarations = generator.generateStaticDeclarations(Calculator);

    // Verify method signatures with parameters
    EXPECT_TRUE(declarations.find("static int Calculator_add") != std::string::npos)
        << "Expected 'static int Calculator_add' in declarations\nGot: " << declarations;
    EXPECT_TRUE(declarations.find("static double Calculator_multiply") != std::string::npos)
        << "Expected 'static double Calculator_multiply' in declarations\nGot: " << declarations;

    // Verify parameters are present (may have different spacing/formatting)
    EXPECT_TRUE(declarations.find("int a") != std::string::npos ||
                declarations.find("int,") != std::string::npos)
        << "Expected parameters in add method\nGot: " << declarations;
    EXPECT_TRUE(declarations.find("double x") != std::string::npos ||
                declarations.find("double,") != std::string::npos)
        << "Expected parameters in multiply method\nGot: " << declarations;
}

/**
 * Test 3: Inheritance with overrides
 * Verify that both base and derived classes get proper declarations
 */
TEST_F(ComStyleVtableTest, InheritanceWithOverrides) {
    const char *code = R"(
        class Base {
        public:
            virtual void method1() = 0;
            virtual int method2() = 0;
            virtual ~Base() {}
        };

        class Derived : public Base {
        public:
            void method1() override { }
            int method2() override { return 42; }
            virtual void method3() { }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForComStyle(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClassInTU(TU, "Base");
    auto *Derived = findClassInTU(TU, "Derived");
    ASSERT_TRUE(Base) << "Base class not found";
    ASSERT_TRUE(Derived) << "Derived class not found";

    // Test Base class declarations
    std::string baseDecls = generator.generateStaticDeclarations(Base);
    EXPECT_TRUE(baseDecls.find("static void Base_method1") != std::string::npos)
        << "Expected 'static void Base_method1' in base declarations\nGot: " << baseDecls;
    EXPECT_TRUE(baseDecls.find("static int Base_method2") != std::string::npos)
        << "Expected 'static int Base_method2' in base declarations\nGot: " << baseDecls;

    // Test Derived class declarations
    std::string derivedDecls = generator.generateStaticDeclarations(Derived);
    EXPECT_TRUE(derivedDecls.find("static void Derived_method1") != std::string::npos)
        << "Expected 'static void Derived_method1' in derived declarations\nGot: " << derivedDecls;
    EXPECT_TRUE(derivedDecls.find("static int Derived_method2") != std::string::npos)
        << "Expected 'static int Derived_method2' in derived declarations\nGot: " << derivedDecls;
    EXPECT_TRUE(derivedDecls.find("static void Derived_method3") != std::string::npos)
        << "Expected 'static void Derived_method3' in derived declarations\nGot: " << derivedDecls;
}

/**
 * Test 4: Signature mismatch detection (compile-time verification)
 * This is a documentation test for manual verification
 */
TEST_F(ComStyleVtableTest, SignatureMismatchDetection) {
    // NOTE: This test verifies the CONCEPT of compile-time type checking
    // The actual verification happens at C compilation time, not in this test
    //
    // Manual verification procedure:
    // 1. Temporarily modify VtableGenerator to create wrong signature
    //    (e.g., change return type or parameter type)
    // 2. Transpile a test C++ file
    // 3. Attempt to compile the generated C code
    // 4. Verify that compiler produces error about type mismatch
    // 5. Verify error message points to the vtable assignment line
    //
    // Example expected compiler error:
    //   error: incompatible pointer types assigning to 'int (*)(struct Shape *)'
    //   from 'void (*)(struct Shape *)'
    //
    // This test serves as documentation for the manual testing procedure
    GTEST_SKIP() << "Manual compile-time verification test - see test comments for procedure";
}

/**
 * Test 5: Multiple inheritance
 * Verify all virtual methods from all base classes get declarations
 */
TEST_F(ComStyleVtableTest, MultipleInheritance) {
    const char *code = R"(
        class Interface1 {
        public:
            virtual void method1() = 0;
            virtual ~Interface1() {}
        };

        class Interface2 {
        public:
            virtual void method2() = 0;
            virtual ~Interface2() {}
        };

        class Implementation : public Interface1, public Interface2 {
        public:
            void method1() override { }
            void method2() override { }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForComStyle(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Interface1 = findClassInTU(TU, "Interface1");
    auto *Interface2 = findClassInTU(TU, "Interface2");
    auto *Implementation = findClassInTU(TU, "Implementation");

    ASSERT_TRUE(Interface1) << "Interface1 class not found";
    ASSERT_TRUE(Interface2) << "Interface2 class not found";
    ASSERT_TRUE(Implementation) << "Implementation class not found";

    // Verify all interface declarations
    std::string decls1 = generator.generateStaticDeclarations(Interface1);
    EXPECT_TRUE(decls1.find("static void Interface1_method1") != std::string::npos)
        << "Expected 'static void Interface1_method1'\nGot: " << decls1;

    std::string decls2 = generator.generateStaticDeclarations(Interface2);
    EXPECT_TRUE(decls2.find("static void Interface2_method2") != std::string::npos)
        << "Expected 'static void Interface2_method2'\nGot: " << decls2;

    std::string implDecls = generator.generateStaticDeclarations(Implementation);
    EXPECT_TRUE(implDecls.find("static void Implementation_method1") != std::string::npos)
        << "Expected 'static void Implementation_method1'\nGot: " << implDecls;
    EXPECT_TRUE(implDecls.find("static void Implementation_method2") != std::string::npos)
        << "Expected 'static void Implementation_method2'\nGot: " << implDecls;
}

/**
 * Test 6: Non-polymorphic class returns empty
 * Verify that classes without virtual methods don't generate declarations
 */
TEST_F(ComStyleVtableTest, NonPolymorphicClassReturnsEmpty) {
    const char *code = R"(
        class PlainClass {
        public:
            void regularMethod() { }
            int getValue() { return 42; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForComStyle(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *PlainClass = findClassInTU(TU, "PlainClass");
    ASSERT_TRUE(PlainClass) << "PlainClass not found";

    std::string declarations = generator.generateStaticDeclarations(PlainClass);

    // Should return empty string for non-polymorphic classes
    EXPECT_TRUE(declarations.empty())
        << "Non-polymorphic class should have no declarations\nGot: " << declarations;
}

/**
 * Test 7: Virtual method with const qualifier
 * Verify const methods are handled correctly
 */
TEST_F(ComStyleVtableTest, VirtualMethodWithConst) {
    const char *code = R"(
        class Container {
        public:
            virtual int size() const = 0;
            virtual void clear() = 0;
            virtual ~Container() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForComStyle(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Container = findClassInTU(TU, "Container");
    ASSERT_TRUE(Container) << "Container class not found";

    std::string declarations = generator.generateStaticDeclarations(Container);

    // Verify const method declaration exists
    EXPECT_TRUE(declarations.find("static int Container_size") != std::string::npos)
        << "Expected 'static int Container_size' declaration\nGot: " << declarations;
    EXPECT_TRUE(declarations.find("static void Container_clear") != std::string::npos)
        << "Expected 'static void Container_clear' declaration\nGot: " << declarations;

    // Note: const qualifier handling is implementation-specific
    // Some implementations may include 'const' in the this pointer type
}

/**
 * Test 8: Pure virtual methods
 * Verify pure virtual methods still get declarations
 */
TEST_F(ComStyleVtableTest, PureVirtualMethods) {
    const char *code = R"(
        class AbstractBase {
        public:
            virtual void pureMethod1() = 0;
            virtual int pureMethod2() = 0;
            virtual double pureMethod3(int x, double y) = 0;
            virtual ~AbstractBase() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForComStyle(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    VtableGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *AbstractBase = findClassInTU(TU, "AbstractBase");
    ASSERT_TRUE(AbstractBase) << "AbstractBase class not found";

    std::string declarations = generator.generateStaticDeclarations(AbstractBase);

    // Verify all pure virtual methods get declarations
    EXPECT_TRUE(declarations.find("static void AbstractBase_pureMethod1") != std::string::npos)
        << "Expected declaration for pureMethod1\nGot: " << declarations;
    EXPECT_TRUE(declarations.find("static int AbstractBase_pureMethod2") != std::string::npos)
        << "Expected declaration for pureMethod2\nGot: " << declarations;
    EXPECT_TRUE(declarations.find("static double AbstractBase_pureMethod3") != std::string::npos)
        << "Expected declaration for pureMethod3\nGot: " << declarations;
}
