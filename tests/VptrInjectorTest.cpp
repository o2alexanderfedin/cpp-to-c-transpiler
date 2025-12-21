/**
 * @file VptrInjectorTest.cpp
 * @brief Tests for Story #169: Vptr Field Injection in Class Layout
 *
 * Acceptance Criteria:
 * - Vptr injected as first field (offset 0)
 * - Correct pointer type (const-qualified)
 * - Compatible with inheritance
 * - Memory layout tests pass
 * - Unit tests pass (6+ test cases)
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/VirtualMethodAnalyzer.h"
#include "../include/VtableGenerator.h"
#include "../include/VptrInjector.h"
#include "../include/CNodeBuilder.h"
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

// Test 1: Inject vptr in polymorphic class

// Test fixture
class VptrInjectorTest : public ::testing::Test {
protected:
};

TEST_F(VptrInjectorTest, InjectVptrInPolymorphicClass) {
    const char *code = R"(
            class Shape {
            public:
                virtual void draw();
            private:
                double x;
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        CNodeBuilder Builder(Context);
        VirtualMethodAnalyzer analyzer(Context);
        VptrInjector injector(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Shape = findClass(TU, "Shape");
        ASSERT_TRUE(Shape) << "Shape class not found";

        // Test: Class should be polymorphic
        ASSERT_TRUE(analyzer.isPolymorphic(Shape)) << "Shape should be polymorphic";

        // Inject vptr field
        std::vector<FieldDecl*> fields;
        bool injected = injector.injectVptrField(Shape, fields);
        ASSERT_TRUE(injected) << "Vptr injection should succeed";

        // Test: Should have exactly 1 field (vptr)
        ASSERT_TRUE(fields.size() == 1) << "Expected 1 field (vptr;, got: " + std::to_string(fields.size()));

        // Test: First field should be vptr
        ASSERT_TRUE(fields[0]->getNameAsString() == "vptr") << "First field should be named 'vptr'";

        // Test: Vptr should be pointer type
        ASSERT_TRUE(fields[0]->getType()->isPointerType()) << "Vptr should be pointer type";

        // Test: Vptr pointee should be const-qualified (const struct X_vtable*)
        auto pointeeType = fields[0]->getType()->getPointeeType();
        ASSERT_TRUE(pointeeType.isConstQualified()) << "Vptr pointee (vtable struct;should be const-qualified");
}

TEST_F(VptrInjectorTest, NoVptrInNonPolymorphicClass) {
    const char *code = R"(
            class Point {
            private:
                double x, y;
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        CNodeBuilder Builder(Context);
        VirtualMethodAnalyzer analyzer(Context);
        VptrInjector injector(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Point = findClass(TU, "Point");
        ASSERT_TRUE(Point) << "Point class not found";

        // Test: Class should NOT be polymorphic
        ASSERT_TRUE(!analyzer.isPolymorphic(Point)) << "Point should not be polymorphic";

        // Try to inject vptr field
        std::vector<FieldDecl*> fields;
        bool injected = injector.injectVptrField(Point, fields);

        // Test: Injection should not happen for non-polymorphic class
        ASSERT_TRUE(!injected) << "Vptr should not be injected in non-polymorphic class";
        ASSERT_TRUE(fields.empty()) << "Fields should be empty for non-polymorphic class";
}

TEST_F(VptrInjectorTest, VptrAtOffsetZeroInDerivedClass) {
    const char *code = R"(
            class Base {
            public:
                virtual void foo();
            };

            class Derived : public Base {
            private:
                int value;
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        CNodeBuilder Builder(Context);
        VirtualMethodAnalyzer analyzer(Context);
        VptrInjector injector(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Derived = findClass(TU, "Derived");
        ASSERT_TRUE(Derived) << "Derived class not found";

        // Test: Derived class should be polymorphic (inherited virtual)
        ASSERT_TRUE(analyzer.isPolymorphic(Derived)) << "Derived should be polymorphic";

        // Inject vptr field
        std::vector<FieldDecl*> fields;
        bool injected = injector.injectVptrField(Derived, fields);
        ASSERT_TRUE(injected) << "Vptr injection should succeed in Derived";

        // Test: Vptr should be first field (offset 0)
        ASSERT_TRUE(fields.size() >= 1) << "Should have at least vptr field";
        ASSERT_TRUE(fields[0]->getNameAsString() == "vptr") << "First field must be vptr for proper memory layout";
}

TEST_F(VptrInjectorTest, VptrTypeReferencesVtableStruct) {
    const char *code = R"(
            class Shape {
            public:
                virtual void draw();
                virtual double area();
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        CNodeBuilder Builder(Context);
        VirtualMethodAnalyzer analyzer(Context);
        VptrInjector injector(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Shape = findClass(TU, "Shape");
        ASSERT_TRUE(Shape) << "Shape class not found";

        // Inject vptr field
        std::vector<FieldDecl*> fields;
        bool injected = injector.injectVptrField(Shape, fields);
        ASSERT_TRUE(injected) << "Vptr injection should succeed";

        // Test: Vptr type should reference Shape_vtable
        auto vptrType = fields[0]->getType();
        ASSERT_TRUE(vptrType->isPointerType()) << "Vptr must be pointer type";

        auto pointeeType = vptrType->getPointeeType();
        std::string typeName = pointeeType.getAsString();

        // Should be "const struct Shape_vtable"
        ASSERT_TRUE(typeName.find("Shape_vtable") != std::string::npos) << "Vptr should point to Shape_vtable, got: " + typeName;
}

TEST_F(VptrInjectorTest, MultiplePolymorphicClassesGetOwnVptr) {
    const char *code = R"(
            class Shape {
            public:
                virtual void draw();
            };

            class Animal {
            public:
                virtual void speak();
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        CNodeBuilder Builder(Context);
        VirtualMethodAnalyzer analyzer(Context);
        VptrInjector injector(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Shape = findClass(TU, "Shape");
        auto *Animal = findClass(TU, "Animal");
        ASSERT_TRUE(Shape) << "Shape class not found";
        ASSERT_TRUE(Animal) << "Animal class not found";

        // Inject vptr in Shape
        std::vector<FieldDecl*> shapeFields;
        bool shapeInjected = injector.injectVptrField(Shape, shapeFields);
        ASSERT_TRUE(shapeInjected) << "Vptr injection should succeed in Shape";

        // Inject vptr in Animal
        std::vector<FieldDecl*> animalFields;
        bool animalInjected = injector.injectVptrField(Animal, animalFields);
        ASSERT_TRUE(animalInjected) << "Vptr injection should succeed in Animal";

        // Test: Both should have vptr
        ASSERT_TRUE(shapeFields.size() >= 1) << "Shape should have vptr";
        ASSERT_TRUE(animalFields.size() >= 1) << "Animal should have vptr";

        // Test: Vptrs should point to different vtable types
        auto shapeVptrType = shapeFields[0]->getType()->getPointeeType().getAsString();
        auto animalVptrType = animalFields[0]->getType()->getPointeeType().getAsString();

        ASSERT_TRUE(shapeVptrType.find("Shape_vtable") != std::string::npos) << "Shape vptr should reference Shape_vtable";
        ASSERT_TRUE(animalVptrType.find("Animal_vtable") != std::string::npos) << "Animal vptr should reference Animal_vtable";
}

TEST_F(VptrInjectorTest, VptrCombinedWithExistingFields) {
    const char *code = R"(
            class Circle {
            public:
                virtual void draw();
            private:
                double radius;
                int color;
            };
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        auto& Context = AST->getASTContext();
        CNodeBuilder Builder(Context);
        VirtualMethodAnalyzer analyzer(Context);
        VptrInjector injector(Context, analyzer);

        auto *TU = Context.getTranslationUnitDecl();
        auto *Circle = findClass(TU, "Circle");
        ASSERT_TRUE(Circle) << "Circle class not found";

        // Inject vptr and existing fields
        std::vector<FieldDecl*> fields;
        injector.injectVptrField(Circle, fields);

        // Add existing fields
        for (auto *Field : Circle->fields()) {
            FieldDecl *CField = Builder.fieldDecl(Field->getType(), Field->getName());
            fields.push_back(CField);
        }

        // Test: Should have 3 fields: vptr, radius, color
        ASSERT_TRUE(fields.size() == 3) << "Expected 3 fields (vptr + radius + color;, got: " + std::to_string(fields.size()));

        // Test: Vptr must be first
        ASSERT_TRUE(fields[0]->getNameAsString() == "vptr") << "Vptr must be first field (offset 0;");

        // Test: Original fields after vptr
        ASSERT_TRUE(fields[1]->getNameAsString() == "radius") << "Second field should be radius";
        ASSERT_TRUE(fields[2]->getNameAsString() == "color") << "Third field should be color";
}
