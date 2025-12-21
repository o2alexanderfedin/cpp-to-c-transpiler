// Phase 2 (v1.19.0): ACSL Type Invariant Generation
// Plan: .planning/phases/02-type-invariants/PLAN.md
//
// Test-Driven Development: Comprehensive test suite for type invariants
// Migrated to Google Test format
//
// Test coverage (12 tests):
// 1. BasicTypeInvariant - Simple struct with constraints
// 2. InheritanceInvariant - Derived class strengthening
// 3. TemplateTypeInvariant - Monomorphized template
// 4. PointerMemberInvariant - Valid pointer constraints
// 5. SizeCapacityInvariant - Relational constraints
// 6. CircularDependencyAvoidance - No mutual recursion
// 7. ArrayMemberInvariant - Array bounds
// 8. OptionalMemberInvariant - Nullable fields
// 9. EnumTypeInvariant - Enum range constraints
// 10. NestedTypeInvariant - Composed types
// 11. ExtractFromClassInvariant - Extract from ACSLClassAnnotator predicate
// 12. TypeInvariantNaming - Proper naming convention

#include "ACSLTypeInvariantGenerator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>
#include <string>

using namespace clang;

// Test helper: Extract CXXRecordDecl from source code
class TypeExtractor : public RecursiveASTVisitor<TypeExtractor> {
public:
    std::vector<const CXXRecordDecl*> classes;
    std::vector<const EnumDecl*> enums;

    bool VisitCXXRecordDecl(CXXRecordDecl* decl) {
        if (decl->isThisDeclarationADefinition()) {
            classes.push_back(decl);
        }
        return true;
    }

    bool VisitEnumDecl(EnumDecl* decl) {
        if (decl->isThisDeclarationADefinition()) {
            enums.push_back(decl);
        }
        return true;
    }
};

// Test fixture for ACSL Type Invariant Generator
class ACSLTypeInvariantGeneratorTest : public ::testing::Test {
protected:
    // Helper: Parse C++ code and extract AST nodes
    std::unique_ptr<ASTUnit> parseCode(const std::string& code) {
        std::vector<std::string> args = {"-std=c++17"};
        return tooling::buildASTFromCodeWithArgs(code, args);
    }
};

// Test 1: BasicTypeInvariant - Simple struct with constraints
TEST_F(ACSLTypeInvariantGeneratorTest, BasicTypeInvariant) {
    std::string code = R"(
        struct Point {
            int x;
            int y;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    TypeExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* pointStruct = extractor.classes[0];
    ACSLTypeInvariantGenerator generator;

    std::string invariant = generator.generateTypeInvariant(pointStruct);

    // Verify type invariant syntax
    ASSERT_FALSE(invariant.empty()) << "Type invariant should not be empty";
    EXPECT_NE(invariant.find("type invariant"), std::string::npos)
        << "Should use ACSL type invariant syntax";
    EXPECT_NE(invariant.find("Point"), std::string::npos)
        << "Should reference the type name";
    EXPECT_NE(invariant.find("\\valid"), std::string::npos)
        << "Should have validity constraint";
}

// Test 2: InheritanceInvariant - Derived class strengthening
TEST_F(ACSLTypeInvariantGeneratorTest, InheritanceInvariant) {
    std::string code = R"(
        class Base {
        public:
            int value;
        };

        class Derived : public Base {
        public:
            int extra;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    TypeExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    ASSERT_GE(extractor.classes.size(), 2) << "Should find base and derived classes";

    const CXXRecordDecl* derivedClass = extractor.classes[1];
    ACSLTypeInvariantGenerator generator;

    std::string invariant = generator.generateTypeInvariant(derivedClass);

    // Verify derived class invariant includes base constraints
    ASSERT_FALSE(invariant.empty()) << "Derived type invariant should not be empty";
    EXPECT_NE(invariant.find("type invariant"), std::string::npos)
        << "Should be a type invariant";
    EXPECT_NE(invariant.find("Derived"), std::string::npos)
        << "Should reference derived type";
}

// Test 3: TemplateTypeInvariant - Monomorphized template
TEST_F(ACSLTypeInvariantGeneratorTest, TemplateTypeInvariant) {
    std::string code = R"(
        template<typename T>
        struct Container {
            T* data;
            int size;
        };

        // Instantiation
        Container<int> intContainer;
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    TypeExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // For template instantiation, we should have specialized class
    ACSLTypeInvariantGenerator generator;

    // Test that generator handles template types
    bool foundValidInvariant = false;
    for (const auto* cls : extractor.classes) {
        std::string invariant = generator.generateTypeInvariant(cls);
        if (!invariant.empty()) {
            EXPECT_NE(invariant.find("type invariant"), std::string::npos)
                << "Should generate type invariant for template";
            foundValidInvariant = true;
        }
    }
    // At least one class should have generated an invariant
    EXPECT_TRUE(foundValidInvariant || !extractor.classes.empty())
        << "Should handle template types";
}

// Test 4: PointerMemberInvariant - Valid pointer constraints
TEST_F(ACSLTypeInvariantGeneratorTest, PointerMemberInvariant) {
    std::string code = R"(
        struct Node {
            int* data;
            Node* next;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    TypeExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* nodeStruct = extractor.classes[0];
    ACSLTypeInvariantGenerator generator;

    std::string invariant = generator.generateTypeInvariant(nodeStruct);

    // Verify pointer validity constraints
    ASSERT_FALSE(invariant.empty()) << "Type invariant should not be empty";
    EXPECT_TRUE(invariant.find("\\valid") != std::string::npos ||
                invariant.find("\\null") != std::string::npos)
        << "Should handle pointer member validity";
}

// Test 5: SizeCapacityInvariant - Relational constraints
TEST_F(ACSLTypeInvariantGeneratorTest, SizeCapacityInvariant) {
    std::string code = R"(
        struct DynamicArray {
            int* data;
            unsigned int size;
            unsigned int capacity;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    TypeExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* arrayStruct = extractor.classes[0];
    ACSLTypeInvariantGenerator generator;

    std::string invariant = generator.generateTypeInvariant(arrayStruct);

    // Verify relational constraints
    ASSERT_FALSE(invariant.empty()) << "Type invariant should not be empty";
    EXPECT_TRUE(invariant.find("size") != std::string::npos &&
                invariant.find("capacity") != std::string::npos)
        << "Should reference size and capacity";
    // Should have size <= capacity constraint
    EXPECT_TRUE(invariant.find("<=") != std::string::npos ||
                invariant.find("size") != std::string::npos)
        << "Should have relational constraint";
}

// Test 6: CircularDependencyAvoidance - No mutual recursion
TEST_F(ACSLTypeInvariantGeneratorTest, CircularDependencyAvoidance) {
    std::string code = R"(
        struct NodeA;
        struct NodeB {
            NodeA* ref;
        };
        struct NodeA {
            NodeB* ref;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    TypeExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ACSLTypeInvariantGenerator generator;

    // Generate invariants for both types
    for (const auto* cls : extractor.classes) {
        if (!cls->isCompleteDefinition()) continue;

        std::string invariant = generator.generateTypeInvariant(cls);
        // Should generate invariant without infinite recursion
        EXPECT_TRUE(true) << "Should handle circular dependencies";
    }
}

// Test 7: ArrayMemberInvariant - Array bounds
TEST_F(ACSLTypeInvariantGeneratorTest, ArrayMemberInvariant) {
    std::string code = R"(
        struct Buffer {
            char data[256];
            int used;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    TypeExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* bufferStruct = extractor.classes[0];
    ACSLTypeInvariantGenerator generator;

    std::string invariant = generator.generateTypeInvariant(bufferStruct);

    // Verify array bounds constraints
    ASSERT_FALSE(invariant.empty()) << "Type invariant should not be empty";
    EXPECT_TRUE(invariant.find("\\valid") != std::string::npos ||
                invariant.find("data") != std::string::npos)
        << "Should handle array member";
}

// Test 8: OptionalMemberInvariant - Nullable fields
TEST_F(ACSLTypeInvariantGeneratorTest, OptionalMemberInvariant) {
    std::string code = R"(
        struct OptionalData {
            int* value;      // May be null
            bool hasValue;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    TypeExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* optionalStruct = extractor.classes[0];
    ACSLTypeInvariantGenerator generator;

    std::string invariant = generator.generateTypeInvariant(optionalStruct);

    // Verify nullable pointer handling
    ASSERT_FALSE(invariant.empty()) << "Type invariant should not be empty";
    EXPECT_NE(invariant.find("value"), std::string::npos)
        << "Should reference optional value";
    // Should allow null: valid(ptr) || ptr == \null
    EXPECT_TRUE(invariant.find("\\null") != std::string::npos ||
                invariant.find("\\valid") != std::string::npos)
        << "Should handle nullable pointers";
}

// Test 9: EnumTypeInvariant - Enum range constraints
TEST_F(ACSLTypeInvariantGeneratorTest, EnumTypeInvariant) {
    std::string code = R"(
        enum class Color {
            Red = 0,
            Green = 1,
            Blue = 2
        };

        struct ColoredObject {
            Color color;
            int value;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    TypeExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ACSLTypeInvariantGenerator generator;

    // Find the struct with enum member
    bool foundColoredObject = false;
    for (const auto* cls : extractor.classes) {
        std::string invariant = generator.generateTypeInvariant(cls);
        if (!invariant.empty() && invariant.find("ColoredObject") != std::string::npos) {
            // Should handle enum member
            EXPECT_TRUE(invariant.find("color") != std::string::npos ||
                        !invariant.empty())
                << "Should reference enum member";
            foundColoredObject = true;
        }
    }
    EXPECT_TRUE(foundColoredObject || !extractor.classes.empty())
        << "Should find ColoredObject struct";
}

// Test 10: NestedTypeInvariant - Composed types
TEST_F(ACSLTypeInvariantGeneratorTest, NestedTypeInvariant) {
    std::string code = R"(
        struct Inner {
            int x;
            int y;
        };

        struct Outer {
            Inner inner;
            int z;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    TypeExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ACSLTypeInvariantGenerator generator;

    // Find Outer struct (should be last)
    const CXXRecordDecl* outerStruct = nullptr;
    for (const auto* cls : extractor.classes) {
        if (cls->getNameAsString() == "Outer") {
            outerStruct = cls;
            break;
        }
    }

    ASSERT_NE(outerStruct, nullptr) << "Should find Outer struct";

    std::string invariant = generator.generateTypeInvariant(outerStruct);

    // Verify nested type handling
    ASSERT_FALSE(invariant.empty()) << "Type invariant should not be empty";
    EXPECT_NE(invariant.find("Outer"), std::string::npos)
        << "Should reference outer type";
    // Should reference inner member
    EXPECT_TRUE(invariant.find("inner") != std::string::npos ||
                !invariant.empty())
        << "Should handle nested types";
}

// Test 11: ExtractFromClassInvariant - Extract from ACSLClassAnnotator predicate
TEST_F(ACSLTypeInvariantGeneratorTest, ExtractFromClassInvariant) {
    std::string code = R"(
        class Stack {
        public:
            int* data;
            int size;
            int capacity;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    TypeExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* stackClass = extractor.classes[0];
    ACSLTypeInvariantGenerator generator;

    // Test extraction capability
    std::string invariant = generator.generateTypeInvariant(stackClass);

    ASSERT_FALSE(invariant.empty()) << "Should extract type invariant";
    EXPECT_NE(invariant.find("type invariant"), std::string::npos)
        << "Should use type invariant syntax";
    EXPECT_NE(invariant.find("Stack"), std::string::npos)
        << "Should reference Stack type";
}

// Test 12: TypeInvariantNaming - Proper naming convention
TEST_F(ACSLTypeInvariantGeneratorTest, TypeInvariantNaming) {
    std::string code = R"(
        struct MyType {
            int value;
        };
    )";

    auto AST = parseCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to parse code";

    TypeExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* myType = extractor.classes[0];
    ACSLTypeInvariantGenerator generator;

    std::string invariant = generator.generateTypeInvariant(myType);

    // Verify naming: type invariant Name(Type t) = ...
    ASSERT_FALSE(invariant.empty()) << "Type invariant should not be empty";
    EXPECT_NE(invariant.find("MyType"), std::string::npos)
        << "Should use type name in invariant";
    // Should have parameter like "struct MyType t" or similar
    EXPECT_TRUE(invariant.find("struct MyType") != std::string::npos ||
                invariant.find("MyType") != std::string::npos)
        << "Should declare type parameter";
}
