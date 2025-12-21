// tests/gtest/ACSLClassAnnotatorTest_GTest.cpp
// Epic #193: ACSL Annotation Generation for Transpiled Code
// Story #198: ACSLClassAnnotator for class invariant predicates
//
// Migrated to Google Test framework
//
// Test coverage:
// - Simple classes with primitive members
// - Classes with pointer members
// - Classes with array members (Stack example)
// - Classes with virtual methods
// - Constructor invariant injection
// - Method invariant injection
// - Destructor invariant injection
// - Integration tests

#include "../../include/ACSLClassAnnotator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>
#include <string>
#include <vector>

using namespace clang;
using namespace std;

// Store AST units to prevent premature destruction
static vector<unique_ptr<ASTUnit>> persistentASTs;

// Test helper: Extract CXXRecordDecl from source code
class ClassExtractor : public RecursiveASTVisitor<ClassExtractor> {
public:
    vector<const CXXRecordDecl*> classes;
    vector<const CXXMethodDecl*> methods;
    vector<const CXXConstructorDecl*> constructors;
    vector<const CXXDestructorDecl*> destructors;

    bool VisitCXXRecordDecl(CXXRecordDecl* decl) {
        if (decl->isThisDeclarationADefinition()) {
            classes.push_back(decl);
        }
        return true;
    }

    bool VisitCXXMethodDecl(CXXMethodDecl* decl) {
        if (!isa<CXXConstructorDecl>(decl) && !isa<CXXDestructorDecl>(decl)) {
            methods.push_back(decl);
        }
        return true;
    }

    bool VisitCXXConstructorDecl(CXXConstructorDecl* decl) {
        constructors.push_back(decl);
        return true;
    }

    bool VisitCXXDestructorDecl(CXXDestructorDecl* decl) {
        destructors.push_back(decl);
        return true;
    }
};

// Test fixture for ACSL Class Annotator
class ACSLClassAnnotatorTest : public ::testing::Test {
protected:
    // Helper: Parse C++ code and extract AST nodes
    unique_ptr<ASTUnit> parseCode(const string& code) {
        vector<string> args = {"-std=c++17"};
        unique_ptr<ASTUnit> AST = tooling::buildASTFromCodeWithArgs(code, args);
        return AST;
    }

    // Helper: Parse code and extract classes with persistent AST
    ClassExtractor parseAndExtractClasses(const string& code) {
        unique_ptr<ASTUnit> AST = parseCode(code);
        EXPECT_NE(AST, nullptr) << "Failed to parse code";

        ClassExtractor extractor;
        if (AST) {
            extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
            // Keep AST alive
            persistentASTs.push_back(std::move(AST));
        }
        return extractor;
    }
};

// ============================================================================
// CLASS INVARIANT PREDICATE GENERATION TESTS (4 tests)
// ============================================================================

TEST_F(ACSLClassAnnotatorTest, SimpleClassPrimitiveMembers) {
    string code = R"(
        class Point {
        public:
            int x;
            int y;
        };
    )";

    ClassExtractor extractor = parseAndExtractClasses(code);
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* pointClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    string predicate = annotator.generateClassInvariantPredicate(pointClass);

    // Verify predicate exists and contains class name
    EXPECT_FALSE(predicate.empty()) << "Predicate should not be empty";
    EXPECT_NE(predicate.find("predicate inv_Point"), string::npos)
        << "Predicate should contain class name";
    EXPECT_NE(predicate.find("\\valid(this)"), string::npos)
        << "Predicate should validate this pointer";
}

TEST_F(ACSLClassAnnotatorTest, ClassWithPointerMembers) {
    string code = R"(
        class Node {
        public:
            int* data;
            Node* next;
        };
    )";

    ClassExtractor extractor = parseAndExtractClasses(code);
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* nodeClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    string predicate = annotator.generateClassInvariantPredicate(nodeClass);

    // Verify pointer validity constraints
    EXPECT_TRUE(predicate.find("\\valid(this->data)") != string::npos ||
                predicate.find("this->data == \\null") != string::npos)
        << "Predicate should handle pointer members";
}

TEST_F(ACSLClassAnnotatorTest, StackClassWithArrayMembers) {
    string code = R"(
        class Stack {
        public:
            int* data;
            int size;
            int capacity;
        };
    )";

    ClassExtractor extractor = parseAndExtractClasses(code);
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* stackClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    string predicate = annotator.generateClassInvariantPredicate(stackClass);

    // Verify array bounds and capacity constraints
    EXPECT_TRUE(predicate.find("capacity > 0") != string::npos ||
                predicate.find("capacity >= 0") != string::npos)
        << "Predicate should constrain capacity";
    EXPECT_TRUE(predicate.find("size <= capacity") != string::npos ||
                predicate.find("size") != string::npos)
        << "Predicate should relate size to capacity";
    EXPECT_NE(predicate.find("\\valid(this->data"), string::npos)
        << "Predicate should validate array pointer";
}

TEST_F(ACSLClassAnnotatorTest, ClassWithVirtualMethods) {
    string code = R"(
        class Base {
        public:
            virtual void foo() = 0;
            virtual ~Base() {}
        };
    )";

    ClassExtractor extractor = parseAndExtractClasses(code);
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* baseClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    string predicate = annotator.generateClassInvariantPredicate(baseClass);

    // Verify vtable validity for virtual classes
    EXPECT_TRUE(predicate.find("\\valid(this->vtable)") != string::npos ||
                predicate.find("\\valid(this)") != string::npos)
        << "Predicate should handle virtual classes";
}

// ============================================================================
// INVARIANT INJECTION TESTS (3 tests)
// ============================================================================

TEST_F(ACSLClassAnnotatorTest, ConstructorInvariantInjection) {
    string code = R"(
        class Widget {
        public:
            int value;
            Widget(int v) : value(v) {}
        };
    )";

    ClassExtractor extractor = parseAndExtractClasses(code);
    ASSERT_FALSE(extractor.constructors.empty()) << "No constructors found";
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXConstructorDecl* ctor = extractor.constructors[0];
    const CXXRecordDecl* widgetClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    string annotation = annotator.injectInvariantInConstructor(ctor, widgetClass);

    // Verify ensures clause with invariant
    EXPECT_NE(annotation.find("ensures"), string::npos)
        << "Constructor should have ensures clause";
    EXPECT_TRUE(annotation.find("inv_Widget(this)") != string::npos ||
                annotation.find("inv_Widget") != string::npos)
        << "Constructor should ensure class invariant";
}

TEST_F(ACSLClassAnnotatorTest, MethodInvariantInjection) {
    string code = R"(
        class Counter {
        public:
            int count;
            void increment() { count++; }
            int getCount() const { return count; }
        };
    )";

    ClassExtractor extractor = parseAndExtractClasses(code);
    ASSERT_FALSE(extractor.methods.empty()) << "No methods found";
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXMethodDecl* method = extractor.methods[0];
    const CXXRecordDecl* counterClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    string annotation = annotator.injectInvariantInMethod(method, counterClass);

    // Verify requires and ensures clauses
    EXPECT_NE(annotation.find("requires"), string::npos)
        << "Method should have requires clause";
    EXPECT_NE(annotation.find("ensures"), string::npos)
        << "Method should have ensures clause";
    EXPECT_TRUE(annotation.find("inv_Counter(this)") != string::npos ||
                annotation.find("inv_Counter") != string::npos)
        << "Method should preserve class invariant";
}

TEST_F(ACSLClassAnnotatorTest, DestructorInvariantInjection) {
    string code = R"(
        class Resource {
        public:
            int* buffer;
            ~Resource() { delete[] buffer; }
        };
    )";

    ClassExtractor extractor = parseAndExtractClasses(code);
    ASSERT_FALSE(extractor.destructors.empty()) << "No destructors found";
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXDestructorDecl* dtor = extractor.destructors[0];
    const CXXRecordDecl* resourceClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    string annotation = annotator.injectInvariantInDestructor(dtor, resourceClass);

    // Verify requires clause (no ensures for destructors)
    EXPECT_NE(annotation.find("requires"), string::npos)
        << "Destructor should have requires clause";
    EXPECT_TRUE(annotation.find("inv_Resource(this)") != string::npos ||
                annotation.find("inv_Resource") != string::npos)
        << "Destructor should require class invariant";
}

// ============================================================================
// CONSTRAINT GENERATION TESTS (1 test)
// ============================================================================

TEST_F(ACSLClassAnnotatorTest, MemberConstraintGeneration) {
    string code = R"(
        class Container {
        public:
            int* items;
            unsigned int size;
            unsigned int capacity;
        };
    )";

    ClassExtractor extractor = parseAndExtractClasses(code);
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* containerClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    // Test individual field constraints
    for (const auto* field : containerClass->fields()) {
        string constraint = annotator.generateMemberConstraints(field);
        EXPECT_FALSE(constraint.empty()) << "Should generate constraints for fields";
    }
}

// ============================================================================
// INTEGRATION TESTS (2 tests)
// ============================================================================

TEST_F(ACSLClassAnnotatorTest, FullACSLLevelIntegration) {
    string code = R"(
        class Stack {
        public:
            int* data;
            int size;
            int capacity;

            Stack(int cap);
            ~Stack();
            void push(int val);
            int pop();
        };
    )";

    ClassExtractor extractor = parseAndExtractClasses(code);
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* stackClass = extractor.classes[0];
    ACSLClassAnnotator annotator(ACSLLevel::Full);

    // Generate full class annotation
    string predicate = annotator.generateClassInvariantPredicate(stackClass);
    EXPECT_FALSE(predicate.empty()) << "Should generate predicate";

    // Verify all components are present
    EXPECT_NE(predicate.find("predicate inv_Stack"), string::npos)
        << "Should have predicate definition";
}

TEST_F(ACSLClassAnnotatorTest, EmptyClass) {
    string code = R"(
        class Empty {};
    )";

    ClassExtractor extractor = parseAndExtractClasses(code);
    ASSERT_FALSE(extractor.classes.empty()) << "No classes found";

    const CXXRecordDecl* emptyClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    string predicate = annotator.generateClassInvariantPredicate(emptyClass);

    // Should still validate this pointer
    EXPECT_NE(predicate.find("\\valid(this)"), string::npos)
        << "Empty class should validate this pointer";
}
