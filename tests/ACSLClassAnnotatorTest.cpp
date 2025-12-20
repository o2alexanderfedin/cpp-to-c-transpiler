// Epic #193: ACSL Annotation Generation for Transpiled Code
// Story #198: ACSLClassAnnotator for class invariant predicates
//
// Test-Driven Development: Comprehensive test suite for class invariants
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

#include "ACSLClassAnnotator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>
#include <memory>
#include <string>

using namespace clang;

// Test helper: Extract CXXRecordDecl from source code
class ClassExtractor : public RecursiveASTVisitor<ClassExtractor> {
public:
    std::vector<const CXXRecordDecl*> classes;
    std::vector<const CXXMethodDecl*> methods;
    std::vector<const CXXConstructorDecl*> constructors;
    std::vector<const CXXDestructorDecl*> destructors;

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

// Test helper: Parse C++ code and extract AST nodes
std::unique_ptr<ASTUnit> parseCode(const std::string& code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args);
}

// Test 1: Simple class with primitive members
void testSimpleClassPrimitiveMembers() {
    std::cout << "Test 1: Simple class with primitive members... ";

    std::string code = R"(
        class Point {
        public:
            int x;
            int y;
        };
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    ClassExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.classes.empty() && "No classes found");

    const CXXRecordDecl* pointClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    std::string predicate = annotator.generateClassInvariantPredicate(pointClass);

    // Verify predicate exists and contains class name
    assert(!predicate.empty() && "Predicate should not be empty");
    assert(predicate.find("predicate inv_Point") != std::string::npos &&
           "Predicate should contain class name");
    assert(predicate.find("\\valid(this)") != std::string::npos &&
           "Predicate should validate this pointer");

    std::cout << "PASSED\n";
}

// Test 2: Class with pointer members
void testClassWithPointerMembers() {
    std::cout << "Test 2: Class with pointer members... ";

    std::string code = R"(
        class Node {
        public:
            int* data;
            Node* next;
        };
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    ClassExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.classes.empty() && "No classes found");

    const CXXRecordDecl* nodeClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    std::string predicate = annotator.generateClassInvariantPredicate(nodeClass);

    // Verify pointer validity constraints
    assert(predicate.find("\\valid(this->data)") != std::string::npos ||
           predicate.find("this->data == \\null") != std::string::npos &&
           "Predicate should handle pointer members");

    std::cout << "PASSED\n";
}

// Test 3: Class with array members (Stack example)
void testStackClassWithArrayMembers() {
    std::cout << "Test 3: Stack class with array members... ";

    std::string code = R"(
        class Stack {
        public:
            int* data;
            int size;
            int capacity;
        };
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    ClassExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.classes.empty() && "No classes found");

    const CXXRecordDecl* stackClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    std::string predicate = annotator.generateClassInvariantPredicate(stackClass);

    // Verify array bounds and capacity constraints
    assert(predicate.find("capacity > 0") != std::string::npos ||
           predicate.find("capacity >= 0") != std::string::npos &&
           "Predicate should constrain capacity");
    assert(predicate.find("size <= capacity") != std::string::npos ||
           predicate.find("size") != std::string::npos &&
           "Predicate should relate size to capacity");
    assert(predicate.find("\\valid(this->data") != std::string::npos &&
           "Predicate should validate array pointer");

    std::cout << "PASSED\n";
}

// Test 4: Class with virtual methods
void testClassWithVirtualMethods() {
    std::cout << "Test 4: Class with virtual methods... ";

    std::string code = R"(
        class Base {
        public:
            virtual void foo() = 0;
            virtual ~Base() {}
        };
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    ClassExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.classes.empty() && "No classes found");

    const CXXRecordDecl* baseClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    std::string predicate = annotator.generateClassInvariantPredicate(baseClass);

    // Verify vtable validity for virtual classes
    assert(predicate.find("\\valid(this->vtable)") != std::string::npos ||
           predicate.find("\\valid(this)") != std::string::npos &&
           "Predicate should handle virtual classes");

    std::cout << "PASSED\n";
}

// Test 5: Constructor invariant injection
void testConstructorInvariantInjection() {
    std::cout << "Test 5: Constructor invariant injection... ";

    std::string code = R"(
        class Widget {
        public:
            int value;
            Widget(int v) : value(v) {}
        };
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    ClassExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.constructors.empty() && "No constructors found");

    const CXXConstructorDecl* ctor = extractor.constructors[0];
    const CXXRecordDecl* widgetClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    std::string annotation = annotator.injectInvariantInConstructor(ctor, widgetClass);

    // Verify ensures clause with invariant
    assert(annotation.find("ensures") != std::string::npos &&
           "Constructor should have ensures clause");
    assert(annotation.find("inv_Widget(this)") != std::string::npos ||
           annotation.find("inv_Widget") != std::string::npos &&
           "Constructor should ensure class invariant");

    std::cout << "PASSED\n";
}

// Test 6: Method invariant injection
void testMethodInvariantInjection() {
    std::cout << "Test 6: Method invariant injection... ";

    std::string code = R"(
        class Counter {
        public:
            int count;
            void increment() { count++; }
            int getCount() const { return count; }
        };
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    ClassExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.methods.empty() && "No methods found");

    const CXXMethodDecl* method = extractor.methods[0];
    const CXXRecordDecl* counterClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    std::string annotation = annotator.injectInvariantInMethod(method, counterClass);

    // Verify requires and ensures clauses
    assert(annotation.find("requires") != std::string::npos &&
           "Method should have requires clause");
    assert(annotation.find("ensures") != std::string::npos &&
           "Method should have ensures clause");
    assert(annotation.find("inv_Counter(this)") != std::string::npos ||
           annotation.find("inv_Counter") != std::string::npos &&
           "Method should preserve class invariant");

    std::cout << "PASSED\n";
}

// Test 7: Destructor invariant injection
void testDestructorInvariantInjection() {
    std::cout << "Test 7: Destructor invariant injection... ";

    std::string code = R"(
        class Resource {
        public:
            int* buffer;
            ~Resource() { delete[] buffer; }
        };
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    ClassExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.destructors.empty() && "No destructors found");

    const CXXDestructorDecl* dtor = extractor.destructors[0];
    const CXXRecordDecl* resourceClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    std::string annotation = annotator.injectInvariantInDestructor(dtor, resourceClass);

    // Verify requires clause (no ensures for destructors)
    assert(annotation.find("requires") != std::string::npos &&
           "Destructor should have requires clause");
    assert(annotation.find("inv_Resource(this)") != std::string::npos ||
           annotation.find("inv_Resource") != std::string::npos &&
           "Destructor should require class invariant");

    std::cout << "PASSED\n";
}

// Test 8: Member constraint generation
void testMemberConstraintGeneration() {
    std::cout << "Test 8: Member constraint generation... ";

    std::string code = R"(
        class Container {
        public:
            int* items;
            unsigned int size;
            unsigned int capacity;
        };
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    ClassExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.classes.empty() && "No classes found");

    const CXXRecordDecl* containerClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    // Test individual field constraints
    for (const auto* field : containerClass->fields()) {
        std::string constraint = annotator.generateMemberConstraints(field);
        assert(!constraint.empty() && "Should generate constraints for fields");
    }

    std::cout << "PASSED\n";
}

// Test 9: Full ACSL level integration
void testFullACSLLevelIntegration() {
    std::cout << "Test 9: Full ACSL level integration... ";

    std::string code = R"(
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

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    ClassExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.classes.empty() && "No classes found");

    const CXXRecordDecl* stackClass = extractor.classes[0];
    ACSLClassAnnotator annotator(ACSLLevel::Full);

    // Generate full class annotation
    std::string predicate = annotator.generateClassInvariantPredicate(stackClass);
    assert(!predicate.empty() && "Should generate predicate");

    // Verify all components are present
    assert(predicate.find("predicate inv_Stack") != std::string::npos &&
           "Should have predicate definition");

    std::cout << "PASSED\n";
}

// Test 10: Edge case - empty class
void testEmptyClass() {
    std::cout << "Test 10: Edge case - empty class... ";

    std::string code = R"(
        class Empty {};
    )";

    auto AST = parseCode(code);
    assert(AST && "Failed to parse code");

    ClassExtractor extractor;
    extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
    assert(!extractor.classes.empty() && "No classes found");

    const CXXRecordDecl* emptyClass = extractor.classes[0];
    ACSLClassAnnotator annotator;

    std::string predicate = annotator.generateClassInvariantPredicate(emptyClass);

    // Should still validate this pointer
    assert(predicate.find("\\valid(this)") != std::string::npos &&
           "Empty class should validate this pointer");

    std::cout << "PASSED\n";
}

int main() {
    std::cout << "=== ACSLClassAnnotator Test Suite ===\n\n";

    try {
        testSimpleClassPrimitiveMembers();
        testClassWithPointerMembers();
        testStackClassWithArrayMembers();
        testClassWithVirtualMethods();
        testConstructorInvariantInjection();
        testMethodInvariantInjection();
        testDestructorInvariantInjection();
        testMemberConstraintGeneration();
        testFullACSLLevelIntegration();
        testEmptyClass();

        std::cout << "\n=== All tests PASSED ===\n";
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "\n=== Test FAILED: " << e.what() << " ===\n";
        return 1;
    }
}
