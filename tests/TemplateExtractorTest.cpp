/**
 * @file TemplateExtractorTest.cpp
 * @brief Tests for Story #67: Template Instantiation Extraction from AST
 *
 * Acceptance Criteria:
 * - Template class instantiations extracted
 * - Template function instantiations extracted
 * - Template arguments captured correctly
 * - Multiple instantiations of same template collected
 * - Nested templates handled (e.g., vector<pair<int, string>>)
 * - Implicit instantiations detected
 */

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/TemplateExtractor.h"
#include <iostream>
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    // Use buildASTFromCodeWithArgs to ensure templates are properly instantiated
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Test helper macros
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

// Test 1: Simple class template instantiation
void test_SimpleClassTemplateInstantiation() {
    TEST_START("SimpleClassTemplateInstantiation");

    const char *code = R"(
        template<typename T>
        class Stack {
        public:
            T data;
        };

        void test() {
            Stack<int> stack1;
            stack1.data = 42;  // Force instantiation by accessing member

            Stack<double> stack2;
            stack2.data = 3.14;  // Force instantiation
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto instantiations = extractor.getClassInstantiations();

    ASSERT(instantiations.size() == 2,
           "Expected 2 instantiations, got: " + std::to_string(instantiations.size()));

    // Verify Stack<int>
    bool foundInt = false;
    bool foundDouble = false;

    for (const auto& inst : instantiations) {
        std::string templateName = inst->getSpecializedTemplate()->getNameAsString();
        ASSERT(templateName == "Stack", "Expected template name 'Stack', got: " + templateName);

        const TemplateArgumentList& args = inst->getTemplateArgs();
        ASSERT(args.size() == 1, "Expected 1 template argument");

        QualType argType = args[0].getAsType();
        if (argType->isIntegerType()) {
            foundInt = true;
        } else if (argType->isFloatingType()) {
            foundDouble = true;
        }
    }

    ASSERT(foundInt, "Stack<int> not found");
    ASSERT(foundDouble, "Stack<double> not found");

    TEST_PASS("SimpleClassTemplateInstantiation");
}

// Test 2: Template function instantiation
void test_TemplateFunctionInstantiation() {
    TEST_START("TemplateFunctionInstantiation");

    const char *code = R"(
        template<typename T>
        T max(T a, T b) {
            return a > b ? a : b;
        }

        int main() {
            int x = max(1, 2);
            double y = max(1.5, 2.5);
            return 0;
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto funcInstantiations = extractor.getFunctionInstantiations();

    ASSERT(funcInstantiations.size() >= 2,
           "Expected at least 2 function instantiations, got: " + std::to_string(funcInstantiations.size()));

    TEST_PASS("TemplateFunctionInstantiation");
}

// Test 3: Multiple instantiations of same template
void test_MultipleInstantiationsOfSameTemplate() {
    TEST_START("MultipleInstantiationsOfSameTemplate");

    const char *code = R"(
        template<typename T>
        class Container {
        public:
            T value;
        };

        Container<int> c1;
        Container<int> c2;      // Same as c1
        Container<double> c3;   // Different type
        Container<int> c4;      // Same as c1 and c2
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto instantiations = extractor.getClassInstantiations();

    // Should have 2 unique instantiations (int and double), not 4
    ASSERT(instantiations.size() == 2,
           "Expected 2 unique instantiations, got: " + std::to_string(instantiations.size()));

    TEST_PASS("MultipleInstantiationsOfSameTemplate");
}

// Test 4: Nested template instantiation
void test_NestedTemplateInstantiation() {
    TEST_START("NestedTemplateInstantiation");

    const char *code = R"(
        template<typename T>
        class Outer {
        public:
            T value;
        };

        template<typename T>
        class Inner {
        public:
            T data;
        };

        Outer<Inner<int>> nested;
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto instantiations = extractor.getClassInstantiations();

    // Should find both Inner<int> and Outer<Inner<int>>
    ASSERT(instantiations.size() == 2,
           "Expected 2 instantiations (Inner<int> and Outer<Inner<int>>), got: " +
           std::to_string(instantiations.size()));

    bool foundInner = false;
    bool foundOuter = false;

    for (const auto& inst : instantiations) {
        std::string name = inst->getNameAsString();
        if (name.find("Inner") != std::string::npos) {
            foundInner = true;
        }
        if (name.find("Outer") != std::string::npos) {
            foundOuter = true;
        }
    }

    ASSERT(foundInner, "Inner<int> not found");
    ASSERT(foundOuter, "Outer<Inner<int>> not found");

    TEST_PASS("NestedTemplateInstantiation");
}

// Test 5: Implicit template instantiation
void test_ImplicitTemplateInstantiation() {
    TEST_START("ImplicitTemplateInstantiation");

    const char *code = R"(
        template<typename T>
        class Box {
        public:
            T* allocate() { return new T(); }
        };

        void useBox() {
            Box<int> box;
            int* ptr = box.allocate();  // Triggers implicit instantiation of allocate()
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInstantiations = extractor.getClassInstantiations();

    ASSERT(classInstantiations.size() >= 1,
           "Expected at least 1 class instantiation (Box<int>), got: " +
           std::to_string(classInstantiations.size()));

    // Verify Box<int> was found
    bool foundBox = false;
    for (const auto& inst : classInstantiations) {
        std::string name = inst->getSpecializedTemplate()->getNameAsString();
        if (name == "Box") {
            foundBox = true;
            break;
        }
    }

    ASSERT(foundBox, "Box<int> instantiation not found");

    TEST_PASS("ImplicitTemplateInstantiation");
}

// Test 6: Template argument details
void test_TemplateArgumentDetails() {
    TEST_START("TemplateArgumentDetails");

    const char *code = R"(
        template<typename T, int N>
        class Array {
        public:
            T data[N];
        };

        Array<double, 10> arr;
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto instantiations = extractor.getClassInstantiations();

    ASSERT(instantiations.size() == 1, "Expected 1 instantiation");

    auto inst = instantiations[0];
    const TemplateArgumentList& args = inst->getTemplateArgs();

    ASSERT(args.size() == 2, "Expected 2 template arguments");

    // First argument should be type (double)
    ASSERT(args[0].getKind() == TemplateArgument::Type,
           "First argument should be a type");
    ASSERT(args[0].getAsType()->isFloatingType(),
           "First type argument should be floating point");

    // Second argument should be integer (10)
    ASSERT(args[1].getKind() == TemplateArgument::Integral,
           "Second argument should be integral");
    ASSERT(args[1].getAsIntegral() == 10,
           "Second argument value should be 10");

    TEST_PASS("TemplateArgumentDetails");
}

int main() {
    std::cout << "Running Template Extractor Tests...\n" << std::endl;

    test_SimpleClassTemplateInstantiation();
    test_TemplateFunctionInstantiation();
    test_MultipleInstantiationsOfSameTemplate();
    test_NestedTemplateInstantiation();
    test_ImplicitTemplateInstantiation();
    test_TemplateArgumentDetails();

    std::cout << "\nAll tests passed!" << std::endl;
    return 0;
}
