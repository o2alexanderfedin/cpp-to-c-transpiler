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

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/TemplateExtractor.h"
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    // Use buildASTFromCodeWithArgs to ensure templates are properly instantiated
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Test 1: Simple class template instantiation

// Test fixture
class TemplateExtractorTest : public ::testing::Test {
protected:
};

TEST_F(TemplateExtractorTest, SimpleClassTemplateInstantiation) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        TemplateExtractor extractor(AST->getASTContext());
        extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

        auto instantiations = extractor.getClassInstantiations();

        ASSERT_TRUE(instantiations.size() == 2) << "Expected 2 instantiations, got: " + std::to_string(instantiations.size());

        // Verify Stack<int>
        bool foundInt = false;
        bool foundDouble = false;

        for (const auto& inst : instantiations) {
            std::string templateName = inst->getSpecializedTemplate()->getNameAsString();
            ASSERT_TRUE(templateName == "Stack") << "Expected template name 'Stack', got: " + templateName;

            const TemplateArgumentList& args = inst->getTemplateArgs();
            ASSERT_TRUE(args.size() == 1) << "Expected 1 template argument";

            QualType argType = args[0].getAsType();
            if (argType->isIntegerType()) {
                foundInt = true;
            } else if (argType->isFloatingType()) {
                foundDouble = true;
            }
        }

        ASSERT_TRUE(foundInt) << "Stack<int> not found";
        ASSERT_TRUE(foundDouble) << "Stack<double> not found";
}

TEST_F(TemplateExtractorTest, TemplateFunctionInstantiation) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        TemplateExtractor extractor(AST->getASTContext());
        extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

        auto funcInstantiations = extractor.getFunctionInstantiations();

        ASSERT_TRUE(funcInstantiations.size() >= 2) << "Expected at least 2 function instantiations, got: " + std::to_string(funcInstantiations.size());
}

TEST_F(TemplateExtractorTest, MultipleInstantiationsOfSameTemplate) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        TemplateExtractor extractor(AST->getASTContext());
        extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

        auto instantiations = extractor.getClassInstantiations();

        // Should have 2 unique instantiations (int and double), not 4
        ASSERT_TRUE(instantiations.size() == 2) << "Expected 2 unique instantiations, got: " + std::to_string(instantiations.size());
}

TEST_F(TemplateExtractorTest, NestedTemplateInstantiation) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        TemplateExtractor extractor(AST->getASTContext());
        extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

        auto instantiations = extractor.getClassInstantiations();

        // Should find both Inner<int> and Outer<Inner<int>>
        ASSERT_TRUE(instantiations.size() == 2) << "Expected 2 instantiations (Inner<int> and Outer<Inner<int>>;, got: " +
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

        ASSERT_TRUE(foundInner) << "Inner<int> not found";
        ASSERT_TRUE(foundOuter) << "Outer<Inner<int>> not found";
}

TEST_F(TemplateExtractorTest, ImplicitTemplateInstantiation) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        TemplateExtractor extractor(AST->getASTContext());
        extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

        auto classInstantiations = extractor.getClassInstantiations();

        ASSERT_TRUE(classInstantiations.size() >= 1) << "Expected at least 1 class instantiation (Box<int>;, got: " +
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

        ASSERT_TRUE(foundBox) << "Box<int> instantiation not found";
}

TEST_F(TemplateExtractorTest, TemplateArgumentDetails) {
    const char *code = R"(
            template<typename T, int N>
            class Array {
            public:
                T data[N];
            };

            Array<double, 10> arr;
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        TemplateExtractor extractor(AST->getASTContext());
        extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

        auto instantiations = extractor.getClassInstantiations();

        ASSERT_TRUE(instantiations.size() == 1) << "Expected 1 instantiation";

        auto inst = instantiations[0];
        const TemplateArgumentList& args = inst->getTemplateArgs();

        ASSERT_TRUE(args.size() == 2) << "Expected 2 template arguments";

        // First argument should be type (double)
        ASSERT_TRUE(args[0].getKind() == TemplateArgument::Type) << "First argument should be a type";
        ASSERT_TRUE(args[0].getAsType()->isFloatingType()) << "First type argument should be floating point";

        // Second argument should be integer (10)
        ASSERT_TRUE(args[1].getKind() == TemplateArgument::Integral) << "Second argument should be integral";
        ASSERT_TRUE(args[1].getAsIntegral() == 10) << "Second argument value should be 10";
}
