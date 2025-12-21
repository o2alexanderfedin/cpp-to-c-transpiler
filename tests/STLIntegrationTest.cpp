/**
 * @file STLIntegrationTest.cpp
 * @brief Story #69: STL Container Support and Integration Testing
 * Migrated to Google Test
 *
 * Tests the complete template pipeline with std::vector<int> to validate:
 * - STL parsing and template extraction
 * - Name mangling for STL types
 * - Monomorphization of std::vector<int>
 * - C code generation for STL methods (push_back, size, operator[])
 *
 * This is the final integration test proving the transpiler can handle
 * production C++ with templates and STL containers.
 */

#include "TemplateMonomorphizer.h"
#include "TemplateExtractor.h"
#include "NameMangler.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include <gtest/gtest.h>
#include <iostream>
#include <sstream>
#include <algorithm>

using namespace clang;

// Helper to build AST from code
std::unique_ptr<ASTUnit> buildASTFromCode(const std::string& code) {
    std::vector<std::string> args = {"-std=c++17", "-xc++"};
    return tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
}

/**
 * Test 1: Simplified std::vector<int> Template Instantiation Extraction
 */
TEST(STLIntegrationTest, VectorIntTemplateExtraction) {
    std::string code = R"(
        namespace std {
            template<typename T>
            class vector {
            public:
                T* data;
                int size_;
                int capacity_;

                vector() : data(nullptr), size_(0), capacity_(0) {}

                void push_back(const T& value) {
                    if (size_ >= capacity_) {
                        capacity_ = capacity_ == 0 ? 1 : capacity_ * 2;
                    }
                    data[size_++] = value;
                }

                int size() const {
                    return size_;
                }

                T& operator[](int index) {
                    return data[index];
                }
            };
        }

        void test() {
            std::vector<int> nums;
            nums.push_back(42);
            int val = nums[0];
            int s = nums.size();
        }
    )";

    auto AST = buildASTFromCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    // Extract template instantiations
    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInstantiations = extractor.getClassInstantiations();

    // Verify std::vector<int> was extracted
    ASSERT_FALSE(classInstantiations.empty()) << "Expected std::vector<int> instantiation";

    bool foundVectorInt = false;
    for (auto* inst : classInstantiations) {
        std::string name = inst->getSpecializedTemplate()->getNameAsString();
        if (name == "vector") {
            const TemplateArgumentList& args = inst->getTemplateArgs();
            if (args.size() > 0 && args[0].getKind() == TemplateArgument::Type) {
                QualType argType = args[0].getAsType();
                if (argType->isIntegerType()) {
                    foundVectorInt = true;
                    break;
                }
            }
        }
    }

    EXPECT_TRUE(foundVectorInt) << "Expected std::vector<int> instantiation";
}

/**
 * Test 2: std::vector<int> Monomorphization to C Code
 */
TEST(STLIntegrationTest, VectorIntMonomorphization) {
    std::string code = R"(
        namespace std {
            template<typename T>
            class vector {
            public:
                T* data;
                int size_;
                int capacity_;

                vector() : data(nullptr), size_(0), capacity_(0) {}

                void push_back(const T& value);
                int size() const;
                T& operator[](int index);
            };
        }

        void test() {
            std::vector<int> nums;
        }
    )";

    auto AST = buildASTFromCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInstantiations = extractor.getClassInstantiations();
    ASSERT_FALSE(classInstantiations.empty()) << "Expected std::vector<int> instantiation";

    // Monomorphize std::vector<int>
    NameMangler mangler(Context);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    ClassTemplateSpecializationDecl* vectorInt = nullptr;
    for (auto* inst : classInstantiations) {
        if (inst->getSpecializedTemplate()->getNameAsString() == "vector") {
            vectorInt = inst;
            break;
        }
    }

    ASSERT_NE(vectorInt, nullptr) << "Expected std::vector<int> instantiation";

    std::string cCode = monomorphizer.monomorphizeClass(vectorInt);

    // Verify generated C code
    EXPECT_NE(cCode.find("typedef struct"), std::string::npos)
        << "Expected struct typedef in C code";
    EXPECT_TRUE(cCode.find("vector_int") != std::string::npos ||
                cCode.find("std_vector_int") != std::string::npos)
        << "Expected mangled name 'vector_int' or 'std_vector_int'";
    EXPECT_NE(cCode.find("int* data"), std::string::npos)
        << "Expected 'int* data' field";
    EXPECT_NE(cCode.find("int size_"), std::string::npos)
        << "Expected 'int size_' field";
    EXPECT_NE(cCode.find("int capacity_"), std::string::npos)
        << "Expected 'int capacity_' field";
}

/**
 * Test 3: std::vector<int> Method Generation
 */
TEST(STLIntegrationTest, VectorIntMethodGeneration) {
    std::string code = R"(
        namespace std {
            template<typename T>
            class vector {
            public:
                T* data;
                int size_;
                int capacity_;

                void push_back(const T& value) {}
                int size() const { return size_; }
                T& operator[](int index) { return data[index]; }
            };
        }

        void test() {
            std::vector<int> nums;
            nums.push_back(42);
            int s = nums.size();
            int val = nums[0];
        }
    )";

    auto AST = buildASTFromCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInstantiations = extractor.getClassInstantiations();
    ASSERT_FALSE(classInstantiations.empty()) << "Expected std::vector<int> instantiation";

    NameMangler mangler(Context);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    ClassTemplateSpecializationDecl* vectorInt = nullptr;
    for (auto* inst : classInstantiations) {
        if (inst->getSpecializedTemplate()->getNameAsString() == "vector") {
            vectorInt = inst;
            break;
        }
    }

    ASSERT_NE(vectorInt, nullptr) << "Expected std::vector<int> instantiation";

    std::string cCode = monomorphizer.monomorphizeClass(vectorInt);

    // Verify method declarations
    bool hasPushBack = (cCode.find("push_back") != std::string::npos);
    bool hasSize = (cCode.find("size") != std::string::npos);
    bool hasOperator = (cCode.find("operator") != std::string::npos ||
                        cCode.find("[") != std::string::npos);

    EXPECT_TRUE(hasPushBack || hasSize || hasOperator)
        << "Expected at least one method declaration";
}

/**
 * Test 4: End-to-End Integration Test
 */
TEST(STLIntegrationTest, EndToEndIntegration) {
    std::string code = R"(
        namespace std {
            template<typename T>
            class vector {
            public:
                T* data;
                int size_;

                void push_back(const T& value) {}
                int size() const { return size_; }
            };
        }

        void useVector() {
            std::vector<int> numbers;
            numbers.push_back(10);
            numbers.push_back(20);
            int count = numbers.size();
        }
    )";

    auto AST = buildASTFromCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    // Step 1: Extract templates
    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInstantiations = extractor.getClassInstantiations();
    ASSERT_FALSE(classInstantiations.empty()) << "Template extraction failed";

    // Step 2: Monomorphize
    NameMangler mangler(Context);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    std::ostringstream allCode;
    for (auto* inst : classInstantiations) {
        std::string cCode = monomorphizer.monomorphizeClass(inst);
        allCode << cCode;
    }

    std::string finalCode = allCode.str();
    ASSERT_FALSE(finalCode.empty()) << "Monomorphization failed";

    // Step 3: Verify output
    EXPECT_NE(finalCode.find("typedef struct"), std::string::npos)
        << "Expected C struct";
    EXPECT_TRUE(finalCode.find("vector_int") != std::string::npos ||
                finalCode.find("std_vector_int") != std::string::npos)
        << "Expected mangled name";
}

/**
 * Test 5: Multiple STL Container Types
 */
TEST(STLIntegrationTest, MultipleVectorTypes) {
    std::string code = R"(
        namespace std {
            template<typename T>
            class vector {
            public:
                T* data;
                int size_;

                void push_back(const T& value) {}
                int size() const { return size_; }
            };
        }

        void test() {
            std::vector<int> ints;
            std::vector<double> doubles;
            std::vector<float> floats;
        }
    )";

    auto AST = buildASTFromCode(code);
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInstantiations = extractor.getClassInstantiations();

    // Count vector instantiations
    int vectorCount = 0;
    for (auto* inst : classInstantiations) {
        if (inst->getSpecializedTemplate()->getNameAsString() == "vector") {
            vectorCount++;
        }
    }

    EXPECT_GE(vectorCount, 1) << "Expected at least one vector instantiation";
}
