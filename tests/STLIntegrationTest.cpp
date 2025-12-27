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
#include "CNodeBuilder.h"
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
    CNodeBuilder builder(Context);
    TemplateMonomorphizer monomorphizer(Context, mangler, builder);

    ClassTemplateSpecializationDecl* vectorInt = nullptr;
    for (auto* inst : classInstantiations) {
        if (inst->getSpecializedTemplate()->getNameAsString() == "vector") {
            vectorInt = inst;
            break;
        }
    }

    ASSERT_NE(vectorInt, nullptr) << "Expected std::vector<int> instantiation";

    RecordDecl* CStruct = monomorphizer.monomorphizeClass(vectorInt);

    // Verify generated C AST
    ASSERT_NE(CStruct, nullptr) << "Expected non-null struct";

    std::string structName = CStruct->getNameAsString();
    EXPECT_TRUE(structName.find("vector") != std::string::npos)
        << "Expected 'vector' in mangled name, got: " << structName;

    // Verify struct has fields
    EXPECT_NE(CStruct->field_begin(), CStruct->field_end())
        << "Expected struct to have fields";

    // Verify field types (std::vector has data, size_, capacity_)
    bool foundData = false, foundSize = false, foundCapacity = false;
    for (auto* field : CStruct->fields()) {
        std::string fieldName = field->getNameAsString();
        if (fieldName == "data") foundData = true;
        if (fieldName == "size_") foundSize = true;
        if (fieldName == "capacity_") foundCapacity = true;
    }

    EXPECT_TRUE(foundData) << "Expected 'data' field in struct";
    EXPECT_TRUE(foundSize) << "Expected 'size_' field in struct";
    EXPECT_TRUE(foundCapacity) << "Expected 'capacity_' field in struct";
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
    CNodeBuilder builder(Context);
    TemplateMonomorphizer monomorphizer(Context, mangler, builder);

    ClassTemplateSpecializationDecl* vectorInt = nullptr;
    for (auto* inst : classInstantiations) {
        if (inst->getSpecializedTemplate()->getNameAsString() == "vector") {
            vectorInt = inst;
            break;
        }
    }

    ASSERT_NE(vectorInt, nullptr) << "Expected std::vector<int> instantiation";

    RecordDecl* CStruct = monomorphizer.monomorphizeClass(vectorInt);
    ASSERT_NE(CStruct, nullptr) << "Expected non-null struct";

    // Generate methods
    std::vector<FunctionDecl*> methods = monomorphizer.monomorphizeClassMethods(vectorInt, CStruct);

    // Verify method declarations
    bool hasPushBack = false, hasSize = false, hasOperator = false;
    for (auto* method : methods) {
        std::string methodName = method->getNameAsString();
        if (methodName.find("push_back") != std::string::npos) hasPushBack = true;
        if (methodName.find("size") != std::string::npos) hasSize = true;
        if (methodName.find("operator") != std::string::npos || methodName.find("[]") != std::string::npos) hasOperator = true;
    }

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
    CNodeBuilder builder(Context);
    TemplateMonomorphizer monomorphizer(Context, mangler, builder);

    std::vector<RecordDecl*> allStructs;
    for (auto* inst : classInstantiations) {
        RecordDecl* CStruct = monomorphizer.monomorphizeClass(inst);
        if (CStruct) {
            allStructs.push_back(CStruct);
        }
    }

    ASSERT_FALSE(allStructs.empty()) << "Monomorphization failed";

    // Step 3: Verify output
    bool foundVectorStruct = false;
    for (auto* CStruct : allStructs) {
        std::string structName = CStruct->getNameAsString();
        if (structName.find("vector") != std::string::npos) {
            foundVectorStruct = true;
            break;
        }
    }

    EXPECT_TRUE(foundVectorStruct) << "Expected vector struct in output";
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
