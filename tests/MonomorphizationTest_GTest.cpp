// tests/MonomorphizationTest_GTest.cpp
// Migrated from MonomorphizationTest.cpp to Google Test framework
// Story #68: Template Monomorphization and Code Generation Tests

#include <gtest/gtest.h>
#include "TemplateMonomorphizer.h"
#include "TemplateExtractor.h"
#include "NameMangler.h"
#include "OverloadRegistry.h"
#include <clang/AST/ASTContext.h>
#include <clang/Frontend/ASTUnit.h>
#include <clang/Tooling/Tooling.h>
#include <memory>
#include <string>
#include <set>

using namespace clang;

// Test fixture for Monomorphization tests
class MonomorphizationTestFixture : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildASTFromCode(const std::string& code) {
        std::vector<std::string> args = {"-std=c++17", "-xc++"};
        return tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
    }
};

// Test 1: Basic class template monomorphization (Stack<int>, Stack<double>)
TEST_F(MonomorphizationTestFixture, BasicClassTemplateMonomorphization) {
    std::string code = R"(
        template<typename T>
        class Stack {
        public:
            T data[10];
            int top;

            void push(T value) {
                data[top++] = value;
            }

            T pop() {
                return data[--top];
            }
        };

        void test() {
            Stack<int> si;
            Stack<double> sd;
        }
    )";

    auto AST = buildASTFromCode(code);
    ASSERT_TRUE(AST) << "Failed to build AST";

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInsts = extractor.getClassInstantiations();
    ASSERT_GE(classInsts.size(), 2u) << "Expected at least 2 class instantiations";

    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    registry.reset();
    NameMangler mangler(Context, registry);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    for (auto* inst : classInsts) {
        std::string cCode = monomorphizer.monomorphizeClass(inst);

        if (inst->getTemplateArgs()[0].getAsType().getAsString() == "int") {
            EXPECT_NE(cCode.find("typedef struct Stack_int"), std::string::npos);
            EXPECT_NE(cCode.find("int data[10]"), std::string::npos);
            EXPECT_NE(cCode.find("void Stack_int_push"), std::string::npos);
            EXPECT_NE(cCode.find("int Stack_int_pop"), std::string::npos);
        }

        if (inst->getTemplateArgs()[0].getAsType().getAsString() == "double") {
            EXPECT_NE(cCode.find("typedef struct Stack_double"), std::string::npos);
            EXPECT_NE(cCode.find("double data[10]"), std::string::npos);
            EXPECT_NE(cCode.find("void Stack_double_push"), std::string::npos);
            EXPECT_NE(cCode.find("double Stack_double_pop"), std::string::npos);
        }
    }
}

// Test 2: Function template monomorphization
TEST_F(MonomorphizationTestFixture, FunctionTemplateMonomorphization) {
    std::string code = R"(
        template<typename T>
        T max(T a, T b) {
            return (a > b) ? a : b;
        }

        void test() {
            int i = max(10, 20);
            double d = max(3.14, 2.71);
        }
    )";

    auto AST = buildASTFromCode(code);
    ASSERT_TRUE(AST) << "Failed to build AST";

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto funcInsts = extractor.getFunctionInstantiations();
    ASSERT_GE(funcInsts.size(), 2u) << "Expected at least 2 function instantiations";

    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    registry.reset();
    NameMangler mangler(Context, registry);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    for (auto* inst : funcInsts) {
        std::string cCode = monomorphizer.monomorphizeFunction(inst);

        if (inst->getParamDecl(0)->getType().getAsString() == "int") {
            EXPECT_NE(cCode.find("int max_int"), std::string::npos);
            EXPECT_NE(cCode.find("int a, int b"), std::string::npos);
        }

        if (inst->getParamDecl(0)->getType().getAsString() == "double") {
            EXPECT_NE(cCode.find("double max_double"), std::string::npos);
            EXPECT_NE(cCode.find("double a, double b"), std::string::npos);
        }
    }
}

// Test 3: Type substitution in complex types
TEST_F(MonomorphizationTestFixture, TypeSubstitution) {
    std::string code = R"(
        template<typename T>
        class Container {
        public:
            T* ptr;
            T** ptrptr;
            const T constValue;
            T& ref;
        };

        void test() {
            Container<int> c;
        }
    )";

    auto AST = buildASTFromCode(code);
    ASSERT_TRUE(AST) << "Failed to build AST";

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInsts = extractor.getClassInstantiations();
    ASSERT_GE(classInsts.size(), 1u) << "Expected at least 1 class instantiation";

    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    registry.reset();
    NameMangler mangler(Context, registry);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    std::string cCode = monomorphizer.monomorphizeClass(classInsts[0]);

    EXPECT_NE(cCode.find("int* ptr"), std::string::npos);
    EXPECT_NE(cCode.find("int** ptrptr"), std::string::npos);
    EXPECT_NE(cCode.find("const int constValue"), std::string::npos);
    EXPECT_NE(cCode.find("int* ref"), std::string::npos) << "C pointer for reference";
}

// Test 4: Deduplication (same instantiation used multiple times)
TEST_F(MonomorphizationTestFixture, Deduplication) {
    std::string code = R"(
        template<typename T>
        class Box {
        public:
            T value;
        };

        void test1() {
            Box<int> b1;
        }

        void test2() {
            Box<int> b2;
        }
    )";

    auto AST = buildASTFromCode(code);
    ASSERT_TRUE(AST) << "Failed to build AST";

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInsts = extractor.getClassInstantiations();

    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    registry.reset();
    NameMangler mangler(Context, registry);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    std::set<std::string> generatedCode;
    for (auto* inst : classInsts) {
        std::string cCode = monomorphizer.monomorphizeClass(inst);
        generatedCode.insert(cCode);
    }

    EXPECT_EQ(generatedCode.size(), classInsts.size())
        << "Deduplication should happen at extractor level";
}

// Test 5: Method generation with 'this' pointer
TEST_F(MonomorphizationTestFixture, MethodGeneration) {
    std::string code = R"(
        template<typename T>
        class Calculator {
        public:
            T value;

            T add(T x) {
                return value + x;
            }

            void set(T x) {
                value = x;
            }
        };

        void test() {
            Calculator<int> calc;
        }
    )";

    auto AST = buildASTFromCode(code);
    ASSERT_TRUE(AST) << "Failed to build AST";

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInsts = extractor.getClassInstantiations();
    ASSERT_GE(classInsts.size(), 1u) << "Expected at least 1 class instantiation";

    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    registry.reset();
    NameMangler mangler(Context, registry);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    std::string cCode = monomorphizer.monomorphizeClass(classInsts[0]);

    EXPECT_NE(cCode.find("int Calculator_int_add(Calculator_int* this, int x)"), std::string::npos)
        << "Expected 'this' pointer in method signature";
    EXPECT_NE(cCode.find("void Calculator_int_set(Calculator_int* this, int x)"), std::string::npos)
        << "Expected 'this' pointer in void method";
}

// Test 6: Non-type template parameters
TEST_F(MonomorphizationTestFixture, NonTypeTemplateParameters) {
    std::string code = R"(
        template<typename T, int Size>
        class Array {
        public:
            T data[Size];

            int getSize() {
                return Size;
            }
        };

        void test() {
            Array<int, 10> arr1;
            Array<double, 20> arr2;
        }
    )";

    auto AST = buildASTFromCode(code);
    ASSERT_TRUE(AST) << "Failed to build AST";

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInsts = extractor.getClassInstantiations();
    ASSERT_GE(classInsts.size(), 2u) << "Expected at least 2 class instantiations";

    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    registry.reset();
    NameMangler mangler(Context, registry);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    for (auto* inst : classInsts) {
        std::string cCode = monomorphizer.monomorphizeClass(inst);

        if (inst->getTemplateArgs()[0].getAsType().getAsString() == "int") {
            EXPECT_NE(cCode.find("typedef struct Array_int_10"), std::string::npos);
            EXPECT_NE(cCode.find("int data[10]"), std::string::npos);
        }

        if (inst->getTemplateArgs()[0].getAsType().getAsString() == "double") {
            EXPECT_NE(cCode.find("typedef struct Array_double_20"), std::string::npos);
            EXPECT_NE(cCode.find("double data[20]"), std::string::npos);
        }
    }
}
