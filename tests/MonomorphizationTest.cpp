/**
 * @file MonomorphizationTest.cpp
 * @brief Story #68: Template Monomorphization and Code Generation Tests
 *
 * Tests the template monomorphization engine that converts C++ templates
 * into separate C code for each instantiation.
 */

#include "TemplateMonomorphizer.h"
#include "TemplateExtractor.h"
#include "NameMangler.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include <iostream>
#include <cassert>
#include <sstream>

using namespace clang;

// Helper to build AST from code
std::unique_ptr<ASTUnit> buildASTFromCode(const std::string& code) {
    std::vector<std::string> args = {"-std=c++17", "-xc++"};
    return tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
}

// Test 1: Basic class template monomorphization (Stack<int>, Stack<double>)
void test_BasicClassTemplateMonomorphization() {
    std::cout << "Test 1: Basic Class Template Monomorphization\n";

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
    assert(AST && "Failed to build AST");

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    // Extract template instantiations
    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInsts = extractor.getClassInstantiations();
    assert(classInsts.size() >= 2 && "Expected at least 2 class instantiations");

    // Monomorphize
    NameMangler mangler(Context);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    for (auto* inst : classInsts) {
        std::string cCode = monomorphizer.monomorphizeClass(inst);

        // Verify Stack<int>
        if (inst->getTemplateArgs()[0].getAsType().getAsString() == "int") {
            assert(cCode.find("typedef struct Stack_int") != std::string::npos &&
                   "Expected typedef struct Stack_int");
            assert(cCode.find("int data[10]") != std::string::npos &&
                   "Expected int data field");
            assert(cCode.find("void Stack_int_push") != std::string::npos &&
                   "Expected Stack_int_push method");
            assert(cCode.find("int Stack_int_pop") != std::string::npos &&
                   "Expected Stack_int_pop method");
        }

        // Verify Stack<double>
        if (inst->getTemplateArgs()[0].getAsType().getAsString() == "double") {
            assert(cCode.find("typedef struct Stack_double") != std::string::npos &&
                   "Expected typedef struct Stack_double");
            assert(cCode.find("double data[10]") != std::string::npos &&
                   "Expected double data field");
            assert(cCode.find("void Stack_double_push") != std::string::npos &&
                   "Expected Stack_double_push method");
            assert(cCode.find("double Stack_double_pop") != std::string::npos &&
                   "Expected Stack_double_pop method");
        }
    }

    std::cout << "  ✓ Basic class template monomorphization working\n";
}

// Test 2: Function template monomorphization
void test_FunctionTemplateMonomorphization() {
    std::cout << "Test 2: Function Template Monomorphization\n";

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
    assert(AST && "Failed to build AST");

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    // Extract template instantiations
    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto funcInsts = extractor.getFunctionInstantiations();
    assert(funcInsts.size() >= 2 && "Expected at least 2 function instantiations");

    // Monomorphize
    NameMangler mangler(Context);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    for (auto* inst : funcInsts) {
        std::string cCode = monomorphizer.monomorphizeFunction(inst);

        // Verify max<int>
        if (inst->getParamDecl(0)->getType().getAsString() == "int") {
            assert(cCode.find("int max_int") != std::string::npos &&
                   "Expected int max_int function");
            assert(cCode.find("int a, int b") != std::string::npos &&
                   "Expected int parameters");
        }

        // Verify max<double>
        if (inst->getParamDecl(0)->getType().getAsString() == "double") {
            assert(cCode.find("double max_double") != std::string::npos &&
                   "Expected double max_double function");
            assert(cCode.find("double a, double b") != std::string::npos &&
                   "Expected double parameters");
        }
    }

    std::cout << "  ✓ Function template monomorphization working\n";
}

// Test 3: Type substitution in complex types
void test_TypeSubstitution() {
    std::cout << "Test 3: Type Substitution\n";

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
    assert(AST && "Failed to build AST");

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    // Extract template instantiations
    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInsts = extractor.getClassInstantiations();
    assert(classInsts.size() >= 1 && "Expected at least 1 class instantiation");

    // Monomorphize
    NameMangler mangler(Context);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    std::string cCode = monomorphizer.monomorphizeClass(classInsts[0]);

    // Verify type substitution
    assert(cCode.find("int* ptr") != std::string::npos &&
           "Expected int* ptr");
    assert(cCode.find("int** ptrptr") != std::string::npos &&
           "Expected int** ptrptr");
    assert(cCode.find("const int constValue") != std::string::npos &&
           "Expected const int constValue");
    assert(cCode.find("int* ref") != std::string::npos &&
           "Expected int* ref (C pointer for reference)");

    std::cout << "  ✓ Type substitution working\n";
}

// Test 4: Deduplication (same instantiation used multiple times)
void test_Deduplication() {
    std::cout << "Test 4: Deduplication\n";

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
    assert(AST && "Failed to build AST");

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    // Extract template instantiations
    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInsts = extractor.getClassInstantiations();

    // Monomorphize all
    NameMangler mangler(Context);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    std::set<std::string> generatedCode;
    for (auto* inst : classInsts) {
        std::string cCode = monomorphizer.monomorphizeClass(inst);
        generatedCode.insert(cCode);
    }

    // Should have only 1 unique Box<int> code
    assert(generatedCode.size() == classInsts.size() &&
           "Deduplication should happen at extractor level");

    std::cout << "  ✓ Deduplication working\n";
}

// Test 5: Method generation with 'this' pointer
void test_MethodGeneration() {
    std::cout << "Test 5: Method Generation\n";

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
    assert(AST && "Failed to build AST");

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    // Extract template instantiations
    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInsts = extractor.getClassInstantiations();
    assert(classInsts.size() >= 1 && "Expected at least 1 class instantiation");

    // Monomorphize
    NameMangler mangler(Context);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    std::string cCode = monomorphizer.monomorphizeClass(classInsts[0]);

    // Verify 'this' pointer injection
    assert(cCode.find("int Calculator_int_add(Calculator_int* this, int x)") != std::string::npos &&
           "Expected 'this' pointer in method signature");
    assert(cCode.find("void Calculator_int_set(Calculator_int* this, int x)") != std::string::npos &&
           "Expected 'this' pointer in void method");

    std::cout << "  ✓ Method generation with 'this' pointer working\n";
}

// Test 6: Non-type template parameters
void test_NonTypeTemplateParameters() {
    std::cout << "Test 6: Non-Type Template Parameters\n";

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
    assert(AST && "Failed to build AST");

    ASTContext& Context = AST->getASTContext();
    TranslationUnitDecl* TU = Context.getTranslationUnitDecl();

    // Extract template instantiations
    TemplateExtractor extractor(Context);
    extractor.extractTemplateInstantiations(TU);

    auto classInsts = extractor.getClassInstantiations();
    assert(classInsts.size() >= 2 && "Expected at least 2 class instantiations");

    // Monomorphize
    NameMangler mangler(Context);
    TemplateMonomorphizer monomorphizer(Context, mangler);

    for (auto* inst : classInsts) {
        std::string cCode = monomorphizer.monomorphizeClass(inst);

        // Verify Array<int, 10>
        if (inst->getTemplateArgs()[0].getAsType().getAsString() == "int") {
            assert(cCode.find("typedef struct Array_int_10") != std::string::npos &&
                   "Expected Array_int_10 struct");
            assert(cCode.find("int data[10]") != std::string::npos &&
                   "Expected int data[10]");
        }

        // Verify Array<double, 20>
        if (inst->getTemplateArgs()[0].getAsType().getAsString() == "double") {
            assert(cCode.find("typedef struct Array_double_20") != std::string::npos &&
                   "Expected Array_double_20 struct");
            assert(cCode.find("double data[20]") != std::string::npos &&
                   "Expected double data[20]");
        }
    }

    std::cout << "  ✓ Non-type template parameters working\n";
}

int main() {
    std::cout << "Running Story #68 - Template Monomorphization Tests\n";
    std::cout << "====================================================\n\n";

    try {
        test_BasicClassTemplateMonomorphization();
        test_FunctionTemplateMonomorphization();
        test_TypeSubstitution();
        test_Deduplication();
        test_MethodGeneration();
        test_NonTypeTemplateParameters();

        std::cout << "\n====================================================\n";
        std::cout << "Test Results: All 6 tests passed!\n";
        return 0;
    } catch (const std::exception& e) {
        std::cerr << "Test failed with exception: " << e.what() << "\n";
        return 1;
    }
}
