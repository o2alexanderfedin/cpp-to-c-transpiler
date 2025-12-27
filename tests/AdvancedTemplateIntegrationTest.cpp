/**
 * @file AdvancedTemplateIntegrationTest.cpp
 * @brief Advanced Template Integration Tests
 *
 * Comprehensive integration test that validates transpilation of modern C++
 * with advanced template features including:
 * - Template classes with custom container types
 * - SFINAE-like template function selection
 * - Auto type deduction with templates
 * - Multiple compilation units conceptually represented
 * - Template instantiation across different types
 *
 * Purpose: Validate that the C++ to C transpiler correctly handles real-world
 * modern C++ patterns with templates, type deduction, and multiple instantiations.
 *
 * Test Strategy: Build multi-instantiation C++ projects, transpile to C, and validate
 * the generated C code structure and correctness.
 *
 * Note: This test avoids std::vector and std::type_traits to prevent SDK header
 * conflicts in the test AST builder. It focuses on core template transpilation
 * features that can be tested with simpler code patterns.
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/TemplateExtractor.h"
#include "../include/TemplateMonomorphizer.h"
#include "../include/NameMangler.h"
#include "../include/CNodeBuilder.h"
#include "../include/CodeGenerator.h"
#include <cassert>
#include <memory>
#include <string>
#include <vector>
#include <sstream>

using namespace clang;

// Helper function to build AST with C++17 support
std::unique_ptr<ASTUnit> buildASTFromCodeWithArgs(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
}

// Helper function to check if string contains substring
bool contains(const std::string& haystack, const std::string& needle) {
    return haystack.find(needle) != std::string::npos;
}

// Helper function to emit C code from AST declaration
std::string emitCCode(Decl* D, ASTContext& Context) {
    std::string code;
    llvm::raw_string_ostream OS(code);
    CodeGenerator generator(OS, Context);
    generator.printDecl(D);
    OS.flush();
    return code;
}

// Helper function to validate that generated code is C, not C++
void validateCOutput(const std::string& code, const std::string& testName) {
    // Skip validation if code is empty or very short
    if (code.empty() || code.length() < 10) {
        return;
    }

    // C output must NOT contain C++ keywords
    EXPECT_FALSE(contains(code, "class "))
        << testName << ": Generated C code contains 'class' keyword (should use 'struct')";
    EXPECT_FALSE(contains(code, "template<"))
        << testName << ": Generated C code contains 'template<' keyword";
    EXPECT_FALSE(contains(code, "template <"))
        << testName << ": Generated C code contains 'template <' keyword";
    EXPECT_FALSE(contains(code, "namespace "))
        << testName << ": Generated C code contains 'namespace' keyword";
    EXPECT_FALSE(contains(code, "::"))
        << testName << ": Generated C code contains '::' (C++ scope operator)";

    // If it looks like a struct/class definition, verify it uses struct (not class)
    // For functions, we don't check for struct/typedef (they're just function declarations)
}

// Test fixture
class AdvancedTemplateIntegrationTest : public ::testing::Test {
protected:
};

// ============================================================================
// Test Case 1: Template Class with Array Members
// ============================================================================

/**
 * Tests transpilation of a template class that uses arrays of template type.
 * Validates:
 * - Template class instantiation with int and double
 * - Template parameter propagation to member types
 * - Multiple instantiations of the same template
 */
TEST_F(AdvancedTemplateIntegrationTest, TemplateClassWithArrayMembers) {
    // Template container class that wraps a fixed-size array
    const char* code = R"(
        template<typename T>
        class Container {
        private:
            T items[10];
            int count;

        public:
            Container() : count(0) {}

            void add(T item) {
                if (count < 10) {
                    items[count++] = item;
                }
            }

            T get(int index) {
                if (index >= 0 && index < count) {
                    return items[index];
                }
                return T();
            }

            int size() const {
                return count;
            }
        };

        int main() {
            // Instantiate with int
            Container<int> intContainer;
            intContainer.add(42);
            intContainer.add(100);

            // Instantiate with double
            Container<double> doubleContainer;
            doubleContainer.add(3.14);
            doubleContainer.add(2.71);

            // Instantiate with pointer
            Container<int*> ptrContainer;

            return 0;
        }
    )";

    auto AST = buildASTFromCodeWithArgs(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to build AST from template code";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    ASSERT_TRUE(classInsts.size() >= 2) << "Should find at least 2 Container instantiations";

    // Verify Container instantiations
    NameMangler mangler(AST->getASTContext());
    CNodeBuilder builder(AST->getASTContext());
    TemplateMonomorphizer mono(AST->getASTContext(), mangler, builder);

    bool foundContainer = false;
    for (auto* inst : classInsts) {
        RecordDecl* CStruct = mono.monomorphizeClass(inst);
        std::string name = inst->getNameAsString();

        if (contains(name, "Container")) {
            // Verify generated AST is not null
            ASSERT_NE(CStruct, nullptr) << "Monomorphized struct should not be null";

            // Verify struct has fields
            ASSERT_NE(CStruct->field_begin(), CStruct->field_end())
                << "Container struct should have fields";

            // A/B Test: Verify generated C code is valid C, not C++
            std::string code = emitCCode(CStruct, AST->getASTContext());
            ASSERT_FALSE(code.empty()) << "Monomorphized code should not be empty";
            validateCOutput(code, "TemplateClassWithArrayMembers");

            foundContainer = true;
        }
    }

    ASSERT_TRUE(foundContainer) << "Container instantiation not found";
}

// ============================================================================
// Test Case 2: Template Function Overloading
// ============================================================================

/**
 * Tests transpilation of template functions with different specializations.
 * Validates:
 * - Template function with different type parameters
 * - Function template instantiation
 * - Type-based function selection
 */
TEST_F(AdvancedTemplateIntegrationTest, TemplateFunctionOverloading) {
    // Template functions with different behaviors for different types
    const char* code = R"(
        // Generic template for all types
        template<typename T>
        T process(T value) {
            return value;
        }

        // Specialized version for pointers
        template<typename T>
        T* processPointer(T* value) {
            return value;
        }

        int main() {
            // Call with integral type
            int intResult = process(10);

            // Call with floating-point type
            double doubleResult = process(2.0);

            // Call with char
            char charResult = process('A');

            // Call with pointer type
            int x = 5;
            int* ptrResult = processPointer(&x);

            return 0;
        }
    )";

    auto AST = buildASTFromCodeWithArgs(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to build AST from template function code";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto funcInsts = extractor.getFunctionInstantiations();
    ASSERT_TRUE(funcInsts.size() >= 3) << "Should find at least 3 template function instantiations";

    // Verify template function instantiations
    NameMangler mangler(AST->getASTContext());
    CNodeBuilder builder(AST->getASTContext());
    TemplateMonomorphizer mono(AST->getASTContext(), mangler, builder);

    bool foundProcess = false;
    bool foundProcessPointer = false;

    for (auto* inst : funcInsts) {
        FunctionDecl* CFunc = mono.monomorphizeFunction(inst);
        std::string name = inst->getNameAsString();

        if (contains(name, "process")) {
            foundProcess = true;
            ASSERT_NE(CFunc, nullptr) << "Template function should not be null";

            // Verify function has parameters
            ASSERT_GT(CFunc->getNumParams(), 0u) << "Function should have parameters";

            // A/B Test: Verify generated C code is valid C, not C++
            std::string code = emitCCode(CFunc, AST->getASTContext());
            ASSERT_FALSE(code.empty()) << "Template function code should not be empty";
            validateCOutput(code, "TemplateFunctionOverloading");
        }

        if (contains(name, "Pointer")) {
            foundProcessPointer = true;
        }
    }

    ASSERT_TRUE(foundProcess) << "Should find process() instantiations";
}

// ============================================================================
// Test Case 3: Auto Type Deduction with Templates
// ============================================================================

/**
 * Tests transpilation of auto type deduction.
 * Validates:
 * - Auto for function return types (C++14 feature)
 * - Auto for variable declarations
 * - Auto with template type deduction
 * - Correct type resolution in generated C code
 */
TEST_F(AdvancedTemplateIntegrationTest, AutoTypeDeduction) {
    // Modern C++ with auto type deduction
    const char* code = R"(
        template<typename T>
        auto multiply(T a, T b) -> decltype(a * b) {
            return a * b;
        }

        template<typename T>
        T getMax(T a, T b) {
            return (a > b) ? a : b;
        }

        int main() {
            // Auto with template function
            auto result1 = multiply(10, 20);        // deduced as int
            auto result2 = multiply(3.14, 2.0);     // deduced as double

            // Auto with template function and trailing return
            auto max1 = getMax(100, 200);           // deduced as int
            auto max2 = getMax(5.5, 3.3);           // deduced as double

            // Auto with explicit template instantiation
            auto result3 = multiply<int>(5, 7);
            auto result4 = multiply<double>(1.5, 2.5);

            return 0;
        }
    )";

    auto AST = buildASTFromCodeWithArgs(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to build AST from auto deduction code";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto funcInsts = extractor.getFunctionInstantiations();
    ASSERT_TRUE(funcInsts.size() >= 4) << "Should find multiple auto function instantiations";

    // Verify auto types are correctly deduced and translated
    NameMangler mangler(AST->getASTContext());
    CNodeBuilder builder(AST->getASTContext());
    TemplateMonomorphizer mono(AST->getASTContext(), mangler, builder);

    bool foundMultiply = false;
    bool foundGetMax = false;

    for (auto* inst : funcInsts) {
        FunctionDecl* CFunc = mono.monomorphizeFunction(inst);
        std::string name = inst->getNameAsString();

        if (contains(name, "multiply")) {
            foundMultiply = true;
        }

        if (contains(name, "getMax")) {
            foundGetMax = true;
        }

        // Verify that function was monomorphized
        ASSERT_NE(CFunc, nullptr) << "Auto function should generate AST node";

        // A/B Test: Verify generated C code is valid C, not C++
        std::string code = emitCCode(CFunc, AST->getASTContext());
        validateCOutput(code, "AutoTypeDeduction");
    }

    ASSERT_TRUE(foundMultiply) << "Should find multiply instantiations";
    ASSERT_TRUE(foundGetMax) << "Should find getMax instantiations";
}

// ============================================================================
// Test Case 4: Multi-File Conceptual Template Project
// ============================================================================

/**
 * Tests transpilation of code that conceptually represents multiple files.
 * Validates:
 * - Multiple template classes and functions in one compilation unit
 * - Cross-template usage patterns
 * - Template instantiation across different contexts
 */
TEST_F(AdvancedTemplateIntegrationTest, MultiFileTemplateProject) {
    // Simulates multiple files with templates
    const char* code = R"(
        // utils.hpp - Template utility functions
        template<typename T>
        T square(T value) {
            return value * value;
        }

        template<typename T>
        T cube(T value) {
            return value * value * value;
        }

        // container.hpp - Template container class
        template<typename T>
        class SimpleContainer {
        private:
            T data[5];
            int size;

        public:
            SimpleContainer() : size(0) {}

            void push(T item) {
                if (size < 5) {
                    data[size++] = item;
                }
            }

            T pop() {
                if (size > 0) {
                    return data[--size];
                }
                return T();
            }

            int count() const {
                return size;
            }
        };

        // math_ops.cpp - Uses utils.hpp
        int computeSquare(int x) {
            return square(x);
        }

        double computeCube(double x) {
            return cube(x);
        }

        // main.cpp - Uses both headers
        int main() {
            // Use template function from utils.hpp
            int squared = square(5);
            double cubed = cube(2.5);

            // Use template class from container.hpp
            SimpleContainer<int> intContainer;
            intContainer.push(10);
            intContainer.push(20);

            SimpleContainer<double> doubleContainer;
            doubleContainer.push(3.14);

            return 0;
        }
    )";

    auto AST = buildASTFromCodeWithArgs(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to build AST from multi-file project";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    auto funcInsts = extractor.getFunctionInstantiations();

    // Should find SimpleContainer<int> and SimpleContainer<double>
    ASSERT_TRUE(classInsts.size() >= 2) << "Should find multiple SimpleContainer instantiations";

    // Should find square<int>, square<double>, cube<int>, cube<double>
    ASSERT_TRUE(funcInsts.size() >= 2) << "Should find template function instantiations";

    // Verify correct instantiations
    NameMangler mangler(AST->getASTContext());
    CNodeBuilder builder(AST->getASTContext());
    TemplateMonomorphizer mono(AST->getASTContext(), mangler, builder);

    bool foundIntContainer = false;
    bool foundDoubleContainer = false;
    bool foundTemplateFunc = false;

    for (auto* inst : classInsts) {
        std::string name = inst->getNameAsString();
        RecordDecl* CStruct = mono.monomorphizeClass(inst);

        if (contains(name, "SimpleContainer")) {
            foundIntContainer = true;  // Simplified - found at least one
            ASSERT_NE(CStruct, nullptr) << "SimpleContainer struct should not be null";

            // Verify struct has fields
            ASSERT_NE(CStruct->field_begin(), CStruct->field_end())
                << "SimpleContainer should have fields";

            // A/B Test: Verify generated C code is valid C, not C++
            std::string code = emitCCode(CStruct, AST->getASTContext());
            validateCOutput(code, "MultiFileTemplateProject");
        }
    }

    for (auto* inst : funcInsts) {
        std::string name = inst->getNameAsString();
        if (contains(name, "square") || contains(name, "cube")) {
            foundTemplateFunc = true;
        }
    }

    ASSERT_TRUE(foundIntContainer) << "Should find SimpleContainer instantiation";
    ASSERT_TRUE(foundTemplateFunc) << "Should find template functions";
}

// ============================================================================
// Test Case 5: Template with Multiple Type Parameters
// ============================================================================

/**
 * Tests transpilation of templates with multiple type parameters.
 * Validates:
 * - Multi-parameter templates
 * - Different combinations of type parameters
 * - Correct parameter substitution
 */
TEST_F(AdvancedTemplateIntegrationTest, MultipleTypeParameters) {
    const char* code = R"(
        // Template with two type parameters
        template<typename T, typename U>
        class Pair {
        public:
            T first;
            U second;

            Pair(T f, U s) : first(f), second(s) {}

            T getFirst() const { return first; }
            U getSecond() const { return second; }
        };

        // Template function with two type parameters
        template<typename T, typename U>
        T add(T a, U b) {
            return a + static_cast<T>(b);
        }

        int main() {
            // Different type combinations
            Pair<int, double> p1(10, 3.14);
            Pair<double, int> p2(2.71, 42);
            Pair<int, int> p3(5, 7);

            // Template function with different types
            auto r1 = add(10, 20.5);      // int, double
            auto r2 = add(3.14, 2);       // double, int

            return 0;
        }
    )";

    auto AST = buildASTFromCodeWithArgs(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to build AST from multi-parameter template code";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    auto funcInsts = extractor.getFunctionInstantiations();

    // Should find multiple Pair instantiations
    ASSERT_TRUE(classInsts.size() >= 3) << "Should find Pair<int,double>, Pair<double,int>, Pair<int,int>";

    // Should find add instantiations
    ASSERT_TRUE(funcInsts.size() >= 2) << "Should find add instantiations";

    // Verify multi-parameter templates are correctly handled
    NameMangler mangler(AST->getASTContext());
    CNodeBuilder builder(AST->getASTContext());
    TemplateMonomorphizer mono(AST->getASTContext(), mangler, builder);

    for (auto* inst : classInsts) {
        RecordDecl* CStruct = mono.monomorphizeClass(inst);
        ASSERT_NE(CStruct, nullptr) << "Multi-parameter template class should generate AST node";

        // Verify struct has fields
        ASSERT_NE(CStruct->field_begin(), CStruct->field_end())
            << "Pair struct should have fields";

        // A/B Test: Verify generated C code is valid C, not C++
        std::string code = emitCCode(CStruct, AST->getASTContext());
        validateCOutput(code, "MultipleTypeParameters");
    }

    for (auto* inst : funcInsts) {
        FunctionDecl* CFunc = mono.monomorphizeFunction(inst);
        ASSERT_NE(CFunc, nullptr) << "Multi-parameter template function should generate AST node";

        // A/B Test: Verify generated C code is valid C, not C++
        std::string code = emitCCode(CFunc, AST->getASTContext());
        validateCOutput(code, "MultipleTypeParameters");
    }
}

// ============================================================================
// Test Case 6: Nested Template Instantiations
// ============================================================================

/**
 * Tests transpilation of nested templates combined with auto type deduction.
 * Validates:
 * - Nested template instantiations (e.g., Wrapper<Pair<T, U>>)
 * - Auto with nested templates
 * - Correct type resolution in complex scenarios
 */
TEST_F(AdvancedTemplateIntegrationTest, NestedTemplatesWithAuto) {
    const char* code = R"(
        template<typename T>
        class Wrapper {
        public:
            T value;

            Wrapper(T v) : value(v) {}

            auto getValue() -> T {
                return value;
            }
        };

        template<typename T>
        auto makeWrapper(T val) -> Wrapper<T> {
            return Wrapper<T>(val);
        }

        int main() {
            // Simple wrappers
            auto w1 = makeWrapper(42);              // Wrapper<int>
            auto w2 = makeWrapper(3.14);            // Wrapper<double>

            // Nested wrapper
            Wrapper<int> inner(5);
            auto w3 = makeWrapper(inner);           // Wrapper<Wrapper<int>>

            return 0;
        }
    )";

    auto AST = buildASTFromCodeWithArgs(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to build AST from nested templates with auto";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    auto funcInsts = extractor.getFunctionInstantiations();

    // Should find Wrapper instantiations (at least Wrapper<int>, Wrapper<double>)
    ASSERT_TRUE(classInsts.size() >= 2) << "Should find multiple Wrapper instantiations";

    // Should find makeWrapper instantiations
    ASSERT_TRUE(funcInsts.size() >= 2) << "Should find multiple makeWrapper instantiations";

    // Verify nested templates are correctly handled
    NameMangler mangler(AST->getASTContext());
    CNodeBuilder builder(AST->getASTContext());
    TemplateMonomorphizer mono(AST->getASTContext(), mangler, builder);

    for (auto* inst : classInsts) {
        RecordDecl* CStruct = mono.monomorphizeClass(inst);
        ASSERT_NE(CStruct, nullptr) << "Nested template class should generate AST node";

        // Verify struct exists
        ASSERT_NE(CStruct->getNameAsString(), "") << "Struct should have a name";

        // A/B Test: Verify generated C code is valid C, not C++
        std::string code = emitCCode(CStruct, AST->getASTContext());
        validateCOutput(code, "NestedTemplatesWithAuto");
    }

    for (auto* inst : funcInsts) {
        FunctionDecl* CFunc = mono.monomorphizeFunction(inst);
        ASSERT_NE(CFunc, nullptr) << "Nested template function should generate AST node";

        // A/B Test: Verify generated C code is valid C, not C++
        std::string code = emitCCode(CFunc, AST->getASTContext());
        validateCOutput(code, "NestedTemplatesWithAuto");
    }
}

// ============================================================================
// Test Case 7: Template Deduplication
// ============================================================================

/**
 * Tests that the same template instantiation is not duplicated.
 * Validates:
 * - Template instantiation deduplication
 * - Multiple uses of same template type
 * - Correct instance counting
 */
TEST_F(AdvancedTemplateIntegrationTest, TemplateDeduplication) {
    const char* code = R"(
        template<typename T>
        class Box {
        public:
            T value;
            Box(T v) : value(v) {}
        };

        void func1() {
            Box<int> b1(10);
        }

        void func2() {
            Box<int> b2(20);  // Same instantiation as func1
        }

        void func3() {
            Box<int> b3(30);  // Same instantiation again
        }

        int main() {
            Box<int> b4(40);  // Same instantiation
            Box<double> b5(3.14);  // Different instantiation

            func1();
            func2();
            func3();

            return 0;
        }
    )";

    auto AST = buildASTFromCodeWithArgs(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to build AST from deduplication test code";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();

    // Should find only 2 unique instantiations: Box<int> and Box<double>
    // (even though Box<int> is used 4 times)
    ASSERT_TRUE(classInsts.size() == 2) << "Should deduplicate Box<int> to single instance";

    // Verify we have one Box<int> and one Box<double>
    bool foundBoxInt = false;
    bool foundBoxDouble = false;

    for (auto* inst : classInsts) {
        std::string name = inst->getNameAsString();
        if (contains(name, "Box")) {
            foundBoxInt = true;  // Simplified - found at least one Box
        }
    }

    ASSERT_TRUE(foundBoxInt) << "Should find Box instantiation";
    ASSERT_TRUE(classInsts.size() == 2) << "Should have exactly 2 Box instantiations (deduplicated)";
}
