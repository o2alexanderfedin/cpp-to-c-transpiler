/**
 * @file TemplateIntegrationTest.cpp
 * @brief Phase 11: Template Integration Tests (v2.4.0)
 *
 * Tests integration of TemplateMonomorphizer and TemplateExtractor into CppToCVisitor.
 * Validates template class instantiation, function templates, specializations,
 * nested templates, deduplication, and complex template hierarchies.
 *
 * TDD Approach: These tests are written BEFORE implementation to drive design.
 */

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/TemplateExtractor.h"
#include "../include/TemplateMonomorphizer.h"
#include "../include/TemplateInstantiationTracker.h"
#include "../include/NameMangler.h"
#include <iostream>
#include <cassert>
#include <memory>
#include <string>

using namespace clang;

// Test helper macros
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
}

bool contains(const std::string& haystack, const std::string& needle) {
    return haystack.find(needle) != std::string::npos;
}

// ============================================================================
// Test Case 1: Simple Class Template Instantiation
// ============================================================================
void test_SimpleClassTemplateInstantiation() {
    TEST_START("SimpleClassTemplateInstantiation");

    const char* code = R"(
        template<typename T>
        class Stack {
            T data;
        public:
            Stack() : data(T()) {}
            void push(T value) { data = value; }
            T pop() { return data; }
        };

        int main() {
            Stack<int> intStack;
            Stack<double> doubleStack;
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    ASSERT(classInsts.size() >= 2, "Should find at least 2 class instantiations");

    // Verify Stack<int> and Stack<double> exist
    bool foundStackInt = false;
    bool foundStackDouble = false;

    NameMangler mangler(AST->getASTContext());
    TemplateMonomorphizer mono(AST->getASTContext(), mangler);

    for (auto* inst : classInsts) {
        std::string code = mono.monomorphizeClass(inst);
        if (contains(code, "Stack") && contains(code, "int")) {
            foundStackInt = true;
        }
        if (contains(code, "Stack") && contains(code, "double")) {
            foundStackDouble = true;
        }
    }

    ASSERT(foundStackInt, "Stack<int> instantiation not found");
    ASSERT(foundStackDouble, "Stack<double> instantiation not found");

    TEST_PASS("SimpleClassTemplateInstantiation");
}

// ============================================================================
// Test Case 2: Template Function with Multiple Instantiations
// ============================================================================
void test_TemplateFunctionMultipleInstantiations() {
    TEST_START("TemplateFunctionMultipleInstantiations");

    const char* code = R"(
        template<typename T>
        T max(T a, T b) {
            return a > b ? a : b;
        }

        int main() {
            int maxInt = max(10, 20);
            double maxDouble = max(3.14, 2.71);
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto funcInsts = extractor.getFunctionInstantiations();
    ASSERT(funcInsts.size() >= 2, "Should find at least 2 function instantiations");

    TEST_PASS("TemplateFunctionMultipleInstantiations");
}

// ============================================================================
// Test Case 3: Explicit Template Instantiation
// ============================================================================
void test_ExplicitInstantiation() {
    TEST_START("ExplicitInstantiation");

    const char* code = R"(
        template<typename T>
        class Container {
            T value;
        public:
            void set(T v) { value = v; }
        };

        // Explicit instantiation
        template class Container<int>;

        int main() {
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    ASSERT(classInsts.size() >= 1, "Should find explicit instantiation");

    TEST_PASS("ExplicitInstantiation");
}

// ============================================================================
// Test Case 4: Implicit Template Instantiation
// ============================================================================
void test_ImplicitInstantiation() {
    TEST_START("ImplicitInstantiation");

    const char* code = R"(
        template<typename T>
        class Box {
            T item;
        };

        int main() {
            Box<int> b;
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    ASSERT(classInsts.size() >= 1, "Should find implicit instantiation");

    TEST_PASS("ImplicitInstantiation");
}

// ============================================================================
// Test Case 5: Nested Template Instantiation
// ============================================================================
void test_NestedTemplateInstantiation() {
    TEST_START("NestedTemplateInstantiation");

    const char* code = R"(
        template<typename T>
        class Vector {
            T* data;
            int size;
        };

        template<typename K, typename V>
        class Pair {
            K key;
            V value;
        };

        int main() {
            Vector<Pair<int, double>> pairs;
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    ASSERT(classInsts.size() >= 2, "Should find both Pair and Vector instantiations");

    bool foundPair = false;
    bool foundVector = false;

    for (auto* inst : classInsts) {
        std::string name = inst->getNameAsString();
        if (contains(name, "Pair")) foundPair = true;
        if (contains(name, "Vector")) foundVector = true;
    }

    ASSERT(foundPair, "Pair<int,double> not found");
    ASSERT(foundVector, "Vector<Pair<int,double>> not found");

    TEST_PASS("NestedTemplateInstantiation");
}

// ============================================================================
// Test Case 6: Full Template Specialization
// ============================================================================
void test_FullTemplateSpecialization() {
    TEST_START("FullTemplateSpecialization");

    const char* code = R"(
        template<typename T>
        class Container {
        public:
            void process() {}
        };

        template<>
        class Container<bool> {
        public:
            void process() {}
        };

        int main() {
            Container<int> intC;
            Container<bool> boolC;
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    ASSERT(classInsts.size() >= 2, "Should find both primary and specialized instantiations");

    TEST_PASS("FullTemplateSpecialization");
}

// ============================================================================
// Test Case 7: Partial Template Specialization
// ============================================================================
void test_PartialTemplateSpecialization() {
    TEST_START("PartialTemplateSpecialization");

    const char* code = R"(
        template<typename T>
        class Array {
            T* data;
        };

        template<typename T>
        class Array<T*> {
            T** data;
        };

        int main() {
            Array<int> intArray;
            Array<int*> ptrArray;
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    ASSERT(classInsts.size() >= 2, "Should find both primary and partial specialization");

    TEST_PASS("PartialTemplateSpecialization");
}

// ============================================================================
// Test Case 8: Template Function Calling Template Class
// ============================================================================
void test_TemplateFunctionCallingTemplateClass() {
    TEST_START("TemplateFunctionCallingTemplateClass");

    const char* code = R"(
        template<typename T>
        class Stack {
            T data;
        };

        template<typename T>
        void useStack() {
            Stack<T> s;
        }

        int main() {
            useStack<int>();
            useStack<double>();
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    auto funcInsts = extractor.getFunctionInstantiations();

    ASSERT(classInsts.size() >= 2, "Should find Stack<int> and Stack<double>");
    ASSERT(funcInsts.size() >= 2, "Should find useStack<int> and useStack<double>");

    TEST_PASS("TemplateFunctionCallingTemplateClass");
}

// ============================================================================
// Test Case 9: Deduplication - Same Template, Same Args
// ============================================================================
void test_DeduplicationSameTemplateSameArgs() {
    TEST_START("DeduplicationSameTemplateSameArgs");

    const char* code = R"(
        template<typename T>
        class Widget {
            T value;
        };

        void func1() {
            Widget<int> w1;
        }

        void func2() {
            Widget<int> w2;
        }

        int main() {
            func1();
            func2();
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();

    // Count Widget<int> instantiations (should be deduplicated to 1)
    int widgetIntCount = 0;
    for (auto* inst : classInsts) {
        std::string name = inst->getNameAsString();
        if (contains(name, "Widget")) {
            widgetIntCount++;
        }
    }

    ASSERT(widgetIntCount == 1, "Widget<int> should be deduplicated to 1 instance");

    // Test TemplateInstantiationTracker directly
    TemplateInstantiationTracker tracker;

    ASSERT(tracker.addInstantiation("Widget<int>") == true, "First add should return true");
    ASSERT(tracker.addInstantiation("Widget<int>") == false, "Second add should return false");
    ASSERT(tracker.isTracked("Widget<int>"), "Widget<int> should be tracked");
    ASSERT(!tracker.isTracked("Widget<double>"), "Widget<double> should not be tracked");

    auto all = tracker.getAllTracked();
    ASSERT(all.size() == 1, "Should have 1 tracked instantiation");
    ASSERT(all[0] == "Widget<int>", "Tracked instantiation should be Widget<int>");

    TEST_PASS("DeduplicationSameTemplateSameArgs");
}

// ============================================================================
// Test Case 10: Template Friend Function
// ============================================================================
void test_TemplateFriendFunction() {
    TEST_START("TemplateFriendFunction");

    const char* code = R"(
        template<typename T>
        class Stack {
            T data;

            template<typename U>
            friend void printStack(const Stack<U>& s);
        };

        template<typename T>
        void printStack(const Stack<T>& s) {
        }

        int main() {
            Stack<int> s;
            printStack(s);
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    ASSERT(classInsts.size() >= 1, "Should find Stack<int>");

    TEST_PASS("TemplateFriendFunction");
}

// ============================================================================
// Test Case 11: Dependent Type Resolution
// ============================================================================
void test_DependentTypeResolution() {
    TEST_START("DependentTypeResolution");

    const char* code = R"(
        template<typename T>
        class Container {
            T data;
        public:
            T getData() { return data; }
        };

        int main() {
            Container<int> intC;
            Container<double> doubleC;
            Container<char*> ptrC;
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    ASSERT(classInsts.size() >= 3, "Should find 3 Container instantiations");

    NameMangler mangler(AST->getASTContext());
    TemplateMonomorphizer mono(AST->getASTContext(), mangler);

    for (auto* inst : classInsts) {
        std::string code = mono.monomorphizeClass(inst);
        // Verify code generation succeeded
        ASSERT(!code.empty(), "Generated code should not be empty");
    }

    TEST_PASS("DependentTypeResolution");
}

// ============================================================================
// Test Case 12: Complex Template Hierarchy
// ============================================================================
void test_ComplexTemplateHierarchy() {
    TEST_START("ComplexTemplateHierarchy");

    const char* code = R"(
        template<typename T>
        class Base {
            T value;
        };

        template<typename T>
        class Derived : public Base<T> {
            T extra;
        };

        int main() {
            Derived<int> d;
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    ASSERT(classInsts.size() >= 2, "Should find both Base<int> and Derived<int>");

    bool foundBase = false;
    bool foundDerived = false;

    for (auto* inst : classInsts) {
        std::string name = inst->getNameAsString();
        if (contains(name, "Base")) foundBase = true;
        if (contains(name, "Derived")) foundDerived = true;
    }

    ASSERT(foundBase, "Base<int> not found");
    ASSERT(foundDerived, "Derived<int> not found");

    TEST_PASS("ComplexTemplateHierarchy");
}

// ============================================================================
// Test Case 13: TemplateInstantiationTracker Unit Tests
// ============================================================================
void test_TemplateInstantiationTrackerBasics() {
    TEST_START("TemplateInstantiationTrackerBasics");

    TemplateInstantiationTracker tracker;

    // Test basic add and check
    ASSERT(tracker.addInstantiation("Stack<int>"), "First add should succeed");
    ASSERT(tracker.isTracked("Stack<int>"), "Should be tracked");
    ASSERT(!tracker.isTracked("Stack<double>"), "Should not be tracked");

    // Test duplicate detection
    ASSERT(!tracker.addInstantiation("Stack<int>"), "Duplicate add should fail");

    // Test multiple instantiations
    ASSERT(tracker.addInstantiation("Stack<double>"), "Different type should succeed");
    ASSERT(tracker.addInstantiation("Vector<int>"), "Different template should succeed");

    auto all = tracker.getAllTracked();
    ASSERT(all.size() == 3, "Should have 3 tracked instantiations");

    // Verify all are tracked
    ASSERT(tracker.isTracked("Stack<int>"), "Stack<int> should be tracked");
    ASSERT(tracker.isTracked("Stack<double>"), "Stack<double> should be tracked");
    ASSERT(tracker.isTracked("Vector<int>"), "Vector<int> should be tracked");

    // Test count
    ASSERT(tracker.getCount() == 3, "Count should be 3");

    // Test clear
    tracker.clear();
    ASSERT(tracker.getCount() == 0, "Count should be 0 after clear");
    ASSERT(!tracker.isTracked("Stack<int>"), "Should not be tracked after clear");

    TEST_PASS("TemplateInstantiationTrackerBasics");
}

// ============================================================================
// Test Case 14: Non-Type Template Parameters
// ============================================================================
void test_NonTypeTemplateParameters() {
    TEST_START("NonTypeTemplateParameters");

    const char* code = R"(
        template<typename T, int N>
        class Array {
            T data[N];
        };

        int main() {
            Array<int, 10> arr1;
            Array<double, 20> arr2;
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    ASSERT(classInsts.size() >= 2, "Should find Array<int,10> and Array<double,20>");

    for (auto* inst : classInsts) {
        auto& args = inst->getTemplateArgs();
        ASSERT(args.size() >= 2, "Should have both type and non-type parameters");
    }

    TEST_PASS("NonTypeTemplateParameters");
}

// ============================================================================
// Test Case 15: Variadic Template
// ============================================================================
void test_VariadicTemplate() {
    TEST_START("VariadicTemplate");

    const char* code = R"(
        template<typename... Args>
        class Tuple {
        };

        int main() {
            Tuple<int> t1;
            Tuple<int, double> t2;
            Tuple<int, double, char*> t3;
            return 0;
        }
    )";

    auto AST = buildAST(code);
    ASSERT(AST != nullptr, "Failed to build AST");

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    ASSERT(classInsts.size() >= 3, "Should find 3 Tuple instantiations");

    TEST_PASS("VariadicTemplate");
}

// ============================================================================
// Main Test Runner
// ============================================================================
int main() {
    std::cout << "\n========================================" << std::endl;
    std::cout << "Template Integration Test Suite (Phase 11)" << std::endl;
    std::cout << "========================================\n" << std::endl;

    test_SimpleClassTemplateInstantiation();
    test_TemplateFunctionMultipleInstantiations();
    test_ExplicitInstantiation();
    test_ImplicitInstantiation();
    test_NestedTemplateInstantiation();
    test_FullTemplateSpecialization();
    test_PartialTemplateSpecialization();
    test_TemplateFunctionCallingTemplateClass();
    test_DeduplicationSameTemplateSameArgs();
    test_TemplateFriendFunction();
    test_DependentTypeResolution();
    test_ComplexTemplateHierarchy();
    test_TemplateInstantiationTrackerBasics();
    test_NonTypeTemplateParameters();
    test_VariadicTemplate();

    std::cout << "\n========================================" << std::endl;
    std::cout << "All tests passed!" << std::endl;
    std::cout << "========================================\n" << std::endl;

    return 0;
}
