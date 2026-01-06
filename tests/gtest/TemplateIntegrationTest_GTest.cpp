// tests/gtest/TemplateIntegrationTest_GTest.cpp
// Unit tests for Template Integration (Phase 11 v2.4.0)
// Migrated to Google Test framework
//
// Tests integration of TemplateMonomorphizer and TemplateExtractor into CppToCVisitor.
// Validates template class instantiation, function templates, specializations,
// nested templates, deduplication, and complex template hierarchies.

#include "../../include/TemplateExtractor.h"
#include "../../include/TemplateMonomorphizer.h"
#include "../../include/TemplateInstantiationTracker.h"
#include "../../include/NameMangler.h"
#include "../../include/OverloadRegistry.h"
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include <gtest/gtest.h>
#include <memory>
#include <string>

using namespace clang;
using namespace std;

// Helper function to build AST
unique_ptr<ASTUnit> buildAST(const char *code) {
    vector<string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
}

// Helper function to check if string contains substring
bool contains(const string& haystack, const string& needle) {
    return haystack.find(needle) != string::npos;
}

// Test fixture for Template Integration
class TemplateIntegrationTest : public ::testing::Test {
protected:
    void SetUp() override {}
    void TearDown() override {}
};

// ============================================================================
// Test Case 1: Simple Class Template Instantiation
// ============================================================================
TEST_F(TemplateIntegrationTest, SimpleClassTemplateInstantiation) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    EXPECT_GE(classInsts.size(), 2) << "Should find at least 2 class instantiations";

    // Verify Stack<int> and Stack<double> exist
    bool foundStackInt = false;
    bool foundStackDouble = false;

    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    registry.reset();
    NameMangler mangler(AST->getASTContext(), registry);
    TemplateMonomorphizer mono(AST->getASTContext(), mangler);

    for (auto* inst : classInsts) {
        string code = mono.monomorphizeClass(inst);
        if (contains(code, "Stack") && contains(code, "int")) {
            foundStackInt = true;
        }
        if (contains(code, "Stack") && contains(code, "double")) {
            foundStackDouble = true;
        }
    }

    EXPECT_TRUE(foundStackInt) << "Stack<int> instantiation not found";
    EXPECT_TRUE(foundStackDouble) << "Stack<double> instantiation not found";
}

// ============================================================================
// Test Case 2: Template Function with Multiple Instantiations
// ============================================================================
TEST_F(TemplateIntegrationTest, TemplateFunctionMultipleInstantiations) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto funcInsts = extractor.getFunctionInstantiations();
    EXPECT_GE(funcInsts.size(), 2) << "Should find at least 2 function instantiations";
}

// ============================================================================
// Test Case 3: Explicit Template Instantiation
// ============================================================================
TEST_F(TemplateIntegrationTest, ExplicitInstantiation) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    EXPECT_GE(classInsts.size(), 1) << "Should find explicit instantiation";
}

// ============================================================================
// Test Case 4: Implicit Template Instantiation
// ============================================================================
TEST_F(TemplateIntegrationTest, ImplicitInstantiation) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    EXPECT_GE(classInsts.size(), 1) << "Should find implicit instantiation";
}

// ============================================================================
// Test Case 5: Nested Template Instantiation
// ============================================================================
TEST_F(TemplateIntegrationTest, NestedTemplateInstantiation) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    EXPECT_GE(classInsts.size(), 2) << "Should find both Pair and Vector instantiations";

    bool foundPair = false;
    bool foundVector = false;

    for (auto* inst : classInsts) {
        string name = inst->getNameAsString();
        if (contains(name, "Pair")) foundPair = true;
        if (contains(name, "Vector")) foundVector = true;
    }

    EXPECT_TRUE(foundPair) << "Pair<int,double> not found";
    EXPECT_TRUE(foundVector) << "Vector<Pair<int,double>> not found";
}

// ============================================================================
// Test Case 6: Full Template Specialization
// ============================================================================
TEST_F(TemplateIntegrationTest, FullTemplateSpecialization) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    EXPECT_GE(classInsts.size(), 2) << "Should find both primary and specialized instantiations";
}

// ============================================================================
// Test Case 7: Partial Template Specialization
// ============================================================================
TEST_F(TemplateIntegrationTest, PartialTemplateSpecialization) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    EXPECT_GE(classInsts.size(), 2) << "Should find both primary and partial specialization";
}

// ============================================================================
// Test Case 8: Template Function Calling Template Class
// ============================================================================
TEST_F(TemplateIntegrationTest, TemplateFunctionCallingTemplateClass) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    auto funcInsts = extractor.getFunctionInstantiations();

    EXPECT_GE(classInsts.size(), 2) << "Should find Stack<int> and Stack<double>";
    EXPECT_GE(funcInsts.size(), 2) << "Should find useStack<int> and useStack<double>";
}

// ============================================================================
// Test Case 9: Deduplication - Same Template, Same Args
// ============================================================================
TEST_F(TemplateIntegrationTest, DeduplicationSameTemplateSameArgs) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();

    // Count Widget<int> instantiations (should be deduplicated to 1)
    int widgetIntCount = 0;
    for (auto* inst : classInsts) {
        string name = inst->getNameAsString();
        if (contains(name, "Widget")) {
            widgetIntCount++;
        }
    }

    EXPECT_EQ(widgetIntCount, 1) << "Widget<int> should be deduplicated to 1 instance";
}

// ============================================================================
// Test Case 10: TemplateInstantiationTracker Unit Tests
// ============================================================================
TEST_F(TemplateIntegrationTest, TemplateInstantiationTrackerBasics) {
    TemplateInstantiationTracker tracker;

    // Test basic add and check
    EXPECT_TRUE(tracker.addInstantiation("Stack<int>")) << "First add should succeed";
    EXPECT_TRUE(tracker.isTracked("Stack<int>")) << "Should be tracked";
    EXPECT_FALSE(tracker.isTracked("Stack<double>")) << "Should not be tracked";

    // Test duplicate detection
    EXPECT_FALSE(tracker.addInstantiation("Stack<int>")) << "Duplicate add should fail";

    // Test multiple instantiations
    EXPECT_TRUE(tracker.addInstantiation("Stack<double>")) << "Different type should succeed";
    EXPECT_TRUE(tracker.addInstantiation("Vector<int>")) << "Different template should succeed";

    auto all = tracker.getAllTracked();
    EXPECT_EQ(all.size(), 3) << "Should have 3 tracked instantiations";

    // Verify all are tracked
    EXPECT_TRUE(tracker.isTracked("Stack<int>")) << "Stack<int> should be tracked";
    EXPECT_TRUE(tracker.isTracked("Stack<double>")) << "Stack<double> should be tracked";
    EXPECT_TRUE(tracker.isTracked("Vector<int>")) << "Vector<int> should be tracked";

    // Test count
    EXPECT_EQ(tracker.getCount(), 3) << "Count should be 3";

    // Test clear
    tracker.clear();
    EXPECT_EQ(tracker.getCount(), 0) << "Count should be 0 after clear";
    EXPECT_FALSE(tracker.isTracked("Stack<int>")) << "Should not be tracked after clear";
}

// ============================================================================
// Test Case 11: Template Friend Function
// ============================================================================
TEST_F(TemplateIntegrationTest, TemplateFriendFunction) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    EXPECT_GE(classInsts.size(), 1) << "Should find Stack<int>";
}

// ============================================================================
// Test Case 12: Dependent Type Resolution
// ============================================================================
TEST_F(TemplateIntegrationTest, DependentTypeResolution) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    EXPECT_GE(classInsts.size(), 3) << "Should find 3 Container instantiations";

    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    registry.reset();
    NameMangler mangler(AST->getASTContext(), registry);
    TemplateMonomorphizer mono(AST->getASTContext(), mangler);

    for (auto* inst : classInsts) {
        string code = mono.monomorphizeClass(inst);
        // Verify code generation succeeded
        EXPECT_FALSE(code.empty()) << "Generated code should not be empty";
    }
}

// ============================================================================
// Test Case 13: Complex Template Hierarchy
// ============================================================================
TEST_F(TemplateIntegrationTest, ComplexTemplateHierarchy) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    EXPECT_GE(classInsts.size(), 2) << "Should find both Base<int> and Derived<int>";

    bool foundBase = false;
    bool foundDerived = false;

    for (auto* inst : classInsts) {
        string name = inst->getNameAsString();
        if (contains(name, "Base")) foundBase = true;
        if (contains(name, "Derived")) foundDerived = true;
    }

    EXPECT_TRUE(foundBase) << "Base<int> not found";
    EXPECT_TRUE(foundDerived) << "Derived<int> not found";
}

// ============================================================================
// Test Case 14: Non-Type Template Parameters
// ============================================================================
TEST_F(TemplateIntegrationTest, NonTypeTemplateParameters) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    EXPECT_GE(classInsts.size(), 2) << "Should find Array<int,10> and Array<double,20>";

    for (auto* inst : classInsts) {
        auto& args = inst->getTemplateArgs();
        EXPECT_GE(args.size(), 2) << "Should have both type and non-type parameters";
    }
}

// ============================================================================
// Test Case 15: Variadic Template
// ============================================================================
TEST_F(TemplateIntegrationTest, VariadicTemplate) {
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
    ASSERT_NE(AST, nullptr) << "Failed to build AST";

    TemplateExtractor extractor(AST->getASTContext());
    extractor.extractTemplateInstantiations(AST->getASTContext().getTranslationUnitDecl());

    auto classInsts = extractor.getClassInstantiations();
    EXPECT_GE(classInsts.size(), 3) << "Should find 3 Tuple instantiations";
}

// Main function for standalone execution
int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
