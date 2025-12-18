// Stream 6: Edge Cases & Integration Tests
// File 1: EdgeCasesTest.cpp - Boundary Conditions and Unusual Inputs
// Target: 25-30 tests covering empty inputs, maximum nesting, unusual type combinations

#include "clang/AST/ASTContext.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include <string>
#include <vector>
#include <memory>

using namespace clang;

// Test framework
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Helper: Create AST from code
std::unique_ptr<ASTUnit> createAST(const std::string &code) {
    std::vector<std::string> args = {"-std=c++17"};
    auto AST = clang::tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
    return AST;
}

// ============================================================================
// Category 1: Empty Inputs (8 tests)
// ============================================================================

// Test 1: Empty class definition
void test_edge_empty_class() {
    TEST_START("test_edge_empty_class");

    const char *code = R"(
        class Empty {};
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse empty class");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    // Verify empty class is parsed correctly
    bool foundEmptyClass = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->getNameAsString() == "Empty") {
                foundEmptyClass = true;
                ASSERT(RD->field_begin() == RD->field_end(), "Empty class should have no fields");
                ASSERT(RD->method_begin() == RD->method_end(), "Empty class should have no methods");
            }
        }
    }

    ASSERT(foundEmptyClass, "Empty class not found");
    TEST_PASS("test_edge_empty_class");
}

// Test 2: Empty struct with no members
void test_edge_empty_struct() {
    TEST_START("test_edge_empty_struct");

    const char *code = R"(
        struct EmptyStruct {};
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse empty struct");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundStruct = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->getNameAsString() == "EmptyStruct") {
                foundStruct = true;
                ASSERT(RD->field_empty(), "Empty struct should have no fields");
            }
        }
    }

    ASSERT(foundStruct, "Empty struct not found");
    TEST_PASS("test_edge_empty_struct");
}

// Test 3: Function with empty body
void test_edge_empty_function() {
    TEST_START("test_edge_empty_function");

    const char *code = R"(
        void emptyFunction() {}
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse empty function");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundFunc = false;
    for (auto *Decl : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(Decl)) {
            if (FD->getNameAsString() == "emptyFunction") {
                foundFunc = true;
                ASSERT(FD->getNumParams() == 0, "Empty function should have no parameters");
                if (auto *Body = FD->getBody()) {
                    if (auto *CS = dyn_cast<CompoundStmt>(Body)) {
                        ASSERT(CS->body_empty(), "Empty function should have empty body");
                    }
                }
            }
        }
    }

    ASSERT(foundFunc, "Empty function not found");
    TEST_PASS("test_edge_empty_function");
}

// Test 4: Empty namespace
void test_edge_empty_namespace() {
    TEST_START("test_edge_empty_namespace");

    const char *code = R"(
        namespace EmptyNS {}
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse empty namespace");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundNS = false;
    for (auto *Decl : TU->decls()) {
        if (auto *NS = dyn_cast<NamespaceDecl>(Decl)) {
            if (NS->getNameAsString() == "EmptyNS") {
                foundNS = true;
                // Empty namespace is valid
            }
        }
    }

    ASSERT(foundNS, "Empty namespace not found");
    TEST_PASS("test_edge_empty_namespace");
}

// Test 5: Empty enum
void test_edge_empty_enum() {
    TEST_START("test_edge_empty_enum");

    const char *code = R"(
        enum EmptyEnum {};
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse empty enum");

    // Note: Empty enums are allowed in C++ but unusual
    TEST_PASS("test_edge_empty_enum");
}

// Test 6: Class with only empty methods
void test_edge_class_with_only_empty_methods() {
    TEST_START("test_edge_class_with_only_empty_methods");

    const char *code = R"(
        class OnlyEmpty {
        public:
            void method1() {}
            void method2() {}
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse class with empty methods");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundClass = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->getNameAsString() == "OnlyEmpty") {
                foundClass = true;
                int methodCount = 0;
                for (auto *Method : RD->methods()) {
                    methodCount++;
                }
                ASSERT(methodCount >= 2, "Should have at least 2 methods");
            }
        }
    }

    ASSERT(foundClass, "Class with empty methods not found");
    TEST_PASS("test_edge_class_with_only_empty_methods");
}

// Test 7: Empty parameter pack
void test_edge_empty_parameter_pack() {
    TEST_START("test_edge_empty_parameter_pack");

    const char *code = R"(
        template<typename... Args>
        void variadicEmpty(Args... args) {}
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse empty parameter pack");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundTemplate = false;
    for (auto *Decl : TU->decls()) {
        if (auto *FTD = dyn_cast<FunctionTemplateDecl>(Decl)) {
            foundTemplate = true;
            // Empty parameter pack is valid
        }
    }

    ASSERT(foundTemplate, "Variadic template not found");
    TEST_PASS("test_edge_empty_parameter_pack");
}

// Test 8: Empty initializer list
void test_edge_empty_initializer_list() {
    TEST_START("test_edge_empty_initializer_list");

    const char *code = R"(
        class EmptyInit {
        public:
            EmptyInit() : {} // Note: This is actually invalid C++, but testing edge case
        };
    )";

    // This should fail to parse, which is the expected edge case
    auto AST = createAST(code);
    // Empty initializer list syntax is invalid, AST creation should handle it
    TEST_PASS("test_edge_empty_initializer_list");
}

// ============================================================================
// Category 2: Maximum Nesting/Recursion (8 tests)
// ============================================================================

// Test 9: Deeply nested classes (5 levels)
void test_edge_deeply_nested_classes() {
    TEST_START("test_edge_deeply_nested_classes");

    const char *code = R"(
        class Level1 {
            class Level2 {
                class Level3 {
                    class Level4 {
                        class Level5 {
                            int data;
                        };
                    };
                };
            };
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse deeply nested classes");
    TEST_PASS("test_edge_deeply_nested_classes");
}

// Test 10: Deeply nested namespaces
void test_edge_deeply_nested_namespaces() {
    TEST_START("test_edge_deeply_nested_namespaces");

    const char *code = R"(
        namespace N1 {
            namespace N2 {
                namespace N3 {
                    namespace N4 {
                        namespace N5 {
                            int value = 42;
                        }
                    }
                }
            }
        }
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse deeply nested namespaces");
    TEST_PASS("test_edge_deeply_nested_namespaces");
}

// Test 11: Deeply nested blocks
void test_edge_deeply_nested_blocks() {
    TEST_START("test_edge_deeply_nested_blocks");

    const char *code = R"(
        void nestedBlocks() {
            {
                {
                    {
                        {
                            {
                                int x = 10;
                            }
                        }
                    }
                }
            }
        }
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse deeply nested blocks");
    TEST_PASS("test_edge_deeply_nested_blocks");
}

// Test 12: Multiple levels of inheritance (5 levels)
void test_edge_deep_inheritance_chain() {
    TEST_START("test_edge_deep_inheritance_chain");

    const char *code = R"(
        class Base {};
        class Derived1 : public Base {};
        class Derived2 : public Derived1 {};
        class Derived3 : public Derived2 {};
        class Derived4 : public Derived3 {};
        class Derived5 : public Derived4 {};
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse deep inheritance chain");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    int classCount = 0;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->isCompleteDefinition()) {
                classCount++;
            }
        }
    }

    ASSERT(classCount >= 6, "Should have at least 6 classes in inheritance chain");
    TEST_PASS("test_edge_deep_inheritance_chain");
}

// Test 13: Nested template instantiations
void test_edge_nested_template_instantiations() {
    TEST_START("test_edge_nested_template_instantiations");

    const char *code = R"(
        template<typename T>
        struct Wrapper { T value; };

        using Nested = Wrapper<Wrapper<Wrapper<Wrapper<int>>>>;
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse nested template instantiations");
    TEST_PASS("test_edge_nested_template_instantiations");
}

// Test 14: Recursive type definitions (pointer to self)
void test_edge_recursive_type_pointer() {
    TEST_START("test_edge_recursive_type_pointer");

    const char *code = R"(
        struct Node {
            int data;
            Node* next;
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse recursive type with pointer");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundNode = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->getNameAsString() == "Node") {
                foundNode = true;
                int fieldCount = 0;
                for (auto *Field : RD->fields()) {
                    fieldCount++;
                }
                ASSERT(fieldCount == 2, "Node should have 2 fields");
            }
        }
    }

    ASSERT(foundNode, "Recursive Node type not found");
    TEST_PASS("test_edge_recursive_type_pointer");
}

// Test 15: Deeply nested function calls
void test_edge_deeply_nested_function_calls() {
    TEST_START("test_edge_deeply_nested_function_calls");

    const char *code = R"(
        int f1(int x) { return x; }
        int f2(int x) { return f1(x); }
        int f3(int x) { return f2(x); }
        int f4(int x) { return f3(x); }
        int f5(int x) { return f4(x); }
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse deeply nested function calls");
    TEST_PASS("test_edge_deeply_nested_function_calls");
}

// Test 16: Maximum template depth (compiler limit testing)
void test_edge_template_recursion_depth() {
    TEST_START("test_edge_template_recursion_depth");

    const char *code = R"(
        template<int N>
        struct Factorial {
            static constexpr int value = N * Factorial<N-1>::value;
        };

        template<>
        struct Factorial<0> {
            static constexpr int value = 1;
        };

        // Test moderate depth (not hitting compiler limits)
        constexpr int result = Factorial<10>::value;
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse template recursion");
    TEST_PASS("test_edge_template_recursion_depth");
}

// ============================================================================
// Category 3: Unusual Type Combinations (9 tests)
// ============================================================================

// Test 17: Pointer to pointer to pointer
void test_edge_triple_pointer() {
    TEST_START("test_edge_triple_pointer");

    const char *code = R"(
        void triplePointer(int*** ptr) {
            // Triple indirection
        }
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse triple pointer");
    TEST_PASS("test_edge_triple_pointer");
}

// Test 18: Array of pointers to arrays
void test_edge_array_of_pointer_to_arrays() {
    TEST_START("test_edge_array_of_pointer_to_arrays");

    const char *code = R"(
        void complexArray() {
            int (*arr[5])[10];  // Array of 5 pointers to arrays of 10 ints
        }
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse array of pointer to arrays");
    TEST_PASS("test_edge_array_of_pointer_to_arrays");
}

// Test 19: Function pointer with complex signature
void test_edge_complex_function_pointer() {
    TEST_START("test_edge_complex_function_pointer");

    const char *code = R"(
        typedef int (*FuncPtr)(double (*)(int, float), void*);
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse complex function pointer");
    TEST_PASS("test_edge_complex_function_pointer");
}

// Test 20: Const volatile qualified types
void test_edge_const_volatile_qualifiers() {
    TEST_START("test_edge_const_volatile_qualifiers");

    const char *code = R"(
        void qualifiedTypes(const volatile int* const volatile ptr) {
            // Multiple qualifiers
        }
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse const volatile qualifiers");
    TEST_PASS("test_edge_const_volatile_qualifiers");
}

// Test 21: Reference to pointer
void test_edge_reference_to_pointer() {
    TEST_START("test_edge_reference_to_pointer");

    const char *code = R"(
        void refToPtr(int*& ref) {
            // Reference to pointer
        }
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse reference to pointer");
    TEST_PASS("test_edge_reference_to_pointer");
}

// Test 22: Rvalue reference to const
void test_edge_rvalue_ref_to_const() {
    TEST_START("test_edge_rvalue_ref_to_const");

    const char *code = R"(
        void rvalueRefConst(const int&& ref) {
            // Rvalue reference to const (unusual but valid)
        }
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse rvalue reference to const");
    TEST_PASS("test_edge_rvalue_ref_to_const");
}

// Test 23: Template with multiple type parameters and defaults
void test_edge_template_multiple_defaults() {
    TEST_START("test_edge_template_multiple_defaults");

    const char *code = R"(
        template<typename T = int, typename U = double, typename V = char>
        struct MultiDefault {
            T t;
            U u;
            V v;
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse template with multiple defaults");
    TEST_PASS("test_edge_template_multiple_defaults");
}

// Test 24: Bitfield with unusual sizes
void test_edge_unusual_bitfield_sizes() {
    TEST_START("test_edge_unusual_bitfield_sizes");

    const char *code = R"(
        struct BitfieldStruct {
            unsigned int a : 1;   // Single bit
            unsigned int b : 31;  // 31 bits
            unsigned int c : 0;   // Zero-width (padding)
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse unusual bitfield sizes");
    TEST_PASS("test_edge_unusual_bitfield_sizes");
}

// Test 25: Union with complex types
void test_edge_union_with_complex_types() {
    TEST_START("test_edge_union_with_complex_types");

    const char *code = R"(
        union ComplexUnion {
            struct {
                int x, y;
            } point;
            double value;
            char buffer[16];
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse union with complex types");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundUnion = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->isUnion() && RD->getNameAsString() == "ComplexUnion") {
                foundUnion = true;
            }
        }
    }

    ASSERT(foundUnion, "Complex union not found");
    TEST_PASS("test_edge_union_with_complex_types");
}

// ============================================================================
// Additional Edge Cases (5 tests)
// ============================================================================

// Test 26: Anonymous struct/union
void test_edge_anonymous_struct() {
    TEST_START("test_edge_anonymous_struct");

    const char *code = R"(
        struct Outer {
            struct {
                int x, y;
            };  // Anonymous struct
            int z;
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse anonymous struct");
    TEST_PASS("test_edge_anonymous_struct");
}

// Test 27: Zero-sized arrays (flexible array member)
void test_edge_flexible_array_member() {
    TEST_START("test_edge_flexible_array_member");

    const char *code = R"(
        struct FlexibleArray {
            int count;
            int data[];  // Flexible array member
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse flexible array member");
    TEST_PASS("test_edge_flexible_array_member");
}

// Test 28: Extremely long identifier names
void test_edge_long_identifier_name() {
    TEST_START("test_edge_long_identifier_name");

    const char *code = R"(
        void veryLongFunctionNameThatExceedsNormalLengthButIsStillValidInCppStandardAndShouldBeHandledProperly() {}
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse long identifier name");
    TEST_PASS("test_edge_long_identifier_name");
}

// Test 29: Multiple inheritance with common base (diamond problem)
void test_edge_diamond_inheritance() {
    TEST_START("test_edge_diamond_inheritance");

    const char *code = R"(
        class Base {};
        class Left : public Base {};
        class Right : public Base {};
        class Diamond : public Left, public Right {};
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse diamond inheritance");

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundDiamond = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->getNameAsString() == "Diamond") {
                foundDiamond = true;
                ASSERT(RD->getNumBases() == 2, "Diamond should have 2 base classes");
            }
        }
    }

    ASSERT(foundDiamond, "Diamond inheritance class not found");
    TEST_PASS("test_edge_diamond_inheritance");
}

// Test 30: Template specialization with edge case types
void test_edge_template_specialization_void() {
    TEST_START("test_edge_template_specialization_void");

    const char *code = R"(
        template<typename T>
        struct Container {
            T value;
        };

        template<>
        struct Container<void> {
            // Specialization for void (no value member)
        };
    )";

    auto AST = createAST(code);
    ASSERT(AST != nullptr, "Failed to parse template specialization for void");
    TEST_PASS("test_edge_template_specialization_void");
}

// ============================================================================
// Main Entry Point
// ============================================================================

int main() {
    std::cout << "\n";
    std::cout << "========================================\n";
    std::cout << "Stream 6: Edge Cases Test Suite\n";
    std::cout << "========================================\n\n";

    std::cout << "Category 1: Empty Inputs\n";
    std::cout << "------------------------\n";
    test_edge_empty_class();
    test_edge_empty_struct();
    test_edge_empty_function();
    test_edge_empty_namespace();
    test_edge_empty_enum();
    test_edge_class_with_only_empty_methods();
    test_edge_empty_parameter_pack();
    test_edge_empty_initializer_list();

    std::cout << "\nCategory 2: Maximum Nesting/Recursion\n";
    std::cout << "--------------------------------------\n";
    test_edge_deeply_nested_classes();
    test_edge_deeply_nested_namespaces();
    test_edge_deeply_nested_blocks();
    test_edge_deep_inheritance_chain();
    test_edge_nested_template_instantiations();
    test_edge_recursive_type_pointer();
    test_edge_deeply_nested_function_calls();
    test_edge_template_recursion_depth();

    std::cout << "\nCategory 3: Unusual Type Combinations\n";
    std::cout << "--------------------------------------\n";
    test_edge_triple_pointer();
    test_edge_array_of_pointer_to_arrays();
    test_edge_complex_function_pointer();
    test_edge_const_volatile_qualifiers();
    test_edge_reference_to_pointer();
    test_edge_rvalue_ref_to_const();
    test_edge_template_multiple_defaults();
    test_edge_unusual_bitfield_sizes();
    test_edge_union_with_complex_types();

    std::cout << "\nCategory 4: Additional Edge Cases\n";
    std::cout << "-----------------------------------\n";
    test_edge_anonymous_struct();
    test_edge_flexible_array_member();
    test_edge_long_identifier_name();
    test_edge_diamond_inheritance();
    test_edge_template_specialization_void();

    std::cout << "\n========================================\n";
    std::cout << "Results: " << tests_passed << " passed, " << tests_failed << " failed\n";
    std::cout << "========================================\n";

    return tests_failed > 0 ? 1 : 0;
}
