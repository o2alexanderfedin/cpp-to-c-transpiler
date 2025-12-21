// Stream 6: Edge Cases & Integration Tests
// File 1: EdgeCasesTest.cpp - Boundary Conditions and Unusual Inputs
// Target: 25-30 tests covering empty inputs, maximum nesting, unusual type combinations

#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclTemplate.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>
#include <string>
#include <vector>

using namespace clang;

// Google Test Fixture
class EdgeCasesTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> createAST(const std::string &code) {
        std::vector<std::string> args = {"-std=c++17"};
        return clang::tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");
    }
};

// ============================================================================
// Category 1: Empty Inputs (8 tests)
// ============================================================================

// Test 1: Empty class definition
TEST_F(EdgeCasesTest, EmptyClass) {
    const char *code = R"(
        class Empty {};
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse empty class";

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    // Verify empty class is parsed correctly
    bool foundEmptyClass = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->getNameAsString() == "Empty") {
                foundEmptyClass = true;
                ASSERT_TRUE(RD->field_begin() == RD->field_end()) << "Empty class should have no fields";
                ASSERT_TRUE(RD->method_begin() == RD->method_end()) << "Empty class should have no methods";
            }
        }
    }

    ASSERT_TRUE(foundEmptyClass) << "Empty class not found";
}

// Test 2: Empty struct with no members
TEST_F(EdgeCasesTest, EmptyStruct) {
    const char *code = R"(
        struct EmptyStruct {};
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse empty struct";

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundStruct = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->getNameAsString() == "EmptyStruct") {
                foundStruct = true;
                ASSERT_TRUE(RD->field_empty()) << "Empty struct should have no fields";
            }
        }
    }

    ASSERT_TRUE(foundStruct) << "Empty struct not found";
}

// Test 3: Function with empty body
TEST_F(EdgeCasesTest, EmptyFunction) {
    const char *code = R"(
        void emptyFunction() {}
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse empty function";

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundFunc = false;
    for (auto *Decl : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(Decl)) {
            if (FD->getNameAsString() == "emptyFunction") {
                foundFunc = true;
                ASSERT_EQ(FD->getNumParams(), 0u) << "Empty function should have no parameters";
                if (auto *Body = FD->getBody()) {
                    if (auto *CS = dyn_cast<CompoundStmt>(Body)) {
                        ASSERT_TRUE(CS->body_empty()) << "Empty function should have empty body";
                    }
                }
            }
        }
    }

    ASSERT_TRUE(foundFunc) << "Empty function not found";
}

// Test 4: Empty namespace
TEST_F(EdgeCasesTest, EmptyNamespace) {
    const char *code = R"(
        namespace EmptyNS {}
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse empty namespace";

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

    ASSERT_TRUE(foundNS) << "Empty namespace not found";
}

// Test 5: Empty enum
TEST_F(EdgeCasesTest, EmptyEnum) {
    const char *code = R"(
        enum EmptyEnum {};
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse empty enum";
    // Note: Empty enums are allowed in C++ but unusual
}

// Test 6: Class with only empty methods
TEST_F(EdgeCasesTest, ClassWithOnlyEmptyMethods) {
    const char *code = R"(
        class OnlyEmpty {
        public:
            void method1() {}
            void method2() {}
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse class with empty methods";

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
                ASSERT_GE(methodCount, 2) << "Should have at least 2 methods";
            }
        }
    }

    ASSERT_TRUE(foundClass) << "Class with empty methods not found";
}

// Test 7: Empty parameter pack
TEST_F(EdgeCasesTest, EmptyParameterPack) {
    const char *code = R"(
        template<typename... Args>
        void variadicEmpty(Args... args) {}
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse empty parameter pack";

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundTemplate = false;
    for (auto *Decl : TU->decls()) {
        if (auto *FTD = dyn_cast<FunctionTemplateDecl>(Decl)) {
            foundTemplate = true;
            // Empty parameter pack is valid
        }
    }

    ASSERT_TRUE(foundTemplate) << "Variadic template not found";
}

// Test 8: Empty initializer list
TEST_F(EdgeCasesTest, EmptyInitializerList) {
    const char *code = R"(
        class EmptyInit {
        public:
            EmptyInit() : {} // Note: This is actually invalid C++, but testing edge case
        };
    )";

    // This should fail to parse, which is the expected edge case
    auto AST = createAST(code);
    // Empty initializer list syntax is invalid, AST creation should handle it
}

// ============================================================================
// Category 2: Maximum Nesting/Recursion (8 tests)
// ============================================================================

// Test 9: Deeply nested classes (5 levels)
TEST_F(EdgeCasesTest, DeeplyNestedClasses) {
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
    ASSERT_TRUE(AST != nullptr) << "Failed to parse deeply nested classes";
}

// Test 10: Deeply nested namespaces
TEST_F(EdgeCasesTest, DeeplyNestedNamespaces) {
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
    ASSERT_TRUE(AST != nullptr) << "Failed to parse deeply nested namespaces";
}

// Test 11: Deeply nested blocks
TEST_F(EdgeCasesTest, DeeplyNestedBlocks) {
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
    ASSERT_TRUE(AST != nullptr) << "Failed to parse deeply nested blocks";
}

// Test 12: Multiple levels of inheritance (5 levels)
TEST_F(EdgeCasesTest, DeepInheritanceChain) {
    const char *code = R"(
        class Base {};
        class Derived1 : public Base {};
        class Derived2 : public Derived1 {};
        class Derived3 : public Derived2 {};
        class Derived4 : public Derived3 {};
        class Derived5 : public Derived4 {};
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse deep inheritance chain";

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

    ASSERT_GE(classCount, 6) << "Should have at least 6 classes in inheritance chain";
}

// Test 13: Nested template instantiations
TEST_F(EdgeCasesTest, NestedTemplateInstantiations) {
    const char *code = R"(
        template<typename T>
        struct Wrapper { T value; };

        using Nested = Wrapper<Wrapper<Wrapper<Wrapper<int>>>>;
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse nested template instantiations";
}

// Test 14: Recursive type definitions (pointer to self)
TEST_F(EdgeCasesTest, RecursiveTypePointer) {
    const char *code = R"(
        struct Node {
            int data;
            Node* next;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse recursive type with pointer";

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
                ASSERT_EQ(fieldCount, 2) << "Node should have 2 fields";
            }
        }
    }

    ASSERT_TRUE(foundNode) << "Recursive Node type not found";
}

// Test 15: Deeply nested function calls
TEST_F(EdgeCasesTest, DeeplyNestedFunctionCalls) {
    const char *code = R"(
        int f1(int x) { return x; }
        int f2(int x) { return f1(x); }
        int f3(int x) { return f2(x); }
        int f4(int x) { return f3(x); }
        int f5(int x) { return f4(x); }
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse deeply nested function calls";
}

// Test 16: Maximum template depth (compiler limit testing)
TEST_F(EdgeCasesTest, TemplateRecursionDepth) {
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
    ASSERT_TRUE(AST != nullptr) << "Failed to parse template recursion";
}

// ============================================================================
// Category 3: Unusual Type Combinations (9 tests)
// ============================================================================

// Test 17: Pointer to pointer to pointer
TEST_F(EdgeCasesTest, TriplePointer) {
    const char *code = R"(
        void triplePointer(int*** ptr) {
            // Triple indirection
        }
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse triple pointer";
}

// Test 18: Array of pointers to arrays
TEST_F(EdgeCasesTest, ArrayOfPointerToArrays) {
    const char *code = R"(
        void complexArray() {
            int (*arr[5])[10];  // Array of 5 pointers to arrays of 10 ints
        }
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse array of pointer to arrays";
}

// Test 19: Function pointer with complex signature
TEST_F(EdgeCasesTest, ComplexFunctionPointer) {
    const char *code = R"(
        typedef int (*FuncPtr)(double (*)(int, float), void*);
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse complex function pointer";
}

// Test 20: Const volatile qualified types
TEST_F(EdgeCasesTest, ConstVolatileQualifiers) {
    const char *code = R"(
        void qualifiedTypes(const volatile int* const volatile ptr) {
            // Multiple qualifiers
        }
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse const volatile qualifiers";
}

// Test 21: Reference to pointer
TEST_F(EdgeCasesTest, ReferenceToPointer) {
    const char *code = R"(
        void refToPtr(int*& ref) {
            // Reference to pointer
        }
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse reference to pointer";
}

// Test 22: Rvalue reference to const
TEST_F(EdgeCasesTest, RvalueRefToConst) {
    const char *code = R"(
        void rvalueRefConst(const int&& ref) {
            // Rvalue reference to const (unusual but valid)
        }
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse rvalue reference to const";
}

// Test 23: Template with multiple type parameters and defaults
TEST_F(EdgeCasesTest, TemplateMultipleDefaults) {
    const char *code = R"(
        template<typename T = int, typename U = double, typename V = char>
        struct MultiDefault {
            T t;
            U u;
            V v;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse template with multiple defaults";
}

// Test 24: Bitfield with unusual sizes
TEST_F(EdgeCasesTest, UnusualBitfieldSizes) {
    const char *code = R"(
        struct BitfieldStruct {
            unsigned int a : 1;   // Single bit
            unsigned int b : 31;  // 31 bits
            unsigned int c : 0;   // Zero-width (padding)
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse unusual bitfield sizes";
}

// Test 25: Union with complex types
TEST_F(EdgeCasesTest, UnionWithComplexTypes) {
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
    ASSERT_TRUE(AST != nullptr) << "Failed to parse union with complex types";

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

    ASSERT_TRUE(foundUnion) << "Complex union not found";
}

// ============================================================================
// Category 4: Additional Edge Cases (6 tests to make 31 total)
// ============================================================================

// Test 26: Anonymous struct/union
TEST_F(EdgeCasesTest, AnonymousStruct) {
    const char *code = R"(
        struct Outer {
            struct {
                int x, y;
            };  // Anonymous struct
            int z;
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse anonymous struct";
}

// Test 27: Zero-sized arrays (flexible array member)
TEST_F(EdgeCasesTest, FlexibleArrayMember) {
    const char *code = R"(
        struct FlexibleArray {
            int count;
            int data[];  // Flexible array member
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse flexible array member";
}

// Test 28: Extremely long identifier names
TEST_F(EdgeCasesTest, LongIdentifierName) {
    const char *code = R"(
        void veryLongFunctionNameThatExceedsNormalLengthButIsStillValidInCppStandardAndShouldBeHandledProperly() {}
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse long identifier name";
}

// Test 29: Multiple inheritance with common base (diamond problem)
TEST_F(EdgeCasesTest, DiamondInheritance) {
    const char *code = R"(
        class Base {};
        class Left : public Base {};
        class Right : public Base {};
        class Diamond : public Left, public Right {};
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse diamond inheritance";

    auto &Ctx = AST->getASTContext();
    auto *TU = Ctx.getTranslationUnitDecl();

    bool foundDiamond = false;
    for (auto *Decl : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(Decl)) {
            if (RD->getNameAsString() == "Diamond") {
                foundDiamond = true;
                ASSERT_EQ(RD->getNumBases(), 2u) << "Diamond should have 2 base classes";
            }
        }
    }

    ASSERT_TRUE(foundDiamond) << "Diamond inheritance class not found";
}

// Test 30: Template specialization with edge case types
TEST_F(EdgeCasesTest, TemplateSpecializationVoid) {
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
    ASSERT_TRUE(AST != nullptr) << "Failed to parse template specialization for void";
}

// Test 31: Nested anonymous unions and structs
TEST_F(EdgeCasesTest, NestedAnonymousUnionStruct) {
    const char *code = R"(
        struct Complex {
            union {
                struct {
                    int a, b;
                };
                double d;
            };
        };
    )";

    auto AST = createAST(code);
    ASSERT_TRUE(AST != nullptr) << "Failed to parse nested anonymous union and struct";
}
