/**
 * @file TypeInfoGeneratorTest.cpp
 * @brief Tests for Story #83: type_info Structure Generation (Itanium ABI)
 *
 * Acceptance Criteria:
 * - Type Info Class Detection: Determine which type_info class to use based on inheritance
 * - __class_type_info Generation: For classes with no bases (vtable_ptr + type_name)
 * - __si_class_type_info Generation: For single inheritance (adds base_type pointer)
 * - __vmi_class_type_info Generation: For multiple/virtual inheritance (adds bases array)
 * - Type Name Encoding: Length-prefixed names per Itanium ABI (e.g., "4Base")
 * - Constant Initialization: Generate const type_info structs
 * - Testing: Validate type_info generated for Base, Derived, Diamond hierarchies
 */

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "../include/TypeInfoGenerator.h"
#include "../include/VirtualMethodAnalyzer.h"
#include <iostream>
#include <cassert>
#include <sstream>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST(const char *code) {
    std::vector<std::string> args = {"-std=c++17"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Test helper macros
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

// Helper function to find class by name
CXXRecordDecl* findClass(TranslationUnitDecl* TU, const std::string& name) {
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == name && RD->isCompleteDefinition()) {
                return RD;
            }
        }
    }
    return nullptr;
}

// Test 1: Generate __class_type_info for base class (no inheritance)
void test_GenerateClassTypeInfo() {
    TEST_START("GenerateClassTypeInfo");

    const char *code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    TypeInfoGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Base = findClass(TU, "Base");
    ASSERT(Base, "Base class not found");

    // Generate type_info constant
    std::string typeInfoCode = generator.generateTypeInfo(Base);

    // Verify __class_type_info structure
    ASSERT(typeInfoCode.find("const struct __class_type_info __ti_Base") != std::string::npos,
           "Expected '__ti_Base' type_info constant");
    ASSERT(typeInfoCode.find(".vtable_ptr = &__vt_class_type_info") != std::string::npos,
           "Expected vtable_ptr initialization");
    ASSERT(typeInfoCode.find(".type_name = \"4Base\"") != std::string::npos,
           "Expected length-prefixed type name '4Base'");

    TEST_PASS("GenerateClassTypeInfo");
}

// Test 2: Generate __si_class_type_info for single inheritance
void test_GenerateSIClassTypeInfo() {
    TEST_START("GenerateSIClassTypeInfo");

    const char *code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
        public:
            virtual ~Derived() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    TypeInfoGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");
    ASSERT(Derived, "Derived class not found");

    // Generate type_info constant
    std::string typeInfoCode = generator.generateTypeInfo(Derived);

    // Verify __si_class_type_info structure
    ASSERT(typeInfoCode.find("const struct __si_class_type_info __ti_Derived") != std::string::npos,
           "Expected '__ti_Derived' type_info constant");
    ASSERT(typeInfoCode.find(".vtable_ptr = &__vt_si_class_type_info") != std::string::npos,
           "Expected __si_class_type_info vtable_ptr");
    ASSERT(typeInfoCode.find(".type_name = \"7Derived\"") != std::string::npos,
           "Expected length-prefixed type name '7Derived'");
    ASSERT(typeInfoCode.find(".base_type = &__ti_Base") != std::string::npos,
           "Expected base_type pointer to __ti_Base");

    TEST_PASS("GenerateSIClassTypeInfo");
}

// Test 3: Generate __vmi_class_type_info for multiple inheritance
void test_GenerateVMIClassTypeInfo() {
    TEST_START("GenerateVMIClassTypeInfo");

    const char *code = R"(
        class Base1 {
        public:
            virtual ~Base1() {}
        };

        class Base2 {
        public:
            virtual ~Base2() {}
        };

        class Diamond : public Base1, public Base2 {
        public:
            virtual ~Diamond() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    TypeInfoGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Diamond = findClass(TU, "Diamond");
    ASSERT(Diamond, "Diamond class not found");

    // Generate type_info constant
    std::string typeInfoCode = generator.generateTypeInfo(Diamond);

    // Verify __vmi_class_type_info structure
    ASSERT(typeInfoCode.find("const struct __vmi_class_type_info __ti_Diamond") != std::string::npos,
           "Expected '__ti_Diamond' type_info constant");
    ASSERT(typeInfoCode.find(".vtable_ptr = &__vt_vmi_class_type_info") != std::string::npos,
           "Expected __vmi_class_type_info vtable_ptr");
    ASSERT(typeInfoCode.find(".type_name = \"7Diamond\"") != std::string::npos,
           "Expected length-prefixed type name '7Diamond'");
    ASSERT(typeInfoCode.find(".base_count = 2") != std::string::npos,
           "Expected base_count = 2");
    ASSERT(typeInfoCode.find("__ti_Base1") != std::string::npos,
           "Expected reference to __ti_Base1");
    ASSERT(typeInfoCode.find("__ti_Base2") != std::string::npos,
           "Expected reference to __ti_Base2");

    TEST_PASS("GenerateVMIClassTypeInfo");
}

// Test 4: Type name encoding (length-prefixed)
void test_TypeNameEncoding() {
    TEST_START("TypeNameEncoding");

    const char *code = R"(
        class VeryLongClassName {
        public:
            virtual ~VeryLongClassName() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    TypeInfoGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *VeryLongClassName = findClass(TU, "VeryLongClassName");
    ASSERT(VeryLongClassName, "VeryLongClassName class not found");

    // Generate type_info constant
    std::string typeInfoCode = generator.generateTypeInfo(VeryLongClassName);

    // "VeryLongClassName" has 17 characters, so should be "17VeryLongClassName"
    ASSERT(typeInfoCode.find(".type_name = \"17VeryLongClassName\"") != std::string::npos,
           "Expected length-prefixed type name '17VeryLongClassName'");

    TEST_PASS("TypeNameEncoding");
}

// Test 5: Detect correct type_info class for hierarchy
void test_DetectTypeInfoClass() {
    TEST_START("DetectTypeInfoClass");

    const char *code = R"(
        class NoBase {
        public:
            virtual ~NoBase() {}
        };

        class SingleBase : public NoBase {
        public:
            virtual ~SingleBase() {}
        };

        class MultiBase : public NoBase, public SingleBase {
        public:
            virtual ~MultiBase() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    TypeInfoGenerator generator(AST->getASTContext());

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    auto *NoBase = findClass(TU, "NoBase");
    ASSERT(NoBase, "NoBase class not found");
    ASSERT(generator.getTypeInfoClass(NoBase) == TypeInfoClass::CLASS_TYPE_INFO,
           "NoBase should use __class_type_info");

    auto *SingleBase = findClass(TU, "SingleBase");
    ASSERT(SingleBase, "SingleBase class not found");
    ASSERT(generator.getTypeInfoClass(SingleBase) == TypeInfoClass::SI_CLASS_TYPE_INFO,
           "SingleBase should use __si_class_type_info");

    auto *MultiBase = findClass(TU, "MultiBase");
    ASSERT(MultiBase, "MultiBase class not found");
    ASSERT(generator.getTypeInfoClass(MultiBase) == TypeInfoClass::VMI_CLASS_TYPE_INFO,
           "MultiBase should use __vmi_class_type_info");

    TEST_PASS("DetectTypeInfoClass");
}

// Test 6: Virtual inheritance should use __vmi_class_type_info
void test_VirtualInheritanceUsesVMI() {
    TEST_START("VirtualInheritanceUsesVMI");

    const char *code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : virtual public Base {
        public:
            virtual ~Derived() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    TypeInfoGenerator generator(AST->getASTContext());

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *Derived = findClass(TU, "Derived");
    ASSERT(Derived, "Derived class not found");

    // Virtual inheritance should use __vmi_class_type_info
    ASSERT(generator.getTypeInfoClass(Derived) == TypeInfoClass::VMI_CLASS_TYPE_INFO,
           "Virtual inheritance should use __vmi_class_type_info");

    std::string typeInfoCode = generator.generateTypeInfo(Derived);
    ASSERT(typeInfoCode.find("__vmi_class_type_info") != std::string::npos,
           "Expected __vmi_class_type_info for virtual inheritance");

    TEST_PASS("VirtualInheritanceUsesVMI");
}

// Test 7: Non-polymorphic class should not generate type_info
void test_NonPolymorphicClassNoTypeInfo() {
    TEST_START("NonPolymorphicClassNoTypeInfo");

    const char *code = R"(
        class NonPolymorphic {
        public:
            ~NonPolymorphic() {}  // Non-virtual destructor
            void foo() {}         // Non-virtual method
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    TypeInfoGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    auto *NonPolymorphic = findClass(TU, "NonPolymorphic");
    ASSERT(NonPolymorphic, "NonPolymorphic class not found");

    // Should not generate type_info for non-polymorphic class
    std::string typeInfoCode = generator.generateTypeInfo(NonPolymorphic);
    ASSERT(typeInfoCode.empty(),
           "Non-polymorphic class should not generate type_info");

    TEST_PASS("NonPolymorphicClassNoTypeInfo");
}

// Test 8: Multi-level inheritance should use correct type_info class
void test_MultiLevelInheritance() {
    TEST_START("MultiLevelInheritance");

    const char *code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived1 : public Base {
        public:
            virtual ~Derived1() {}
        };

        class Derived2 : public Derived1 {
        public:
            virtual ~Derived2() {}
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    VirtualMethodAnalyzer analyzer(AST->getASTContext());
    TypeInfoGenerator generator(AST->getASTContext(), analyzer);

    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    auto *Derived2 = findClass(TU, "Derived2");
    ASSERT(Derived2, "Derived2 class not found");

    // Multi-level single inheritance should still use __si_class_type_info
    ASSERT(generator.getTypeInfoClass(Derived2) == TypeInfoClass::SI_CLASS_TYPE_INFO,
           "Multi-level single inheritance should use __si_class_type_info");

    std::string typeInfoCode = generator.generateTypeInfo(Derived2);
    ASSERT(typeInfoCode.find("__si_class_type_info") != std::string::npos,
           "Expected __si_class_type_info for multi-level single inheritance");
    ASSERT(typeInfoCode.find(".base_type = &__ti_Derived1") != std::string::npos,
           "Expected direct base Derived1");

    TEST_PASS("MultiLevelInheritance");
}

int main() {
    std::cout << "=== TypeInfoGenerator Tests ===" << std::endl;

    test_GenerateClassTypeInfo();
    test_GenerateSIClassTypeInfo();
    test_GenerateVMIClassTypeInfo();
    test_TypeNameEncoding();
    test_DetectTypeInfoClass();
    test_VirtualInheritanceUsesVMI();
    test_NonPolymorphicClassNoTypeInfo();
    test_MultiLevelInheritance();

    std::cout << "\n=== All Tests Passed ===" << std::endl;
    return 0;
}
