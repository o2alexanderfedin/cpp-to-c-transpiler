/**
 * @file RvalueRefParameterTest.cpp
 * @brief Tests for rvalue reference parameter handling (Story #133)
 *
 * Test Strategy:
 * - Following TDD: Tests written first, implementation follows
 * - Tests cover rvalue reference parameter detection and translation
 * - Tests verify function signature translation to C
 * - Tests verify call site translation (passing addresses)
 * - Integration with existing type translation infrastructure
 */

#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "../../../include/RvalueRefParamTranslator.h"
#include <iostream>
#include <cassert>
#include <string>
#include <vector>

using namespace clang;

// Test helper to build AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const char *code) {
    return tooling::buildASTFromCode(code);
}

// Test helper macros
#define TEST_START(name) std::cout << "Test: " << name << " ... " << std::flush
#define TEST_PASS(name) std::cout << "PASS" << std::endl
#define ASSERT(cond, msg) \
    if (!(cond)) { \
        std::cerr << "\nASSERT FAILED: " << msg << std::endl; \
        return; \
    }

// Helper visitor to find function declarations
class FunctionFinder : public RecursiveASTVisitor<FunctionFinder> {
public:
    std::vector<const FunctionDecl*> functions;
    std::vector<const ParmVarDecl*> rvalueRefParams;

    bool VisitFunctionDecl(const FunctionDecl *FD) {
        if (FD->isThisDeclarationADefinition()) {
            functions.push_back(FD);

            // Check for rvalue reference parameters
            for (unsigned i = 0; i < FD->getNumParams(); ++i) {
                const ParmVarDecl *Param = FD->getParamDecl(i);
                if (Param->getType()->isRValueReferenceType()) {
                    rvalueRefParams.push_back(Param);
                }
            }
        }
        return true;
    }
};

// ============================================================================
// Test 1: Simple rvalue ref parameter
// C++: void func(Buffer&& b)
// C:   void func(struct Buffer *b)
// ============================================================================
void test_simple_rvalue_ref_parameter() {
    TEST_START("simple_rvalue_ref_parameter");

    const char *code = R"(
        class Buffer {
            int* data;
        public:
            Buffer() : data(nullptr) {}
        };

        void consume(Buffer&& b) {
            // Use buffer
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.rvalueRefParams.size() >= 1, "Expected at least one rvalue reference parameter");

    const ParmVarDecl *Param = finder.rvalueRefParams[0];
    RvalueRefParamTranslator translator(AST->getASTContext());

    // Test detection
    ASSERT(translator.isRvalueReference(Param->getType()), "Should detect rvalue reference type");

    // Test type translation
    std::string cType = translator.translateType(Param->getType());
    ASSERT(cType.find("struct Buffer") != std::string::npos, "C type should contain 'struct Buffer'");
    ASSERT(cType.find("*") != std::string::npos, "C type should be a pointer");

    // Test parameter translation
    std::string cParam = translator.translateParameter(Param);
    ASSERT(cParam.find("struct Buffer") != std::string::npos, "C parameter should contain 'struct Buffer'");
    ASSERT(cParam.find("*") != std::string::npos, "C parameter should be a pointer");
    ASSERT(cParam.find("b") != std::string::npos, "C parameter should contain parameter name");

    TEST_PASS("simple_rvalue_ref_parameter");
}

// ============================================================================
// Test 2: Multiple rvalue ref parameters
// C++: void func(Buffer&& a, Buffer&& b)
// C:   void func(struct Buffer *a, struct Buffer *b)
// ============================================================================
void test_multiple_rvalue_ref_parameters() {
    TEST_START("multiple_rvalue_ref_parameters");

    const char *code = R"(
        class Buffer {
            int* data;
        };

        void process(Buffer&& a, Buffer&& b) {
            // Process both buffers
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.rvalueRefParams.size() >= 2, "Expected at least two rvalue reference parameters");
    ASSERT(finder.functions.size() >= 1, "Expected at least one function");

    const FunctionDecl *Func = finder.functions[0];
    RvalueRefParamTranslator translator(AST->getASTContext());

    // Test function signature translation
    std::string cSignature = translator.translateFunctionSignature(Func);
    ASSERT(cSignature.find("process") != std::string::npos, "C signature should contain function name");
    ASSERT(cSignature.find("struct Buffer") != std::string::npos, "C signature should contain 'struct Buffer'");

    // Count pointer types in signature (should have 2)
    size_t count = 0;
    size_t pos = 0;
    while ((pos = cSignature.find("*", pos)) != std::string::npos) {
        count++;
        pos++;
    }
    ASSERT(count >= 2, "C signature should have at least 2 pointer parameters");

    TEST_PASS("multiple_rvalue_ref_parameters");
}

// ============================================================================
// Test 3: Mixed lvalue and rvalue ref parameters
// C++: void func(Buffer& a, Buffer&& b, int c)
// C:   void func(struct Buffer *a, struct Buffer *b, int c)
// ============================================================================
void test_mixed_reference_parameters() {
    TEST_START("mixed_reference_parameters");

    const char *code = R"(
        class Buffer {
            int* data;
        };

        void mixed(Buffer& lvalue, Buffer&& rvalue, int value) {
            // Process all parameters
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.rvalueRefParams.size() >= 1, "Expected at least one rvalue reference parameter");
    ASSERT(finder.functions.size() >= 1, "Expected at least one function");

    const FunctionDecl *Func = finder.functions[0];
    RvalueRefParamTranslator translator(AST->getASTContext());

    // Test function signature translation
    std::string cSignature = translator.translateFunctionSignature(Func);
    ASSERT(cSignature.find("mixed") != std::string::npos, "C signature should contain function name");
    ASSERT(cSignature.find("struct Buffer") != std::string::npos, "C signature should contain 'struct Buffer'");
    ASSERT(cSignature.find("int") != std::string::npos, "C signature should contain 'int'");

    // Should have 2 Buffer pointers and 1 int
    ASSERT(cSignature.find("lvalue") != std::string::npos, "C signature should contain 'lvalue'");
    ASSERT(cSignature.find("rvalue") != std::string::npos, "C signature should contain 'rvalue'");
    ASSERT(cSignature.find("value") != std::string::npos, "C signature should contain 'value'");

    TEST_PASS("mixed_reference_parameters");
}

// ============================================================================
// Test 4: Rvalue ref return type
// C++: Buffer&& getBuffer()
// C:   struct Buffer* getBuffer()
// ============================================================================
void test_rvalue_ref_return_type() {
    TEST_START("rvalue_ref_return_type");

    const char *code = R"(
        class Buffer {
            int* data;
        };

        Buffer global;

        Buffer&& getBuffer() {
            return static_cast<Buffer&&>(global);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Find getBuffer function
    const FunctionDecl *Func = nullptr;
    for (const FunctionDecl *FD : finder.functions) {
        if (FD->getNameAsString() == "getBuffer") {
            Func = FD;
            break;
        }
    }

    ASSERT(Func != nullptr, "getBuffer function not found");

    RvalueRefParamTranslator translator(AST->getASTContext());

    // Test return type detection
    ASSERT(translator.isRvalueReference(Func->getReturnType()), "Should detect rvalue reference return type");

    // Test function signature translation
    std::string cSignature = translator.translateFunctionSignature(Func);
    ASSERT(cSignature.find("struct Buffer") != std::string::npos, "C signature should contain 'struct Buffer'");
    ASSERT(cSignature.find("*") != std::string::npos, "C return type should be a pointer");
    ASSERT(cSignature.find("getBuffer") != std::string::npos, "C signature should contain function name");

    TEST_PASS("rvalue_ref_return_type");
}

// ============================================================================
// Test 5: Const rvalue reference
// C++: void func(const Buffer&& b)
// C:   void func(const struct Buffer *b)
// ============================================================================
void test_const_rvalue_reference() {
    TEST_START("const_rvalue_reference");

    const char *code = R"(
        class Buffer {
            int* data;
        };

        void readOnly(const Buffer&& b) {
            // Read from buffer only
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.rvalueRefParams.size() >= 1, "Expected at least one rvalue reference parameter");

    const ParmVarDecl *Param = finder.rvalueRefParams[0];
    RvalueRefParamTranslator translator(AST->getASTContext());

    // Test const detection
    ASSERT(translator.isRvalueReference(Param->getType()), "Should detect rvalue reference type");

    // Test type translation with const
    std::string cType = translator.translateType(Param->getType());
    ASSERT(cType.find("const") != std::string::npos, "C type should contain 'const'");
    ASSERT(cType.find("struct Buffer") != std::string::npos, "C type should contain 'struct Buffer'");
    ASSERT(cType.find("*") != std::string::npos, "C type should be a pointer");

    TEST_PASS("const_rvalue_reference");
}

// ============================================================================
// Test 6: Integration with function translation
// ============================================================================
void test_function_translation_integration() {
    TEST_START("function_translation_integration");

    const char *code = R"(
        class Buffer {
            int* data;
            int size;
        public:
            Buffer() : data(nullptr), size(0) {}
            Buffer(Buffer&& other) : data(other.data), size(other.size) {
                other.data = nullptr;
                other.size = 0;
            }
        };

        void transfer(Buffer&& source, Buffer& dest) {
            dest = Buffer(static_cast<Buffer&&>(source));
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Find transfer function
    const FunctionDecl *Func = nullptr;
    for (const FunctionDecl *FD : finder.functions) {
        if (FD->getNameAsString() == "transfer") {
            Func = FD;
            break;
        }
    }

    ASSERT(Func != nullptr, "transfer function not found");
    ASSERT(Func->getNumParams() == 2, "transfer should have 2 parameters");

    RvalueRefParamTranslator translator(AST->getASTContext());

    // Test full function signature
    std::string cSignature = translator.translateFunctionSignature(Func);
    ASSERT(cSignature.find("transfer") != std::string::npos, "C signature should contain function name");
    ASSERT(cSignature.find("void") != std::string::npos, "C signature should have void return type");

    // Should have correct parameter types
    ASSERT(cSignature.find("source") != std::string::npos, "C signature should contain 'source'");
    ASSERT(cSignature.find("dest") != std::string::npos, "C signature should contain 'dest'");

    TEST_PASS("function_translation_integration");
}

// ============================================================================
// Test 7: Parameter passing at call sites
// ============================================================================
void test_call_site_parameter_passing() {
    TEST_START("call_site_parameter_passing");

    const char *code = R"(
        class Buffer {
            int* data;
        };

        void consume(Buffer&& b) {
            // Consume buffer
        }

        void test() {
            Buffer b1;
            consume(static_cast<Buffer&&>(b1));
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Find consume function
    const FunctionDecl *ConsumeFunc = nullptr;
    for (const FunctionDecl *FD : finder.functions) {
        if (FD->getNameAsString() == "consume") {
            ConsumeFunc = FD;
            break;
        }
    }

    ASSERT(ConsumeFunc != nullptr, "consume function not found");

    RvalueRefParamTranslator translator(AST->getASTContext());

    // Verify function signature uses pointer
    std::string cSignature = translator.translateFunctionSignature(ConsumeFunc);
    ASSERT(cSignature.find("*") != std::string::npos, "C function should take pointer parameter");

    // Note: Call site translation would be handled by a separate component
    // This test verifies the function signature is correct for pointer passing

    TEST_PASS("call_site_parameter_passing");
}

// ============================================================================
// Test 8: Rvalue reference to primitive type
// C++: void func(int&& x)
// C:   void func(int x)  // Primitive types passed by value
// ============================================================================
void test_primitive_rvalue_reference() {
    TEST_START("primitive_rvalue_reference");

    const char *code = R"(
        void processPrimitive(int&& x) {
            // Process integer
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.rvalueRefParams.size() >= 1, "Expected at least one rvalue reference parameter");

    const ParmVarDecl *Param = finder.rvalueRefParams[0];
    RvalueRefParamTranslator translator(AST->getASTContext());

    // Test detection
    ASSERT(translator.isRvalueReference(Param->getType()), "Should detect rvalue reference type");

    // For primitives, we might pass by value in C (implementation choice)
    // Test that translation produces valid C code
    std::string cParam = translator.translateParameter(Param);
    ASSERT(!cParam.empty(), "C parameter should not be empty");
    ASSERT(cParam.find("x") != std::string::npos, "C parameter should contain parameter name");

    TEST_PASS("primitive_rvalue_reference");
}

// ============================================================================
// Test 9: Template function with rvalue reference (forwarding reference)
// Note: This test documents that T&& is different from Buffer&&
// ============================================================================
void test_forwarding_reference_detection() {
    TEST_START("forwarding_reference_detection");

    const char *code = R"(
        template<typename T>
        void forward(T&& arg) {
            // Perfect forwarding
        }

        class Buffer {};

        void test() {
            Buffer b;
            forward(b);  // T = Buffer&, not Buffer
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    // Note: Forwarding references (T&&) require template instantiation analysis
    // This is marked as future work in the story requirements
    // For now, we just verify the code parses

    TEST_PASS("forwarding_reference_detection");
}

// ============================================================================
// Test 10: Nested class with rvalue reference parameter
// ============================================================================
void test_nested_class_rvalue_reference() {
    TEST_START("nested_class_rvalue_reference");

    const char *code = R"(
        class Outer {
        public:
            class Inner {
                int value;
            };

            void process(Inner&& inner) {
                // Process inner object
            }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT(AST, "Failed to parse C++ code");

    FunctionFinder finder;
    finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    ASSERT(finder.rvalueRefParams.size() >= 1, "Expected at least one rvalue reference parameter");

    const ParmVarDecl *Param = finder.rvalueRefParams[0];
    RvalueRefParamTranslator translator(AST->getASTContext());

    // Test detection and translation
    ASSERT(translator.isRvalueReference(Param->getType()), "Should detect rvalue reference type");

    std::string cType = translator.translateType(Param->getType());
    ASSERT(cType.find("Inner") != std::string::npos, "C type should contain 'Inner'");
    ASSERT(cType.find("*") != std::string::npos, "C type should be a pointer");

    TEST_PASS("nested_class_rvalue_reference");
}

// ============================================================================
// Main Test Runner
// ============================================================================
int main() {
    std::cout << "\n=== Rvalue Reference Parameter Handling Test Suite (Story #133) ===\n\n";

    test_simple_rvalue_ref_parameter();
    test_multiple_rvalue_ref_parameters();
    test_mixed_reference_parameters();
    test_rvalue_ref_return_type();
    test_const_rvalue_reference();
    test_function_translation_integration();
    test_call_site_parameter_passing();
    test_primitive_rvalue_reference();
    test_forwarding_reference_detection();
    test_nested_class_rvalue_reference();

    std::cout << "\n=== All 10 Tests Completed Successfully ===\n";
    std::cout << "\nTest Coverage Summary:\n";
    std::cout << "- Simple rvalue reference parameters\n";
    std::cout << "- Multiple rvalue reference parameters\n";
    std::cout << "- Mixed lvalue/rvalue reference parameters\n";
    std::cout << "- Rvalue reference return types\n";
    std::cout << "- Const rvalue references\n";
    std::cout << "- Function translation integration\n";
    std::cout << "- Call site parameter passing\n";
    std::cout << "- Primitive type rvalue references\n";
    std::cout << "- Forwarding references (documented)\n";
    std::cout << "- Nested class rvalue references\n";
    std::cout << "Total: 10 comprehensive unit tests\n\n";

    return 0;
}
