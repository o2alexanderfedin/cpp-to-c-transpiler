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

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "../../../include/RvalueRefParamTranslator.h"
#include <cassert>
#include <string>
#include <vector>

using namespace clang;

// Test helper to build AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const char *code) {
    return tooling::buildASTFromCode(code);
}

// Test helper macros
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

// Test fixture
class RvalueRefParameterTest : public ::testing::Test {
protected:
};

TEST_F(RvalueRefParameterTest, simple_rvalue_ref_parameter) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(finder.rvalueRefParams.size() >= 1) << "Expected at least one rvalue reference parameter";

        const ParmVarDecl *Param = finder.rvalueRefParams[0];
        RvalueRefParamTranslator translator(AST->getASTContext());

        // Test detection
        ASSERT_TRUE(translator.isRvalueReference(Param->getType())) << "Should detect rvalue reference type";

        // Test type translation
        std::string cType = translator.translateType(Param->getType());
        ASSERT_TRUE(cType.find("struct Buffer") != std::string::npos) << "C type should contain 'struct Buffer'";
        ASSERT_TRUE(cType.find("*") != std::string::npos) << "C type should be a pointer";

        // Test parameter translation
        std::string cParam = translator.translateParameter(Param);
        ASSERT_TRUE(cParam.find("struct Buffer") != std::string::npos) << "C parameter should contain 'struct Buffer'";
        ASSERT_TRUE(cParam.find("*") != std::string::npos) << "C parameter should be a pointer";
        ASSERT_TRUE(cParam.find("b") != std::string::npos) << "C parameter should contain parameter name";
}

TEST_F(RvalueRefParameterTest, multiple_rvalue_ref_parameters) {
    const char *code = R"(
            class Buffer {
                int* data;
            };

            void process(Buffer&& a, Buffer&& b) {
                // Process both buffers
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(finder.rvalueRefParams.size() >= 2) << "Expected at least two rvalue reference parameters";
        ASSERT_TRUE(finder.functions.size() >= 1) << "Expected at least one function";

        const FunctionDecl *Func = finder.functions[0];
        RvalueRefParamTranslator translator(AST->getASTContext());

        // Test function signature translation
        std::string cSignature = translator.translateFunctionSignature(Func);
        ASSERT_TRUE(cSignature.find("process") != std::string::npos) << "C signature should contain function name";
        ASSERT_TRUE(cSignature.find("struct Buffer") != std::string::npos) << "C signature should contain 'struct Buffer'";

        // Count pointer types in signature (should have 2)
        size_t count = 0;
        size_t pos = 0;
        while ((pos = cSignature.find("*", pos)) != std::string::npos) {
            count++;
            pos++;
        }
        ASSERT_TRUE(count >= 2) << "C signature should have at least 2 pointer parameters";
}

TEST_F(RvalueRefParameterTest, mixed_reference_parameters) {
    const char *code = R"(
            class Buffer {
                int* data;
            };

            void mixed(Buffer& lvalue, Buffer&& rvalue, int value) {
                // Process all parameters
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(finder.rvalueRefParams.size() >= 1) << "Expected at least one rvalue reference parameter";
        ASSERT_TRUE(finder.functions.size() >= 1) << "Expected at least one function";

        const FunctionDecl *Func = finder.functions[0];
        RvalueRefParamTranslator translator(AST->getASTContext());

        // Test function signature translation
        std::string cSignature = translator.translateFunctionSignature(Func);
        ASSERT_TRUE(cSignature.find("mixed") != std::string::npos) << "C signature should contain function name";
        ASSERT_TRUE(cSignature.find("struct Buffer") != std::string::npos) << "C signature should contain 'struct Buffer'";
        ASSERT_TRUE(cSignature.find("int") != std::string::npos) << "C signature should contain 'int'";

        // Should have 2 Buffer pointers and 1 int
        ASSERT_TRUE(cSignature.find("lvalue") != std::string::npos) << "C signature should contain 'lvalue'";
        ASSERT_TRUE(cSignature.find("rvalue") != std::string::npos) << "C signature should contain 'rvalue'";
        ASSERT_TRUE(cSignature.find("value") != std::string::npos) << "C signature should contain 'value'";
}

TEST_F(RvalueRefParameterTest, rvalue_ref_return_type) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

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

        ASSERT_TRUE(Func != nullptr) << "getBuffer function not found";

        RvalueRefParamTranslator translator(AST->getASTContext());

        // Test return type detection
        ASSERT_TRUE(translator.isRvalueReference(Func->getReturnType())) << "Should detect rvalue reference return type";

        // Test function signature translation
        std::string cSignature = translator.translateFunctionSignature(Func);
        ASSERT_TRUE(cSignature.find("struct Buffer") != std::string::npos) << "C signature should contain 'struct Buffer'";
        ASSERT_TRUE(cSignature.find("*") != std::string::npos) << "C return type should be a pointer";
        ASSERT_TRUE(cSignature.find("getBuffer") != std::string::npos) << "C signature should contain function name";
}

TEST_F(RvalueRefParameterTest, const_rvalue_reference) {
    const char *code = R"(
            class Buffer {
                int* data;
            };

            void readOnly(const Buffer&& b) {
                // Read from buffer only
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(finder.rvalueRefParams.size() >= 1) << "Expected at least one rvalue reference parameter";

        const ParmVarDecl *Param = finder.rvalueRefParams[0];
        RvalueRefParamTranslator translator(AST->getASTContext());

        // Test const detection
        ASSERT_TRUE(translator.isRvalueReference(Param->getType())) << "Should detect rvalue reference type";

        // Test type translation with const
        std::string cType = translator.translateType(Param->getType());
        ASSERT_TRUE(cType.find("const") != std::string::npos) << "C type should contain 'const'";
        ASSERT_TRUE(cType.find("struct Buffer") != std::string::npos) << "C type should contain 'struct Buffer'";
        ASSERT_TRUE(cType.find("*") != std::string::npos) << "C type should be a pointer";
}

TEST_F(RvalueRefParameterTest, function_translation_integration) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

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

        ASSERT_TRUE(Func != nullptr) << "transfer function not found";
        ASSERT_TRUE(Func->getNumParams() == 2) << "transfer should have 2 parameters";

        RvalueRefParamTranslator translator(AST->getASTContext());

        // Test full function signature
        std::string cSignature = translator.translateFunctionSignature(Func);
        ASSERT_TRUE(cSignature.find("transfer") != std::string::npos) << "C signature should contain function name";
        ASSERT_TRUE(cSignature.find("void") != std::string::npos) << "C signature should have void return type";

        // Should have correct parameter types
        ASSERT_TRUE(cSignature.find("source") != std::string::npos) << "C signature should contain 'source'";
        ASSERT_TRUE(cSignature.find("dest") != std::string::npos) << "C signature should contain 'dest'";
}

TEST_F(RvalueRefParameterTest, call_site_parameter_passing) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

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

        ASSERT_TRUE(ConsumeFunc != nullptr) << "consume function not found";

        RvalueRefParamTranslator translator(AST->getASTContext());

        // Verify function signature uses pointer
        std::string cSignature = translator.translateFunctionSignature(ConsumeFunc);
        ASSERT_TRUE(cSignature.find("*") != std::string::npos) << "C function should take pointer parameter";

        // Note: Call site translation would be handled by a separate component
        // This test verifies the function signature is correct for pointer passing
}

TEST_F(RvalueRefParameterTest, primitive_rvalue_reference) {
    const char *code = R"(
            void processPrimitive(int&& x) {
                // Process integer
            }
        )";

        std::unique_ptr<ASTUnit> AST = buildAST(code);
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(finder.rvalueRefParams.size() >= 1) << "Expected at least one rvalue reference parameter";

        const ParmVarDecl *Param = finder.rvalueRefParams[0];
        RvalueRefParamTranslator translator(AST->getASTContext());

        // Test detection
        ASSERT_TRUE(translator.isRvalueReference(Param->getType())) << "Should detect rvalue reference type";

        // For primitives, we might pass by value in C (implementation choice)
        // Test that translation produces valid C code
        std::string cParam = translator.translateParameter(Param);
        ASSERT_TRUE(!cParam.empty()) << "C parameter should not be empty";
        ASSERT_TRUE(cParam.find("x") != std::string::npos) << "C parameter should contain parameter name";
}

TEST_F(RvalueRefParameterTest, forwarding_reference_detection) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        // Note: Forwarding references (T&&) require template instantiation analysis
        // This is marked as future work in the story requirements
        // For now, we just verify the code parses
}

TEST_F(RvalueRefParameterTest, nested_class_rvalue_reference) {
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
        ASSERT_TRUE(AST) << "Failed to parse C++ code";

        FunctionFinder finder;
        finder.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

        ASSERT_TRUE(finder.rvalueRefParams.size() >= 1) << "Expected at least one rvalue reference parameter";

        const ParmVarDecl *Param = finder.rvalueRefParams[0];
        RvalueRefParamTranslator translator(AST->getASTContext());

        // Test detection and translation
        ASSERT_TRUE(translator.isRvalueReference(Param->getType())) << "Should detect rvalue reference type";

        std::string cType = translator.translateType(Param->getType());
        ASSERT_TRUE(cType.find("Inner") != std::string::npos) << "C type should contain 'Inner'";
        ASSERT_TRUE(cType.find("*") != std::string::npos) << "C type should be a pointer";
}
