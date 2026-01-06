/**
 * @file ReferenceTranslationTest.cpp
 * @brief Test suite for C++ reference to C pointer translation (Phase 35-02 Bug Fix)
 *
 * CRITICAL BUG FIX: Phase 35-02 validation discovered that the transpiler
 * generates C++ reference syntax (&) in generated C code instead of C pointer syntax (*).
 *
 * Example of BUG:
 *   C++ Input:  Vector3D add(const Vector3D& other) const;
 *   BUGGY Output: Vector3D Vector3D_add(struct Vector3D * this, const Vector3D & other);
 *                                                                            ^^^^ ERROR: & in C code
 *   CORRECT Output: struct Vector3D Vector3D_add(struct Vector3D * this, const struct Vector3D * other);
 *                                                                                             ^^^ Pointer
 *
 * This test suite validates that ALL reference types are properly converted to pointers.
 *
 * Test-Driven Development (TDD):
 * - These tests will FAIL initially (that's the bug we're fixing)
 * - Implement fix in CodeGenerator.cpp
 * - Tests should then PASS
 */

#include <gtest/gtest.h>
#include "CodeGenerator.h"
#include "CNodeBuilder.h"
#include "FileOriginTracker.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <string>

using namespace clang;

// Helper to create AST from C++ code
std::unique_ptr<ASTUnit> buildAST(const std::string &code) {
  return tooling::buildASTFromCode(code);
}

// Helper to transpile C++ code and get generated C code
std::string transpileToCCode(const std::string &cppCode) {
    std::unique_ptr<ASTUnit> AST = buildAST(cppCode);
    if (!AST) {
        return "ERROR: Failed to parse C++ code";
    }

    ASTContext &Context = AST->getASTContext();
    CNodeBuilder builder(Context);
    cpptoc::FileOriginTracker tracker(Context.getSourceManager());
    tracker.addUserHeaderPath(".");
    TargetContext targetCtx;

    CppToCVisitor visitor(Context, builder, targetCtx, tracker, nullptr);
    visitor.TraverseDecl(Context.getTranslationUnitDecl());

    // Generate C code output from AST
    std::string output;
    llvm::raw_string_ostream OS(output);
    CodeGenerator generator(OS, Context);

    // Print all declarations from the context (C++ AST)
    // Note: visitor has transformed the C++ nodes, we print them here
    for (auto *D : Context.getTranslationUnitDecl()->decls()) {
        if (!D->isImplicit()) {
            generator.printDecl(D, false);
        }
    }

    OS.flush();
    return output;
}

// ============================================================================
// Test Fixture
// ============================================================================

class ReferenceTranslationTest : public ::testing::Test {
protected:
};

// ============================================================================
// Test 1: Const Lvalue Reference Parameter (most common case)
// ============================================================================

TEST_F(ReferenceTranslationTest, ConstLvalueReferenceParameter) {
    const char *cpp = R"(
        struct Vector3D {
            float x, y, z;
        };

        Vector3D add(const Vector3D& other) {
            return Vector3D{x + other.x, y + other.y, z + other.z};
        }
    )";

    std::string cCode = transpileToCCode(cpp);

    // CRITICAL: Should NOT contain C++ reference syntax
    EXPECT_EQ(cCode.find("&"), std::string::npos)
        << "CRITICAL BUG: Generated C code contains C++ reference syntax (&)!\n"
        << "Generated code:\n" << cCode;

    // MUST contain C pointer syntax
    EXPECT_NE(cCode.find("const struct Vector3D *"), std::string::npos)
        << "EXPECTED: 'const struct Vector3D *' (C pointer syntax)\n"
        << "Generated code:\n" << cCode;
}

// ============================================================================
// Test 2: Non-const Lvalue Reference Parameter
// ============================================================================

TEST_F(ReferenceTranslationTest, NonConstLvalueReferenceParameter) {
    const char *cpp = R"(
        struct Point {
            int x, y;
        };

        void modify(Point& p) {
            p.x = 10;
            p.y = 20;
        }
    )";

    std::string cCode = transpileToCCode(cpp);

    // Should NOT contain C++ reference syntax
    EXPECT_EQ(cCode.find("&"), std::string::npos)
        << "CRITICAL BUG: Generated C code contains C++ reference syntax (&)!\n"
        << "Generated code:\n" << cCode;

    // MUST contain C pointer syntax (without const)
    EXPECT_NE(cCode.find("struct Point *"), std::string::npos)
        << "EXPECTED: 'struct Point *' (C pointer syntax)\n"
        << "Generated code:\n" << cCode;
}

// ============================================================================
// Test 3: Rvalue Reference Parameter (C++11 move semantics)
// ============================================================================

TEST_F(ReferenceTranslationTest, RvalueReferenceParameter) {
    const char *cpp = R"(
        struct Resource {
            int* data;
        };

        void consume(Resource&& r) {
            // Move semantics
        }
    )";

    std::string cCode = transpileToCCode(cpp);

    // Should NOT contain C++ rvalue reference syntax (&&)
    EXPECT_EQ(cCode.find("&&"), std::string::npos)
        << "CRITICAL BUG: Generated C code contains C++ rvalue reference syntax (&&)!\n"
        << "Generated code:\n" << cCode;

    // MUST contain C pointer syntax
    EXPECT_NE(cCode.find("struct Resource *"), std::string::npos)
        << "EXPECTED: 'struct Resource *' (C pointer syntax for rvalue ref)\n"
        << "Generated code:\n" << cCode;
}

// ============================================================================
// Test 4: Reference Return Type
// ============================================================================

TEST_F(ReferenceTranslationTest, ReferenceReturnType) {
    const char *cpp = R"(
        struct Container {
            int data;
            int& get() { return data; }
        };
    )";

    std::string cCode = transpileToCCode(cpp);

    // Should NOT contain C++ reference syntax in return type
    // Note: This might legitimately have & in function body, so we check declaration only
    size_t funcPos = cCode.find("get(");
    if (funcPos != std::string::npos) {
        // Find the return type before get(
        std::string beforeFunc = cCode.substr(0, funcPos);
        size_t lastNewline = beforeFunc.rfind('\n');
        std::string declaration = (lastNewline != std::string::npos)
            ? beforeFunc.substr(lastNewline)
            : beforeFunc;

        EXPECT_EQ(declaration.find("&"), std::string::npos)
            << "CRITICAL BUG: Return type contains C++ reference syntax (&)!\n"
            << "Declaration: " << declaration;

        EXPECT_NE(declaration.find("int *"), std::string::npos)
            << "EXPECTED: 'int *' (C pointer return type)\n"
            << "Declaration: " << declaration;
    }
}

// ============================================================================
// Test 5: Multiple Reference Parameters
// ============================================================================

TEST_F(ReferenceTranslationTest, MultipleReferenceParameters) {
    const char *cpp = R"(
        struct Matrix {
            float data[9];
        };

        void multiply(const Matrix& a, const Matrix& b, Matrix& result) {
            // Matrix multiplication
        }
    )";

    std::string cCode = transpileToCCode(cpp);

    // Should NOT contain ANY C++ reference syntax
    EXPECT_EQ(cCode.find("&"), std::string::npos)
        << "CRITICAL BUG: Generated C code contains C++ reference syntax (&)!\n"
        << "Generated code:\n" << cCode;

    // MUST contain multiple C pointer parameters
    size_t firstPtr = cCode.find("const struct Matrix *");
    EXPECT_NE(firstPtr, std::string::npos)
        << "EXPECTED: First parameter as 'const struct Matrix *'\n"
        << "Generated code:\n" << cCode;

    if (firstPtr != std::string::npos) {
        size_t secondPtr = cCode.find("const struct Matrix *", firstPtr + 1);
        EXPECT_NE(secondPtr, std::string::npos)
            << "EXPECTED: Second parameter as 'const struct Matrix *'\n"
            << "Generated code:\n" << cCode;
    }

    EXPECT_NE(cCode.find("struct Matrix *"), std::string::npos)
        << "EXPECTED: Third parameter as 'struct Matrix *' (non-const)\n"
        << "Generated code:\n" << cCode;
}

// ============================================================================
// Test 6: Class with Method Taking Const Reference (Real-world case from validation)
// ============================================================================

TEST_F(ReferenceTranslationTest, ClassMethodConstReferenceParameter) {
    const char *cpp = R"(
        class Vector3D {
        public:
            float x, y, z;

            Vector3D(float x, float y, float z) : x(x), y(y), z(z) {}

            Vector3D add(const Vector3D& other) const {
                return Vector3D(x + other.x, y + other.y, z + other.z);
            }

            float dot(const Vector3D& other) const {
                return x * other.x + y * other.y + z * other.z;
            }
        };
    )";

    std::string cCode = transpileToCCode(cpp);

    // This is the EXACT bug from Phase 35-02 validation
    // The generated code was:
    //   Vector3D Vector3D_add(struct Vector3D * this, const Vector3D & other);
    //                                                               ^^^ BUG!
    // Should be:
    //   struct Vector3D Vector3D_add(struct Vector3D * this, const struct Vector3D * other);

    // Should NOT contain C++ reference syntax
    EXPECT_EQ(cCode.find("& "), std::string::npos)
        << "CRITICAL BUG: Generated C code contains C++ reference syntax (& )!\n"
        << "This is the EXACT bug found in Phase 35-02 validation!\n"
        << "Generated code:\n" << cCode;

    // MUST contain proper C pointer syntax for parameters
    EXPECT_NE(cCode.find("const struct Vector3D *"), std::string::npos)
        << "EXPECTED: Method parameters as 'const struct Vector3D *'\n"
        << "Generated code:\n" << cCode;

    // Return type should also have 'struct' keyword
    EXPECT_NE(cCode.find("struct Vector3D Vector3D_add"), std::string::npos)
        << "EXPECTED: Return type as 'struct Vector3D' (not just 'Vector3D')\n"
        << "Generated code:\n" << cCode;
}

// ============================================================================
// Test 7: Ensure no false positives (& in other contexts should be OK)
// ============================================================================

TEST_F(ReferenceTranslationTest, NoFalsePositivesForAddressOf) {
    const char *cpp = R"(
        struct Data {
            int value;
        };

        void usePointer(Data* p) {
            int* addr = &p->value;  // Address-of operator in function body is OK
        }
    )";

    std::string cCode = transpileToCCode(cpp);

    // The '&' in function BODY (&p->value) is OK in C
    // We only care that function DECLARATION doesn't have C++ reference syntax

    // Find the function declaration (before the opening brace)
    size_t funcStart = cCode.find("void usePointer");
    size_t bracePos = cCode.find("{", funcStart);

    if (funcStart != std::string::npos && bracePos != std::string::npos) {
        std::string declaration = cCode.substr(funcStart, bracePos - funcStart);

        // Declaration should NOT contain reference syntax (but might contain pointer)
        // Looking for pattern like "Data &" or "Data&" (reference parameter)
        EXPECT_EQ(declaration.find("Data &"), std::string::npos)
            << "Function declaration should not contain C++ reference syntax\n"
            << "Declaration: " << declaration;
        EXPECT_EQ(declaration.find("Data&"), std::string::npos)
            << "Function declaration should not contain C++ reference syntax\n"
            << "Declaration: " << declaration;

        // Should contain proper pointer syntax
        EXPECT_NE(declaration.find("Data *"), std::string::npos)
            << "EXPECTED: 'Data *' (C pointer syntax)\n"
            << "Declaration: " << declaration;
    }
}
