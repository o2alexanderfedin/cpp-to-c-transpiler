// Test comprehensive struct return type generation scenarios
// Verifies that class/struct return types get proper 'struct' prefix in C code

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

TEST(StructReturnTypeTest, ValueReturnType) {
  const char *code = R"(
    class Vector3D {
    public:
      float x, y, z;

      Vector3D add(const Vector3D& other) {
        Vector3D result;
        result.x = x + other.x;
        result.y = y + other.y;
        result.z = z + other.z;
        return result;
      }
    };
  )";

  std::string output = transpileToCCode(code);
  ASSERT_FALSE(output.empty()) << "Failed to transpile code";

  // Return type should have 'struct' prefix
  EXPECT_TRUE(output.find("struct Vector3D Vector3D_add") != std::string::npos)
      << "Return type missing 'struct' prefix. Output:\n" << output;

  // Parameters should also have 'struct' prefix (existing fix verification)
  EXPECT_TRUE(output.find("const struct Vector3D *") != std::string::npos)
      << "Parameter type missing 'struct' prefix. Output:\n" << output;
}

TEST(StructReturnTypeTest, ReferenceReturnType) {
  const char *code = R"(
    class Vector3D {
    public:
      float x, y, z;

      Vector3D& scale(float factor) {
        x *= factor;
        y *= factor;
        z *= factor;
        return *this;
      }
    };
  )";

  std::string output = transpileToCCode(code);
  ASSERT_FALSE(output.empty()) << "Failed to transpile code";

  // Reference return type should become pointer with 'struct' prefix
  EXPECT_TRUE(output.find("struct Vector3D * Vector3D_scale") != std::string::npos)
      << "Reference return type should be 'struct Vector3D *'. Output:\n" << output;
}

TEST(StructReturnTypeTest, ConstReferenceReturnType) {
  const char *code = R"(
    class Vector3D {
    public:
      float x, y, z;

      const Vector3D& getThis() const {
        return *this;
      }
    };
  )";

  std::string output = transpileToCCode(code);
  ASSERT_FALSE(output.empty()) << "Failed to transpile code";

  // Const reference return type should become const pointer with 'struct' prefix
  EXPECT_TRUE(output.find("const struct Vector3D * Vector3D_getThis") != std::string::npos)
      << "Const reference return type should be 'const struct Vector3D *'. Output:\n" << output;
}

TEST(StructReturnTypeTest, PointerReturnType) {
  const char *code = R"(
    class Vector3D {
    public:
      float x, y, z;

      Vector3D* clone() {
        return new Vector3D(*this);
      }
    };
  )";

  std::string output = transpileToCCode(code);
  ASSERT_FALSE(output.empty()) << "Failed to transpile code";

  // Pointer return type should have 'struct' prefix
  EXPECT_TRUE(output.find("struct Vector3D * Vector3D_clone") != std::string::npos)
      << "Pointer return type should have 'struct' prefix. Output:\n" << output;
}

TEST(StructReturnTypeTest, ConstPointerReturnType) {
  const char *code = R"(
    class Vector3D {
    public:
      float x, y, z;

      const Vector3D* getData() const {
        return this;
      }
    };
  )";

  std::string output = transpileToCCode(code);
  ASSERT_FALSE(output.empty()) << "Failed to transpile code";

  // Const pointer return type should have 'struct' prefix
  EXPECT_TRUE(output.find("const struct Vector3D * Vector3D_getData") != std::string::npos)
      << "Const pointer return type should have 'struct' prefix. Output:\n" << output;
}

TEST(StructReturnTypeTest, StructKeywordReturnType) {
  const char *code = R"(
    struct Point {
      int x, y;

      Point translate(int dx, int dy) {
        Point result;
        result.x = x + dx;
        result.y = y + dy;
        return result;
      }
    };
  )";

  std::string output = transpileToCCode(code);
  ASSERT_FALSE(output.empty()) << "Failed to transpile code";

  // Struct return type should have 'struct' prefix
  EXPECT_TRUE(output.find("struct Point Point_translate") != std::string::npos)
      << "Struct return type missing 'struct' prefix. Output:\n" << output;
}

TEST(StructReturnTypeTest, PrimitiveReturnType) {
  const char *code = R"(
    class Vector3D {
    public:
      float x, y, z;

      float magnitude() const {
        return x * x + y * y + z * z;
      }

      int getIntX() const {
        return (int)x;
      }
    };
  )";

  std::string output = transpileToCCode(code);
  ASSERT_FALSE(output.empty()) << "Failed to transpile code";

  // Primitive return types should NOT have 'struct' prefix
  EXPECT_TRUE(output.find("float Vector3D_magnitude") != std::string::npos)
      << "Primitive return type should not have 'struct' prefix. Output:\n" << output;

  EXPECT_TRUE(output.find("int Vector3D_getIntX") != std::string::npos)
      << "Primitive return type should not have 'struct' prefix. Output:\n" << output;

  // Ensure we don't incorrectly add 'struct' to primitives
  EXPECT_TRUE(output.find("struct float") == std::string::npos)
      << "Primitive type should not have 'struct' prefix. Output:\n" << output;
  EXPECT_TRUE(output.find("struct int") == std::string::npos)
      << "Primitive type should not have 'struct' prefix. Output:\n" << output;
}

TEST(StructReturnTypeTest, VoidReturnType) {
  const char *code = R"(
    class Vector3D {
    public:
      float x, y, z;

      void normalize() {
        float mag = x * x + y * y + z * z;
        if (mag > 0) {
          x /= mag;
          y /= mag;
          z /= mag;
        }
      }
    };
  )";

  std::string output = transpileToCCode(code);
  ASSERT_FALSE(output.empty()) << "Failed to transpile code";

  // Void return type should remain void
  EXPECT_TRUE(output.find("void Vector3D_normalize") != std::string::npos)
      << "Void return type should remain void. Output:\n" << output;

  // Ensure we don't add 'struct' to void
  EXPECT_TRUE(output.find("struct void") == std::string::npos)
      << "Void type should not have 'struct' prefix. Output:\n" << output;
}

TEST(StructReturnTypeTest, MultipleMethodsWithDifferentReturnTypes) {
  const char *code = R"(
    class Vector3D {
    public:
      float x, y, z;

      Vector3D add(const Vector3D& other) {
        Vector3D result;
        result.x = x + other.x;
        result.y = y + other.y;
        result.z = z + other.z;
        return result;
      }

      Vector3D& scale(float factor) {
        x *= factor;
        y *= factor;
        z *= factor;
        return *this;
      }

      float magnitude() const {
        return x * x + y * y + z * z;
      }

      void reset() {
        x = y = z = 0.0f;
      }
    };
  )";

  std::string output = transpileToCCode(code);
  ASSERT_FALSE(output.empty()) << "Failed to transpile code";

  // Check all return types
  EXPECT_TRUE(output.find("struct Vector3D Vector3D_add") != std::string::npos)
      << "Value return type missing 'struct' prefix. Output:\n" << output;

  EXPECT_TRUE(output.find("struct Vector3D * Vector3D_scale") != std::string::npos)
      << "Reference return type should be pointer with 'struct' prefix. Output:\n" << output;

  EXPECT_TRUE(output.find("float Vector3D_magnitude") != std::string::npos)
      << "Primitive return type should not have 'struct' prefix. Output:\n" << output;

  EXPECT_TRUE(output.find("void Vector3D_reset") != std::string::npos)
      << "Void return type should remain void. Output:\n" << output;
}

// Bug #16: Test that returning a local variable doesn't create compound literal syntax
TEST(StructReturnTypeTest, ReturnLocalVariableNoCopyConstructor) {
  const char *code = R"(
    class Matrix3x3 {
    public:
      float data[9];

      Matrix3x3() {
        for (int i = 0; i < 9; i++) data[i] = 0.0f;
      }

      Matrix3x3 add(const Matrix3x3& other) const {
        Matrix3x3 result;
        for (int i = 0; i < 9; i++) {
          result.data[i] = data[i] + other.data[i];
        }
        return result;
      }
    };
  )";

  std::string output = transpileToCCode(code);
  ASSERT_FALSE(output.empty()) << "Failed to transpile code";

  // Bug #16: Should NOT have compound literal syntax like:
  //   return (struct Matrix3x3){result};
  // Should have simple return:
  //   return result;
  EXPECT_TRUE(output.find("return (struct Matrix3x3){result}") == std::string::npos)
      << "Bug #16: Found invalid compound literal syntax. Should be 'return result;'. Output:\n" << output;

  // Should have simple return statement
  EXPECT_TRUE(output.find("return result") != std::string::npos)
      << "Bug #16: Missing simple 'return result;' statement. Output:\n" << output;
}

// Bug #16: Test that constructor calls still use compound literals correctly
TEST(StructReturnTypeTest, ReturnConstructorCallUsesCompoundLiteral) {
  const char *code = R"(
    class Vector3D {
    public:
      float x, y, z;

      Vector3D(float x, float y, float z) : x(x), y(y), z(z) {}

      Vector3D scale(float factor) const {
        return Vector3D(x * factor, y * factor, z * factor);
      }
    };
  )";

  std::string output = transpileToCCode(code);
  ASSERT_FALSE(output.empty()) << "Failed to transpile code";

  // Should have compound literal for constructor call with arguments
  EXPECT_TRUE(output.find("return (struct Vector3D){") != std::string::npos)
      << "Constructor call should use compound literal syntax. Output:\n" << output;
}
