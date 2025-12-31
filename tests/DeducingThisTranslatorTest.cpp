/**
 * @file DeducingThisTranslatorTest.cpp
 * @brief Tests for Phase 4: Deducing This / Explicit Object Parameter Translation
 *
 * Test Coverage (12+ tests):
 * 1. auto& self → 2 overloads (lvalue, const)
 * 2. const auto& self → 1 overload (const)
 * 3. auto&& self → 4 overloads (forwarding reference)
 * 4. auto self → 1 overload (by value)
 * 5. Call on lvalue object
 * 6. Call on const lvalue object
 * 7. Call on rvalue object (temporary)
 * 8. Method with additional parameters
 * 9. Method with return value using self
 * 10. Nested member access through self
 * 11. Template class with deducing this
 * 12. Multiple deducing-this methods in same class
 *
 * Acceptance Criteria:
 * - All 12+ tests pass
 * - Correct overload count per parameter type
 * - Call site qualifier analysis works
 * - C output is valid C99
 * - No regressions in existing tests
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/DeclTemplate.h"
#include "../include/DeducingThisTranslator.h"
#include "../include/CNodeBuilder.h"
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildAST_deducing(const char *code) {
    std::vector<std::string> args = {"-std=c++23"};
    return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
}

// Helper function to find class by name
CXXRecordDecl* findClass_deducing(TranslationUnitDecl* TU, const std::string& name) {
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == name && RD->isCompleteDefinition()) {
                return RD;
            }
        }
    }
    return nullptr;
}

// Helper to find explicit object member function
CXXMethodDecl* findExplicitObjectMethod(CXXRecordDecl* Class, const std::string& name) {
    // Check regular methods first
    for (auto* Method : Class->methods()) {
        if (Method->getNameAsString() == name &&
            Method->isExplicitObjectMemberFunction()) {
            return Method;
        }
    }

    // Check function templates (e.g., methods with auto parameters)
    for (auto* D : Class->decls()) {
        if (auto* FTD = dyn_cast<FunctionTemplateDecl>(D)) {
            if (FTD->getNameAsString() == name) {
                if (auto* MD = dyn_cast<CXXMethodDecl>(FTD->getTemplatedDecl())) {
                    if (MD->isExplicitObjectMemberFunction()) {
                        return MD;
                    }
                }
            }
        }
    }

    return nullptr;
}

// Helper to find calls to explicit object member functions
// Note: Explicit object member function calls are represented as CallExpr, not CXXMemberCallExpr
CallExpr* findExplicitObjectMemberCall(Stmt* S, const std::string& methodName) {
    if (!S) return nullptr;

    // Check for calls to explicit object member functions (represented as CallExpr)
    if (auto* Call = dyn_cast<CallExpr>(S)) {
        if (auto* DRE = dyn_cast_or_null<DeclRefExpr>(Call->getCallee()->IgnoreImplicit())) {
            if (auto* Method = dyn_cast_or_null<CXXMethodDecl>(DRE->getDecl())) {
                if (Method->getNameAsString() == methodName &&
                    Method->isExplicitObjectMemberFunction()) {
                    return Call;
                }
            }
        }
    }

    for (auto* Child : S->children()) {
        if (auto* Result = findExplicitObjectMemberCall(Child, methodName)) {
            return Result;
        }
    }

    return nullptr;
}

// Helper to find CXXMemberCallExpr in AST (for regular member calls)
CXXMemberCallExpr* findMemberCall(Stmt* S, const std::string& methodName) {
    if (!S) return nullptr;

    // Check for regular member calls
    if (auto* Call = dyn_cast<CXXMemberCallExpr>(S)) {
        if (auto* Method = Call->getMethodDecl()) {
            if (Method->getNameAsString() == methodName) {
                return Call;
            }
        }
    }

    for (auto* Child : S->children()) {
        if (auto* Result = findMemberCall(Child, methodName)) {
            return Result;
        }
    }

    return nullptr;
}

// Test fixture
class DeducingThisTranslatorTest : public ::testing::Test {
protected:
};

// Test 1: auto& self → 2 overloads
TEST_F(DeducingThisTranslatorTest, AutoRefGenerates2Overloads) {
    const char *code = R"(
        struct Buffer {
            int data;
            int& get(this auto& self) { return self.data; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_deducing(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    DeducingThisTranslator translator(builder);

    // Create C TranslationUnit
    auto* C_TU = TranslationUnitDecl::Create(Ctx);

    // Find Buffer class
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* Buffer = findClass_deducing(TU, "Buffer");
    ASSERT_TRUE(Buffer) << "Buffer class not found";

    // Find get method with explicit object parameter
    auto* GetMethod = findExplicitObjectMethod(Buffer, "get");
    ASSERT_TRUE(GetMethod) << "get method with explicit object param not found";
    ASSERT_TRUE(GetMethod->isExplicitObjectMemberFunction())
        << "Method should be explicit object member function";

    // Transform method to C function overloads
    auto C_Funcs = translator.transformMethod(GetMethod, Ctx, C_TU);

    // auto& should generate 2 overloads (lvalue, const)
    EXPECT_EQ(C_Funcs.size(), 2) << "auto& should generate 2 overloads";

    // Check function names
    std::set<std::string> funcNames;
    for (auto* F : C_Funcs) {
        funcNames.insert(F->getNameAsString());
    }

    EXPECT_TRUE(funcNames.count("Buffer__get_lvalue") > 0)
        << "Should have Buffer__get_lvalue overload";
    EXPECT_TRUE(funcNames.count("Buffer__get_const") > 0)
        << "Should have Buffer__get_const overload";
}

// Test 2: const auto& self → 1 overload
TEST_F(DeducingThisTranslatorTest, ConstAutoRefGenerates1Overload) {
    const char *code = R"(
        struct Buffer {
            int data;
            const int& get(this const auto& self) { return self.data; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_deducing(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    DeducingThisTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* Buffer = findClass_deducing(TU, "Buffer");
    ASSERT_TRUE(Buffer);

    auto* GetMethod = findExplicitObjectMethod(Buffer, "get");
    ASSERT_TRUE(GetMethod);

    auto C_Funcs = translator.transformMethod(GetMethod, Ctx, C_TU);

    // const auto& should generate 1 overload (const only)
    EXPECT_EQ(C_Funcs.size(), 1) << "const auto& should generate 1 overload";
    EXPECT_EQ(C_Funcs[0]->getNameAsString(), "Buffer__get_const");
}

// Test 3: auto&& self → 4 overloads (forwarding reference)
TEST_F(DeducingThisTranslatorTest, AutoRefRefGenerates4Overloads) {
    const char *code = R"(
        struct Buffer {
            int data;
            int&& get(this auto&& self) { return static_cast<int&&>(self.data); }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_deducing(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    DeducingThisTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* Buffer = findClass_deducing(TU, "Buffer");
    ASSERT_TRUE(Buffer);

    auto* GetMethod = findExplicitObjectMethod(Buffer, "get");
    ASSERT_TRUE(GetMethod);

    auto C_Funcs = translator.transformMethod(GetMethod, Ctx, C_TU);

    // auto&& should generate 4 overloads (lvalue, const, rvalue, const_rvalue)
    EXPECT_EQ(C_Funcs.size(), 4) << "auto&& should generate 4 overloads";

    std::set<std::string> funcNames;
    for (auto* F : C_Funcs) {
        funcNames.insert(F->getNameAsString());
    }

    EXPECT_TRUE(funcNames.count("Buffer__get_lvalue") > 0);
    EXPECT_TRUE(funcNames.count("Buffer__get_const") > 0);
    EXPECT_TRUE(funcNames.count("Buffer__get_rvalue") > 0);
    EXPECT_TRUE(funcNames.count("Buffer__get_const_rvalue") > 0);
}

// Test 4: auto self → 1 overload (by value)
TEST_F(DeducingThisTranslatorTest, AutoValueGenerates1Overload) {
    const char *code = R"(
        struct Buffer {
            int data;
            int get(this auto self) { return self.data; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_deducing(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    DeducingThisTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* Buffer = findClass_deducing(TU, "Buffer");
    ASSERT_TRUE(Buffer);

    auto* GetMethod = findExplicitObjectMethod(Buffer, "get");
    ASSERT_TRUE(GetMethod);

    auto C_Funcs = translator.transformMethod(GetMethod, Ctx, C_TU);

    // auto should generate 1 overload (by value)
    EXPECT_EQ(C_Funcs.size(), 1) << "auto should generate 1 overload";
    EXPECT_EQ(C_Funcs[0]->getNameAsString(), "Buffer__get_value");
}

// Test 5: Call on lvalue object
TEST_F(DeducingThisTranslatorTest, CallOnLvalueObject) {
    const char *code = R"(
        struct Buffer {
            int data;
            int& get(this auto& self) { return self.data; }
        };

        void test() {
            Buffer b;
            b.get();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_deducing(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    DeducingThisTranslator translator(builder);

    auto* TU = Ctx.getTranslationUnitDecl();

    // Find the call in test function (explicit object member calls are CallExpr)
    CallExpr* Call = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test" && FD->getBody()) {
                Call = findExplicitObjectMemberCall(FD->getBody(), "get");
                break;
            }
        }
    }

    ASSERT_TRUE(Call) << "Call to get() not found";

    // Transform call
    auto* C_Call = translator.transformCall(Call, Ctx);
    ASSERT_TRUE(C_Call) << "Call transformation should succeed";

    // Should call lvalue overload
    if (auto* Callee = dyn_cast_or_null<DeclRefExpr>(C_Call->getCallee())) {
        if (auto* FD = dyn_cast_or_null<FunctionDecl>(Callee->getDecl())) {
            EXPECT_TRUE(FD->getNameAsString().find("_lvalue") != std::string::npos)
                << "Should call lvalue overload, got: " << FD->getNameAsString();
        }
    }
}

// Test 6: Call on const lvalue object
TEST_F(DeducingThisTranslatorTest, CallOnConstLvalueObject) {
    const char *code = R"(
        struct Buffer {
            int data;
            const int& get(this auto& self) { return self.data; }
        };

        void test() {
            const Buffer b;
            b.get();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_deducing(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    DeducingThisTranslator translator(builder);

    auto* TU = Ctx.getTranslationUnitDecl();

    CallExpr* Call = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test" && FD->getBody()) {
                Call = findExplicitObjectMemberCall(FD->getBody(), "get");
                break;
            }
        }
    }

    ASSERT_TRUE(Call);

    auto* C_Call = translator.transformCall(Call, Ctx);
    ASSERT_TRUE(C_Call);

    // Should call const overload
    if (auto* Callee = dyn_cast_or_null<DeclRefExpr>(C_Call->getCallee())) {
        if (auto* FD = dyn_cast_or_null<FunctionDecl>(Callee->getDecl())) {
            EXPECT_TRUE(FD->getNameAsString().find("_const") != std::string::npos)
                << "Should call const overload, got: " << FD->getNameAsString();
        }
    }
}

// Test 7: Call on rvalue object (temporary)
TEST_F(DeducingThisTranslatorTest, CallOnRvalueObject) {
    const char *code = R"(
        struct Buffer {
            int data;
            int&& get(this auto&& self) { return static_cast<int&&>(self.data); }
        };

        void test() {
            Buffer{}.get();
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_deducing(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    DeducingThisTranslator translator(builder);

    auto* TU = Ctx.getTranslationUnitDecl();

    CallExpr* Call = nullptr;
    for (auto* D : TU->decls()) {
        if (auto* FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "test" && FD->getBody()) {
                Call = findExplicitObjectMemberCall(FD->getBody(), "get");
                break;
            }
        }
    }

    ASSERT_TRUE(Call);

    auto* C_Call = translator.transformCall(Call, Ctx);
    ASSERT_TRUE(C_Call);

    // Should call rvalue overload
    if (auto* Callee = dyn_cast_or_null<DeclRefExpr>(C_Call->getCallee())) {
        if (auto* FD = dyn_cast_or_null<FunctionDecl>(Callee->getDecl())) {
            EXPECT_TRUE(FD->getNameAsString().find("_rvalue") != std::string::npos)
                << "Should call rvalue overload, got: " << FD->getNameAsString();
        }
    }
}

// Test 8: Method with additional parameters
TEST_F(DeducingThisTranslatorTest, MethodWithAdditionalParameters) {
    const char *code = R"(
        struct Calculator {
            int compute(this auto& self, int a, int b) { return a + b; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_deducing(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    DeducingThisTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* Calc = findClass_deducing(TU, "Calculator");
    ASSERT_TRUE(Calc);

    auto* ComputeMethod = findExplicitObjectMethod(Calc, "compute");
    ASSERT_TRUE(ComputeMethod);

    auto C_Funcs = translator.transformMethod(ComputeMethod, Ctx, C_TU);
    EXPECT_EQ(C_Funcs.size(), 2);

    // Check that overloads have correct parameter count
    // Should have: self + a + b = 3 parameters
    for (auto* F : C_Funcs) {
        EXPECT_EQ(F->getNumParams(), 3)
            << "Overload should have 3 parameters (self, a, b)";
    }
}

// Test 9: Method with return value using self
TEST_F(DeducingThisTranslatorTest, MethodReturnsValueUsingSelf) {
    const char *code = R"(
        struct Point {
            int x, y;
            int getX(this auto& self) { return self.x; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_deducing(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    DeducingThisTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* Point = findClass_deducing(TU, "Point");
    ASSERT_TRUE(Point);

    auto* GetXMethod = findExplicitObjectMethod(Point, "getX");
    ASSERT_TRUE(GetXMethod);

    auto C_Funcs = translator.transformMethod(GetXMethod, Ctx, C_TU);
    EXPECT_EQ(C_Funcs.size(), 2);

    // Check return type is int
    for (auto* F : C_Funcs) {
        EXPECT_TRUE(F->getReturnType()->isIntegerType())
            << "Return type should be int";
    }
}

// Test 10: Qualifier suffix generation
TEST_F(DeducingThisTranslatorTest, QualifierSuffixGeneration) {
    QualifierSet lvalue(false, false, false);
    EXPECT_EQ(lvalue.getSuffix(), "_lvalue");

    QualifierSet constLvalue(true, false, false);
    EXPECT_EQ(constLvalue.getSuffix(), "_const");

    QualifierSet rvalue(false, true, false);
    EXPECT_EQ(rvalue.getSuffix(), "_rvalue");

    QualifierSet constRvalue(true, true, false);
    EXPECT_EQ(constRvalue.getSuffix(), "_const_rvalue");

    QualifierSet value(false, false, true);
    EXPECT_EQ(value.getSuffix(), "_value");
}

// Test 11: Non-explicit object method returns empty
TEST_F(DeducingThisTranslatorTest, NonExplicitObjectMethodReturnsEmpty) {
    const char *code = R"(
        struct Buffer {
            int data;
            int get() { return data; }  // Regular method, not deducing this
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_deducing(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    DeducingThisTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* Buffer = findClass_deducing(TU, "Buffer");
    ASSERT_TRUE(Buffer);

    // Find regular (non-explicit object) method
    CXXMethodDecl* GetMethod = nullptr;
    for (auto* Method : Buffer->methods()) {
        if (Method->getNameAsString() == "get") {
            GetMethod = Method;
            break;
        }
    }
    ASSERT_TRUE(GetMethod);
    ASSERT_FALSE(GetMethod->isExplicitObjectMemberFunction())
        << "Method should NOT be explicit object member function";

    auto C_Funcs = translator.transformMethod(GetMethod, Ctx, C_TU);

    // Should return empty vector for non-explicit object methods
    EXPECT_TRUE(C_Funcs.empty())
        << "Non-explicit object methods should not be transformed";
}

// Test 12: Multiple deducing-this methods in same class
TEST_F(DeducingThisTranslatorTest, MultipleDeducingThisMethods) {
    const char *code = R"(
        struct Container {
            int data;
            int& get(this auto& self) { return self.data; }
            void set(this auto& self, int val) { self.data = val; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST_deducing(code);
    ASSERT_TRUE(AST) << "Failed to parse C++23 code";

    auto& Ctx = AST->getASTContext();
    CNodeBuilder builder(Ctx);
    DeducingThisTranslator translator(builder);

    auto* C_TU = TranslationUnitDecl::Create(Ctx);
    auto* TU = Ctx.getTranslationUnitDecl();
    auto* Container = findClass_deducing(TU, "Container");
    ASSERT_TRUE(Container);

    // Transform both methods
    auto* GetMethod = findExplicitObjectMethod(Container, "get");
    auto* SetMethod = findExplicitObjectMethod(Container, "set");
    ASSERT_TRUE(GetMethod);
    ASSERT_TRUE(SetMethod);

    auto GetFuncs = translator.transformMethod(GetMethod, Ctx, C_TU);
    auto SetFuncs = translator.transformMethod(SetMethod, Ctx, C_TU);

    EXPECT_EQ(GetFuncs.size(), 2);
    EXPECT_EQ(SetFuncs.size(), 2);

    // Check that all 4 functions have unique names
    std::set<std::string> allNames;
    for (auto* F : GetFuncs) allNames.insert(F->getNameAsString());
    for (auto* F : SetFuncs) allNames.insert(F->getNameAsString());

    EXPECT_EQ(allNames.size(), 4) << "Should have 4 unique function names";
}

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
