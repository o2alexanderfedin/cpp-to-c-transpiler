// TDD GREEN Phase: Tests for CNodeBuilder type helpers
// Story #9: CNodeBuilder structure and type helpers

#include <gtest/gtest.h>
#include "CNodeBuilder.h"
#include "clang/Tooling/Tooling.h"

using namespace clang;

TEST(CNodeBuilder, Constructor) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    CNodeBuilder builder(Ctx);
}

TEST(CNodeBuilder, intType) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    ");
        CNodeBuilder builder(Ctx);
        QualType intTy = builder.intType();
        ASSERT_TRUE(!intTy.isNull()) << "intType returned null";
        ASSERT_TRUE(intTy->isIntegerType()) << "intType not an integer type";");
}

TEST(CNodeBuilder, voidType) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    ");
        CNodeBuilder builder(Ctx);
        QualType voidTy = builder.voidType();
        ASSERT_TRUE(!voidTy.isNull()) << "voidType returned null";
        ASSERT_TRUE(voidTy->isVoidType()) << "voidType not a void type";");
}

TEST(CNodeBuilder, charType) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    ");
        CNodeBuilder builder(Ctx);
        QualType charTy = builder.charType();
        ASSERT_TRUE(!charTy.isNull()) << "charType returned null";
        ASSERT_TRUE(charTy->isCharType()) << "charType not a char type";");
}

TEST(CNodeBuilder, ptrType) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    ");
        CNodeBuilder builder(Ctx);
        QualType intTy = builder.intType();
        QualType ptrTy = builder.ptrType(intTy);
        ASSERT_TRUE(!ptrTy.isNull()) << "ptrType returned null";
        ASSERT_TRUE(ptrTy->isPointerType()) << "ptrType not a pointer type";");
}

TEST(CNodeBuilder, structType) {
    // Build AST for test
    const char *code = R"(int main() { return 0; })";
    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASTContext &Ctx = AST->getASTContext();

    ");
        CNodeBuilder builder(Ctx);
        QualType structTy = builder.structType("Point");
        ASSERT_TRUE(!structTy.isNull()) << "structType returned null";
        ASSERT_TRUE(structTy->isStructureType()) << "structType not a structure type";");
}
