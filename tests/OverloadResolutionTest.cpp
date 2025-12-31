#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include <gtest/gtest.h>
#include "../include/NameMangler.h"
#include <cassert>

using namespace clang;

// Google Test Fixture
class OverloadResolutionTest : public ::testing::Test {
protected:
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }
};

// Test 1: Simple overload with different primitive types
TEST_F(OverloadResolutionTest, PrimitiveTypeOverloads) {
    const char *code = R"(
        class Math {
        public:
            int add(int a, int b);
            double add(double a, double b);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Find both add methods
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXMethodDecl *addInt = nullptr;
    CXXMethodDecl *addDouble = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Math") {
                for (auto *M : RD->methods()) {
                    if (M->getNameAsString() == "add") {
                        if (M->getNumParams() == 2) {
                            QualType FirstParam = M->getParamDecl(0)->getType();
                            if (FirstParam->isIntegerType()) {
                                addInt = M;
                            } else if (FirstParam->isFloatingType()) {
                                addDouble = M;
                            }
                        }
                    }
                }
            }
        }
    }

    ASSERT_TRUE(addInt != nullptr) << "Math::add(int, int) not found";
    ASSERT_TRUE(addDouble != nullptr) << "Math::add(double, double) not found";

    std::string mangledInt = cpptoc::mangle_method(addInt);
    std::string mangledDouble = cpptoc::mangle_method(addDouble);

    // Verify separator pattern and overload differentiation
    EXPECT_EQ("Math__add__int_int", mangledInt);
    EXPECT_EQ("Math__add__double_double", mangledDouble);
    ASSERT_TRUE(mangledInt != mangledDouble) << "Overloaded methods must have different mangled names";
}

// Test 2: Const qualification in parameters
TEST_F(OverloadResolutionTest, ConstQualification) {
    const char *code = R"(
        class Processor {
        public:
            void process(int value);
            void process(const int value);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Find both process methods
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXMethodDecl *processNonConst = nullptr;
    CXXMethodDecl *processConst = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Processor") {
                for (auto *M : RD->methods()) {
                    if (M->getNameAsString() == "process" && M->getNumParams() == 1) {
                        QualType ParamType = M->getParamDecl(0)->getType();
                        if (ParamType.isConstQualified()) {
                            processConst = M;
                        } else {
                            processNonConst = M;
                        }
                    }
                }
            }
        }
    }

    ASSERT_TRUE(processNonConst != nullptr) << "Processor::process(int) not found";
    ASSERT_TRUE(processConst != nullptr) << "Processor::process(const int) not found";

    std::string mangledNonConst = cpptoc::mangle_method(processNonConst);
    std::string mangledConst = cpptoc::mangle_method(processConst);

    // Verify separator pattern
    EXPECT_TRUE(mangledNonConst.find("__") != std::string::npos) << "Expected __ separator pattern";
    EXPECT_TRUE(mangledConst.find("__") != std::string::npos) << "Expected __ separator pattern";

    // Const qualification should be encoded
    ASSERT_TRUE(mangledConst.find("const") != std::string::npos || mangledNonConst != mangledConst)
        << "Const qualification must be preserved in mangling";
}

// Test 3: Reference types
TEST_F(OverloadResolutionTest, ReferenceTypes) {
    const char *code = R"(
        class Handler {
        public:
            void handle(int value);
            void handle(int& ref);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Find both handle methods
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXMethodDecl *handleValue = nullptr;
    CXXMethodDecl *handleRef = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Handler") {
                for (auto *M : RD->methods()) {
                    if (M->getNameAsString() == "handle" && M->getNumParams() == 1) {
                        QualType ParamType = M->getParamDecl(0)->getType();
                        if (ParamType->isReferenceType()) {
                            handleRef = M;
                        } else {
                            handleValue = M;
                        }
                    }
                }
            }
        }
    }

    ASSERT_TRUE(handleValue != nullptr) << "Handler::handle(int) not found";
    ASSERT_TRUE(handleRef != nullptr) << "Handler::handle(int&) not found";

    std::string mangledValue = cpptoc::mangle_method(handleValue);
    std::string mangledRef = cpptoc::mangle_method(handleRef);

    // Verify separator pattern
    EXPECT_TRUE(mangledValue.find("__") != std::string::npos) << "Expected __ separator pattern";
    EXPECT_TRUE(mangledRef.find("__") != std::string::npos) << "Expected __ separator pattern";

    // Reference should be encoded differently
    ASSERT_TRUE(mangledValue != mangledRef) << "Reference and value parameters must have different mangled names";
    ASSERT_TRUE(mangledRef.find("ref") != std::string::npos || mangledRef != mangledValue)
        << "Reference type must be encoded in mangling";
}

// Test 4: Class type parameters
TEST_F(OverloadResolutionTest, ClassTypeParameters) {
    const char *code = R"(
        class Point {
        public:
            int x, y;
        };

        class Calculator {
        public:
            int compute(int value);
            int compute(Point p);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Find both compute methods
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXMethodDecl *computeInt = nullptr;
    CXXMethodDecl *computePoint = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Calculator") {
                for (auto *M : RD->methods()) {
                    if (M->getNameAsString() == "compute" && M->getNumParams() == 1) {
                        QualType ParamType = M->getParamDecl(0)->getType();
                        if (ParamType->isIntegerType()) {
                            computeInt = M;
                        } else if (ParamType->isRecordType()) {
                            computePoint = M;
                        }
                    }
                }
            }
        }
    }

    ASSERT_TRUE(computeInt != nullptr) << "Calculator::compute(int) not found";
    ASSERT_TRUE(computePoint != nullptr) << "Calculator::compute(Point) not found";

    std::string mangledInt = cpptoc::mangle_method(computeInt);
    std::string mangledPoint = cpptoc::mangle_method(computePoint);

    // Verify separator pattern
    EXPECT_TRUE(mangledInt.find("__") != std::string::npos) << "Expected __ separator pattern";
    EXPECT_TRUE(mangledPoint.find("__") != std::string::npos) << "Expected __ separator pattern";

    ASSERT_TRUE(mangledInt != mangledPoint) << "Overloaded methods with different types must have different names";
    ASSERT_TRUE(mangledPoint.find("Point") != std::string::npos)
        << "Class type name must appear in mangled name, got: " << mangledPoint;
}

// Test 5: Multiple parameters
TEST_F(OverloadResolutionTest, MultipleParameters) {
    const char *code = R"(
        class Combiner {
        public:
            int combine(int a, int b);
            int combine(int a, int b, int c);
            double combine(int a, double b);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Find all three combine methods
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXMethodDecl *combine2 = nullptr;
    CXXMethodDecl *combine3 = nullptr;
    CXXMethodDecl *combineMixed = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Combiner") {
                for (auto *M : RD->methods()) {
                    if (M->getNameAsString() == "combine") {
                        if (M->getNumParams() == 2) {
                            QualType SecondParam = M->getParamDecl(1)->getType();
                            if (SecondParam->isIntegerType()) {
                                combine2 = M;
                            } else if (SecondParam->isFloatingType()) {
                                combineMixed = M;
                            }
                        } else if (M->getNumParams() == 3) {
                            combine3 = M;
                        }
                    }
                }
            }
        }
    }

    ASSERT_TRUE(combine2 != nullptr) << "Combiner::combine(int, int) not found";
    ASSERT_TRUE(combine3 != nullptr) << "Combiner::combine(int, int, int) not found";
    ASSERT_TRUE(combineMixed != nullptr) << "Combiner::combine(int, double) not found";

    std::string mangled2 = cpptoc::mangle_method(combine2);
    std::string mangled3 = cpptoc::mangle_method(combine3);
    std::string mangledMixed = cpptoc::mangle_method(combineMixed);

    // Verify separator pattern
    EXPECT_TRUE(mangled2.find("__") != std::string::npos) << "Expected __ separator pattern";
    EXPECT_TRUE(mangled3.find("__") != std::string::npos) << "Expected __ separator pattern";
    EXPECT_TRUE(mangledMixed.find("__") != std::string::npos) << "Expected __ separator pattern";

    // All three must be unique
    ASSERT_TRUE(mangled2 != mangled3) << "Different parameter counts must produce different names";
    ASSERT_TRUE(mangled2 != mangledMixed) << "Different parameter types must produce different names";
    ASSERT_TRUE(mangled3 != mangledMixed) << "All overloads must have unique names";
}

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
