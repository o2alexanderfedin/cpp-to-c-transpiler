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

    NameMangler mangler(AST->getASTContext());

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

    std::string mangledInt = mangler.mangleName(addInt);
    std::string mangledDouble = mangler.mangleName(addDouble);

    ASSERT_TRUE(mangledInt == "Math_add" || mangledInt == "Math_add_int_int") << "Expected 'Math_add' or 'Math_add_int_int', got: " << mangledInt;
    ASSERT_TRUE(mangledDouble == "Math_add_float_float") << "Expected 'Math_add_float_float', got: " << mangledDouble;
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

    NameMangler mangler(AST->getASTContext());

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

    std::string mangledNonConst = mangler.mangleName(processNonConst);
    std::string mangledConst = mangler.mangleName(processConst);

    // Const qualification should be encoded
    ASSERT_TRUE(mangledConst.find("const") != std::string::npos || mangledNonConst != mangledConst) << "Const qualification must be preserved in mangling";
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

    NameMangler mangler(AST->getASTContext());

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

    std::string mangledValue = mangler.mangleName(handleValue);
    std::string mangledRef = mangler.mangleName(handleRef);

    // Reference should be encoded differently
    ASSERT_TRUE(mangledValue != mangledRef) << "Reference and value parameters must have different mangled names";
    ASSERT_TRUE(mangledRef.find("ref") != std::string::npos || mangledRef != mangledValue) << "Reference type must be encoded in mangling";
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

    NameMangler mangler(AST->getASTContext());

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

    std::string mangledInt = mangler.mangleName(computeInt);
    std::string mangledPoint = mangler.mangleName(computePoint);

    ASSERT_TRUE(mangledInt != mangledPoint) << "Overloaded methods with different types must have different names";
    ASSERT_TRUE(mangledPoint.find("Point") != std::string::npos) << "Class type name must appear in mangled name, got: " << mangledPoint;
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

    NameMangler mangler(AST->getASTContext());

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

    std::string mangled2 = mangler.mangleName(combine2);
    std::string mangled3 = mangler.mangleName(combine3);
    std::string mangledMixed = mangler.mangleName(combineMixed);

    // All three must be unique
    ASSERT_TRUE(mangled2 != mangled3) << "Different parameter counts must produce different names";
    ASSERT_TRUE(mangled2 != mangledMixed) << "Different parameter types must produce different names";
    ASSERT_TRUE(mangled3 != mangledMixed) << "All overloads must have unique names";
}

int main(int argc, char **argv) {
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
