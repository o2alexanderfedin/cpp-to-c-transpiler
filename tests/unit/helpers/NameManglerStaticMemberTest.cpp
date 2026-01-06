/**
 * @file NameManglerStaticMemberTest.cpp
 * @brief Tests for NameMangler static data member mangling (Phase 49 Task 1C)
 *
 * Tests the mangle_static_member() function that generates mangled names for
 * C++ static data members. Pattern: ClassName__memberName
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/DeclCXX.h"
#include "../../../include/NameMangler.h"
#include <cassert>

using namespace clang;

std::unique_ptr<ASTUnit> buildASTForStaticMember(const char *code) {
    return tooling::buildASTFromCode(code);
}

// Test fixture
class NameManglerStaticMemberTest : public ::testing::Test {
protected:
};

// Test 1: Mangle simple static member
TEST_F(NameManglerStaticMemberTest, SimpleStaticMember) {
    const char *code = R"(
        class Counter {
        public:
            static int count;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForStaticMember(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Find Counter and static member 'count'
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *Counter = nullptr;
    VarDecl *countMember = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Counter" && RD->isCompleteDefinition()) {
                Counter = RD;
                // Find static member in decls()
                for (auto *Decl : RD->decls()) {
                    if (auto *VD = dyn_cast<VarDecl>(Decl)) {
                        if (VD->getNameAsString() == "count") {
                            countMember = VD;
                            break;
                        }
                    }
                }
                break;
            }
        }
    }

    ASSERT_TRUE(Counter != nullptr) << "Counter class not found";
    ASSERT_TRUE(countMember != nullptr) << "Static member 'count' not found";
    ASSERT_TRUE(countMember->isStaticDataMember()) << "'count' should be static";

    std::string mangled = cpptoc::mangle_static_member(countMember);
    EXPECT_EQ("Counter__count", mangled);
}

// Test 2: Mangle static member in nested class
TEST_F(NameManglerStaticMemberTest, NestedClassStaticMember) {
    const char *code = R"(
        class Outer {
            class Inner {
            public:
                static int value;
            };
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForStaticMember(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Find Outer::Inner and static member 'value'
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *Inner = nullptr;
    VarDecl *valueMember = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *Outer = dyn_cast<CXXRecordDecl>(D)) {
            if (Outer->getNameAsString() == "Outer" && Outer->isCompleteDefinition()) {
                for (auto *InnerDecl : Outer->decls()) {
                    if (auto *InnerRD = dyn_cast<CXXRecordDecl>(InnerDecl)) {
                        if (InnerRD->getNameAsString() == "Inner" && InnerRD->isCompleteDefinition()) {
                            Inner = InnerRD;
                            for (auto *MemberDecl : InnerRD->decls()) {
                                if (auto *VD = dyn_cast<VarDecl>(MemberDecl)) {
                                    if (VD->getNameAsString() == "value") {
                                        valueMember = VD;
                                        break;
                                    }
                                }
                            }
                            break;
                        }
                    }
                }
                break;
            }
        }
    }

    ASSERT_TRUE(Inner != nullptr) << "Inner class not found";
    ASSERT_TRUE(valueMember != nullptr) << "Static member 'value' not found";

    std::string mangled = cpptoc::mangle_static_member(valueMember);
    EXPECT_EQ("Outer__Inner__value", mangled);
}

// Test 3: Mangle static member in namespaced class
TEST_F(NameManglerStaticMemberTest, NamespacedClassStaticMember) {
    const char *code = R"(
        namespace ns {
            class Config {
            public:
                static int maxSize;
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForStaticMember(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Find ns::Config and static member 'maxSize'
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *Config = nullptr;
    VarDecl *maxSizeMember = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
            if (ND->getNameAsString() == "ns") {
                for (auto *Inner : ND->decls()) {
                    if (auto *RD = dyn_cast<CXXRecordDecl>(Inner)) {
                        if (RD->getNameAsString() == "Config" && RD->isCompleteDefinition()) {
                            Config = RD;
                            for (auto *MemberDecl : RD->decls()) {
                                if (auto *VD = dyn_cast<VarDecl>(MemberDecl)) {
                                    if (VD->getNameAsString() == "maxSize") {
                                        maxSizeMember = VD;
                                        break;
                                    }
                                }
                            }
                            break;
                        }
                    }
                }
                break;
            }
        }
    }

    ASSERT_TRUE(Config != nullptr) << "Config class not found";
    ASSERT_TRUE(maxSizeMember != nullptr) << "Static member 'maxSize' not found";

    std::string mangled = cpptoc::mangle_static_member(maxSizeMember);
    EXPECT_EQ("ns__Config__maxSize", mangled);
}

// Test 4: Mangle static member with namespace and nested class
TEST_F(NameManglerStaticMemberTest, NamespaceNestedClassStaticMember) {
    const char *code = R"(
        namespace app {
            class Outer {
                class Inner {
                public:
                    static int data;
                };
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForStaticMember(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Find app::Outer::Inner and static member 'data'
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *Inner = nullptr;
    VarDecl *dataMember = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
            if (ND->getNameAsString() == "app") {
                for (auto *NsDecl : ND->decls()) {
                    if (auto *Outer = dyn_cast<CXXRecordDecl>(NsDecl)) {
                        if (Outer->getNameAsString() == "Outer" && Outer->isCompleteDefinition()) {
                            for (auto *OuterMember : Outer->decls()) {
                                if (auto *InnerRD = dyn_cast<CXXRecordDecl>(OuterMember)) {
                                    if (InnerRD->getNameAsString() == "Inner" && InnerRD->isCompleteDefinition()) {
                                        Inner = InnerRD;
                                        for (auto *InnerMember : InnerRD->decls()) {
                                            if (auto *VD = dyn_cast<VarDecl>(InnerMember)) {
                                                if (VD->getNameAsString() == "data") {
                                                    dataMember = VD;
                                                    break;
                                                }
                                            }
                                        }
                                        break;
                                    }
                                }
                            }
                            break;
                        }
                    }
                }
                break;
            }
        }
    }

    ASSERT_TRUE(Inner != nullptr) << "Inner class not found";
    ASSERT_TRUE(dataMember != nullptr) << "Static member 'data' not found";

    std::string mangled = cpptoc::mangle_static_member(dataMember);
    EXPECT_EQ("app__Outer__Inner__data", mangled);
}

// Test 5: Verify no collision with method names
TEST_F(NameManglerStaticMemberTest, NoCollisionWithMethodNames) {
    const char *code = R"(
        class Test {
        public:
            static int getValue;
            int getValue() { return 42; }
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForStaticMember(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Find Test class, static member 'getValue', and method 'getValue()'
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *Test = nullptr;
    VarDecl *getValueMember = nullptr;
    CXXMethodDecl *getValueMethod = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Test" && RD->isCompleteDefinition()) {
                Test = RD;
                for (auto *Decl : RD->decls()) {
                    if (auto *VD = dyn_cast<VarDecl>(Decl)) {
                        if (VD->getNameAsString() == "getValue") {
                            getValueMember = VD;
                        }
                    } else if (auto *MD = dyn_cast<CXXMethodDecl>(Decl)) {
                        if (MD->getNameAsString() == "getValue") {
                            getValueMethod = MD;
                        }
                    }
                }
                break;
            }
        }
    }

    ASSERT_TRUE(Test != nullptr) << "Test class not found";
    ASSERT_TRUE(getValueMember != nullptr) << "Static member 'getValue' not found";
    ASSERT_TRUE(getValueMethod != nullptr) << "Method 'getValue()' not found";

    std::string memberMangled = cpptoc::mangle_static_member(getValueMember);
    std::string methodMangled = cpptoc::mangle_method(getValueMethod);

    EXPECT_EQ("Test__getValue", memberMangled);
    EXPECT_EQ("Test__getValue__void", methodMangled);
    EXPECT_NE(memberMangled, methodMangled) << "Static member and method names must not collide";
}

// Test 6: Mangle multiple static members
TEST_F(NameManglerStaticMemberTest, MultipleStaticMembers) {
    const char *code = R"(
        class Stats {
        public:
            static int count;
            static int total;
            static int average;
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForStaticMember(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Find Stats class and all static members
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *Stats = nullptr;
    VarDecl *countMember = nullptr;
    VarDecl *totalMember = nullptr;
    VarDecl *averageMember = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "Stats" && RD->isCompleteDefinition()) {
                Stats = RD;
                for (auto *Decl : RD->decls()) {
                    if (auto *VD = dyn_cast<VarDecl>(Decl)) {
                        if (VD->getNameAsString() == "count") countMember = VD;
                        else if (VD->getNameAsString() == "total") totalMember = VD;
                        else if (VD->getNameAsString() == "average") averageMember = VD;
                    }
                }
                break;
            }
        }
    }

    ASSERT_TRUE(Stats != nullptr) << "Stats class not found";
    ASSERT_TRUE(countMember != nullptr) << "Static member 'count' not found";
    ASSERT_TRUE(totalMember != nullptr) << "Static member 'total' not found";
    ASSERT_TRUE(averageMember != nullptr) << "Static member 'average' not found";

    EXPECT_EQ("Stats__count", cpptoc::mangle_static_member(countMember));
    EXPECT_EQ("Stats__total", cpptoc::mangle_static_member(totalMember));
    EXPECT_EQ("Stats__average", cpptoc::mangle_static_member(averageMember));
}

// Test 7: Verify consistency with method mangling
TEST_F(NameManglerStaticMemberTest, ConsistencyWithMethodMangling) {
    const char *code = R"(
        namespace utils {
            class Helper {
            public:
                static int data;
                void process() {}
            };
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildASTForStaticMember(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    // Find utils::Helper, static member, and method
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    CXXRecordDecl *Helper = nullptr;
    VarDecl *dataMember = nullptr;
    CXXMethodDecl *processMethod = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
            if (ND->getNameAsString() == "utils") {
                for (auto *Inner : ND->decls()) {
                    if (auto *RD = dyn_cast<CXXRecordDecl>(Inner)) {
                        if (RD->getNameAsString() == "Helper" && RD->isCompleteDefinition()) {
                            Helper = RD;
                            for (auto *Member : RD->decls()) {
                                if (auto *VD = dyn_cast<VarDecl>(Member)) {
                                    if (VD->getNameAsString() == "data") dataMember = VD;
                                } else if (auto *MD = dyn_cast<CXXMethodDecl>(Member)) {
                                    if (MD->getNameAsString() == "process") processMethod = MD;
                                }
                            }
                            break;
                        }
                    }
                }
                break;
            }
        }
    }

    ASSERT_TRUE(Helper != nullptr) << "Helper class not found";
    ASSERT_TRUE(dataMember != nullptr) << "Static member 'data' not found";
    ASSERT_TRUE(processMethod != nullptr) << "Method 'process' not found";

    std::string memberMangled = cpptoc::mangle_static_member(dataMember);
    std::string methodMangled = cpptoc::mangle_method(processMethod);
    std::string classMangled = cpptoc::mangle_class(Helper);

    // Verify consistent double underscore pattern throughout
    EXPECT_EQ("utils__Helper__data", memberMangled);
    EXPECT_EQ("utils__Helper__process__void", methodMangled);
    EXPECT_EQ("utils__Helper", classMangled);

    // Verify all use consistent namespace and class naming
    EXPECT_TRUE(memberMangled.find("Helper__data") != std::string::npos) << "Static member should have double underscore before member name";
    EXPECT_TRUE(methodMangled.find("Helper__process") != std::string::npos) << "Method should have double underscore before method name";
}
