/**
 * Unit tests for OverloadRegistry
 *
 * Tests the global overload tracking system that enables consistent
 * cross-file name mangling for overloaded functions.
 *
 * Following TDD approach - tests written before implementation.
 */

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/AST/DeclCXX.h"
#include "../../include/OverloadRegistry.h"
#include <cassert>

using namespace clang;
using namespace cpptoc;

// Test fixture
class OverloadRegistryTest : public ::testing::Test {
protected:
    void SetUp() override {
        // Clear registry before each test for isolation
        OverloadRegistry::getInstance().reset();
    }

    void TearDown() override {
        // Clean up after each test
        OverloadRegistry::getInstance().reset();
    }

    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return tooling::buildASTFromCode(code);
    }

    // Helper: Find function by name in AST
    FunctionDecl* findFunction(ASTUnit& AST, const std::string& name) {
        auto *TU = AST.getASTContext().getTranslationUnitDecl();
        for (auto *D : TU->decls()) {
            if (auto *FD = dyn_cast<FunctionDecl>(D)) {
                if (FD->getNameAsString() == name) {
                    return FD;
                }
            }
            // Also search in namespaces
            if (auto *ND = dyn_cast<NamespaceDecl>(D)) {
                for (auto *ND_D : ND->decls()) {
                    if (auto *FD = dyn_cast<FunctionDecl>(ND_D)) {
                        if (FD->getNameAsString() == name) {
                            return FD;
                        }
                    }
                }
            }
        }
        return nullptr;
    }

    // Helper: Find method by class and method name
    CXXMethodDecl* findMethod(ASTUnit& AST, const std::string& className, const std::string& methodName) {
        auto *TU = AST.getASTContext().getTranslationUnitDecl();
        for (auto *D : TU->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == className) {
                    for (auto *M : RD->methods()) {
                        if (M->getNameAsString() == methodName) {
                            return M;
                        }
                    }
                }
            }
        }
        return nullptr;
    }
};

// ============================================================================
// Test 1: Singleton Access
// ============================================================================

TEST_F(OverloadRegistryTest, SingletonAccess) {
    // Registry should be accessible as singleton
    OverloadRegistry& registry1 = OverloadRegistry::getInstance();
    OverloadRegistry& registry2 = OverloadRegistry::getInstance();

    // Both references should point to same instance
    ASSERT_EQ(&registry1, &registry2) << "Singleton must return same instance";
}

// ============================================================================
// Test 2: Register Single Function
// ============================================================================

TEST_F(OverloadRegistryTest, RegisterSingleFunction) {
    const char *code = R"(
        void foo(int x);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl* foo = findFunction(*AST, "foo");
    ASSERT_TRUE(foo != nullptr) << "Function 'foo' not found";

    OverloadRegistry& registry = OverloadRegistry::getInstance();

    // Register function with mangled name
    std::string baseName = "foo";
    std::string mangledName = "foo_int";
    registry.registerOverload(baseName, foo, mangledName);

    // Query should return single overload
    std::vector<std::string> overloads = registry.getOverloads(baseName);
    ASSERT_EQ(overloads.size(), 1u) << "Expected 1 overload";
    ASSERT_EQ(overloads[0], mangledName) << "Expected mangled name 'foo_int'";
}

// ============================================================================
// Test 3: Register Multiple Overloads
// ============================================================================

TEST_F(OverloadRegistryTest, RegisterMultipleOverloads) {
    const char *code = R"(
        void foo(int x);
        void foo(double x);
        void foo(int x, int y);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    OverloadRegistry& registry = OverloadRegistry::getInstance();
    std::string baseName = "foo";

    // Find all three overloads and register them
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    int funcCount = 0;
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "foo") {
                std::string mangledName;
                if (FD->getNumParams() == 1) {
                    QualType paramType = FD->getParamDecl(0)->getType();
                    if (paramType->isIntegerType()) {
                        mangledName = "foo_int";
                    } else if (paramType->isFloatingType()) {
                        mangledName = "foo_double";
                    }
                } else if (FD->getNumParams() == 2) {
                    mangledName = "foo_int_int";
                }
                registry.registerOverload(baseName, FD, mangledName);
                funcCount++;
            }
        }
    }

    ASSERT_EQ(funcCount, 3) << "Expected to find 3 overloads";

    // Query should return all three overloads
    std::vector<std::string> overloads = registry.getOverloads(baseName);
    ASSERT_EQ(overloads.size(), 3u) << "Expected 3 overloads";
}

// ============================================================================
// Test 4: Deterministic Ordering
// ============================================================================

TEST_F(OverloadRegistryTest, DeterministicOrdering) {
    const char *code = R"(
        void foo(double x);
        void foo(int x);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    OverloadRegistry& registry = OverloadRegistry::getInstance();
    std::string baseName = "foo";

    // Register in one order (double first, then int)
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "foo") {
                QualType paramType = FD->getParamDecl(0)->getType();
                std::string mangledName;
                if (paramType->isFloatingType()) {
                    mangledName = "foo_double";
                } else if (paramType->isIntegerType()) {
                    mangledName = "foo_int";
                }
                registry.registerOverload(baseName, FD, mangledName);
            }
        }
    }

    std::vector<std::string> overloads1 = registry.getOverloads(baseName);

    // Reset and register in reverse order
    registry.reset();

    std::unique_ptr<ASTUnit> AST2 = buildAST(code);
    ASSERT_TRUE(AST2) << "Failed to parse C++ code";

    auto *TU2 = AST2->getASTContext().getTranslationUnitDecl();
    std::vector<FunctionDecl*> funcs;
    for (auto *D : TU2->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "foo") {
                funcs.push_back(FD);
            }
        }
    }

    // Register in reverse order
    for (auto it = funcs.rbegin(); it != funcs.rend(); ++it) {
        FunctionDecl* FD = *it;
        QualType paramType = FD->getParamDecl(0)->getType();
        std::string mangledName;
        if (paramType->isFloatingType()) {
            mangledName = "foo_double";
        } else if (paramType->isIntegerType()) {
            mangledName = "foo_int";
        }
        registry.registerOverload(baseName, FD, mangledName);
    }

    std::vector<std::string> overloads2 = registry.getOverloads(baseName);

    // Ordering should be deterministic regardless of insertion order
    ASSERT_EQ(overloads1, overloads2) << "Overload ordering must be deterministic";
}

// ============================================================================
// Test 5: Query Non-Existent Function
// ============================================================================

TEST_F(OverloadRegistryTest, QueryNonExistent) {
    OverloadRegistry& registry = OverloadRegistry::getInstance();

    std::vector<std::string> overloads = registry.getOverloads("nonexistent");
    ASSERT_TRUE(overloads.empty()) << "Non-existent function should return empty vector";
}

// ============================================================================
// Test 6: Reset Functionality
// ============================================================================

TEST_F(OverloadRegistryTest, ResetClearsRegistry) {
    const char *code = R"(
        void foo(int x);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl* foo = findFunction(*AST, "foo");
    ASSERT_TRUE(foo != nullptr) << "Function 'foo' not found";

    OverloadRegistry& registry = OverloadRegistry::getInstance();

    // Register function
    registry.registerOverload("foo", foo, "foo_int");
    ASSERT_EQ(registry.getOverloads("foo").size(), 1u) << "Expected 1 overload before reset";

    // Reset should clear all registrations
    registry.reset();
    ASSERT_TRUE(registry.getOverloads("foo").empty()) << "Registry should be empty after reset";
}

// ============================================================================
// Test 7: Get Overload Index
// ============================================================================

TEST_F(OverloadRegistryTest, GetOverloadIndex) {
    const char *code = R"(
        void foo(int x);
        void foo(double x);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    OverloadRegistry& registry = OverloadRegistry::getInstance();
    std::string baseName = "foo";

    // Register overloads
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    FunctionDecl* fooInt = nullptr;
    FunctionDecl* fooDouble = nullptr;

    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "foo") {
                QualType paramType = FD->getParamDecl(0)->getType();
                if (paramType->isIntegerType()) {
                    fooInt = FD;
                    registry.registerOverload(baseName, FD, "foo_int");
                } else if (paramType->isFloatingType()) {
                    fooDouble = FD;
                    registry.registerOverload(baseName, FD, "foo_double");
                }
            }
        }
    }

    ASSERT_TRUE(fooInt != nullptr) << "foo(int) not found";
    ASSERT_TRUE(fooDouble != nullptr) << "foo(double) not found";

    // Get indices
    int index1 = registry.getOverloadIndex(baseName, fooInt);
    int index2 = registry.getOverloadIndex(baseName, fooDouble);

    ASSERT_GE(index1, 0) << "Index should be non-negative";
    ASSERT_GE(index2, 0) << "Index should be non-negative";
    ASSERT_NE(index1, index2) << "Different overloads should have different indices";
}

// ============================================================================
// Test 8: Namespace Support
// ============================================================================

TEST_F(OverloadRegistryTest, NamespaceQualifiedFunctions) {
    const char *code = R"(
        namespace ns {
            void foo(int x);
        }
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl* foo = findFunction(*AST, "foo");
    ASSERT_TRUE(foo != nullptr) << "Function 'ns::foo' not found";

    OverloadRegistry& registry = OverloadRegistry::getInstance();

    // Register with namespace-qualified base name
    std::string baseName = "ns::foo";
    std::string mangledName = "ns_foo_int";
    registry.registerOverload(baseName, foo, mangledName);

    // Query with qualified name
    std::vector<std::string> overloads = registry.getOverloads(baseName);
    ASSERT_EQ(overloads.size(), 1u) << "Expected 1 overload for ns::foo";
    ASSERT_EQ(overloads[0], mangledName) << "Expected mangled name 'ns_foo_int'";

    // Query with unqualified name should return empty
    std::vector<std::string> unqualified = registry.getOverloads("foo");
    ASSERT_TRUE(unqualified.empty()) << "Unqualified query should not match qualified function";
}

// ============================================================================
// Test 9: Method Overloads
// ============================================================================

TEST_F(OverloadRegistryTest, MethodOverloads) {
    const char *code = R"(
        class MyClass {
        public:
            void method(int x);
            void method(double x);
        };
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    OverloadRegistry& registry = OverloadRegistry::getInstance();
    std::string baseName = "MyClass::method";

    // Find and register both methods
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    for (auto *D : TU->decls()) {
        if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
            if (RD->getNameAsString() == "MyClass") {
                for (auto *M : RD->methods()) {
                    if (M->getNameAsString() == "method") {
                        QualType paramType = M->getParamDecl(0)->getType();
                        std::string mangledName;
                        if (paramType->isIntegerType()) {
                            mangledName = "MyClass_method_int";
                        } else if (paramType->isFloatingType()) {
                            mangledName = "MyClass_method_double";
                        }
                        registry.registerOverload(baseName, M, mangledName);
                    }
                }
            }
        }
    }

    // Query should return both method overloads
    std::vector<std::string> overloads = registry.getOverloads(baseName);
    ASSERT_EQ(overloads.size(), 2u) << "Expected 2 method overloads";
}

// ============================================================================
// Test 10: Duplicate Registration
// ============================================================================

TEST_F(OverloadRegistryTest, DuplicateRegistration) {
    const char *code = R"(
        void foo(int x);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl* foo = findFunction(*AST, "foo");
    ASSERT_TRUE(foo != nullptr) << "Function 'foo' not found";

    OverloadRegistry& registry = OverloadRegistry::getInstance();

    // Register same function twice
    registry.registerOverload("foo", foo, "foo_int");
    registry.registerOverload("foo", foo, "foo_int");

    // Should only store once (de-duplication)
    std::vector<std::string> overloads = registry.getOverloads("foo");
    ASSERT_EQ(overloads.size(), 1u) << "Duplicate registration should not create duplicates";
}

// ============================================================================
// Test 11: Get Mangled Name by Declaration
// ============================================================================

TEST_F(OverloadRegistryTest, GetMangledNameByDecl) {
    const char *code = R"(
        void foo(int x);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl* foo = findFunction(*AST, "foo");
    ASSERT_TRUE(foo != nullptr) << "Function 'foo' not found";

    OverloadRegistry& registry = OverloadRegistry::getInstance();

    std::string baseName = "foo";
    std::string mangledName = "foo_int";
    registry.registerOverload(baseName, foo, mangledName);

    // Retrieve mangled name using declaration pointer
    std::string retrieved = registry.getMangledName(baseName, foo);
    ASSERT_EQ(retrieved, mangledName) << "Should retrieve correct mangled name";
}

// ============================================================================
// Test 12: Get Mangled Name for Unregistered Declaration
// ============================================================================

TEST_F(OverloadRegistryTest, GetMangledNameUnregistered) {
    const char *code = R"(
        void foo(int x);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    FunctionDecl* foo = findFunction(*AST, "foo");
    ASSERT_TRUE(foo != nullptr) << "Function 'foo' not found";

    OverloadRegistry& registry = OverloadRegistry::getInstance();

    // Query without registration should return empty string
    std::string retrieved = registry.getMangledName("foo", foo);
    ASSERT_TRUE(retrieved.empty()) << "Unregistered declaration should return empty string";
}

// ============================================================================
// Test 13: Has Overloads Check
// ============================================================================

TEST_F(OverloadRegistryTest, HasOverloadsCheck) {
    const char *code = R"(
        void foo(int x);
        void bar(int x);
        void bar(double x);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    OverloadRegistry& registry = OverloadRegistry::getInstance();

    // Register functions
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            std::string name = FD->getNameAsString();
            QualType paramType = FD->getParamDecl(0)->getType();
            std::string mangledName;

            if (paramType->isIntegerType()) {
                mangledName = name + "_int";
            } else if (paramType->isFloatingType()) {
                mangledName = name + "_double";
            }

            registry.registerOverload(name, FD, mangledName);
        }
    }

    // foo has only one overload
    ASSERT_FALSE(registry.hasMultipleOverloads("foo")) << "foo should not have multiple overloads";

    // bar has multiple overloads
    ASSERT_TRUE(registry.hasMultipleOverloads("bar")) << "bar should have multiple overloads";

    // nonexistent has no overloads
    ASSERT_FALSE(registry.hasMultipleOverloads("nonexistent")) << "nonexistent should not have multiple overloads";
}

// ============================================================================
// Test 14: Count Overloads
// ============================================================================

TEST_F(OverloadRegistryTest, CountOverloads) {
    const char *code = R"(
        void foo(int x);
        void foo(double x);
        void foo(int x, int y);
    )";

    std::unique_ptr<ASTUnit> AST = buildAST(code);
    ASSERT_TRUE(AST) << "Failed to parse C++ code";

    OverloadRegistry& registry = OverloadRegistry::getInstance();
    std::string baseName = "foo";

    // Register all three overloads
    auto *TU = AST->getASTContext().getTranslationUnitDecl();
    for (auto *D : TU->decls()) {
        if (auto *FD = dyn_cast<FunctionDecl>(D)) {
            if (FD->getNameAsString() == "foo") {
                std::string mangledName;
                if (FD->getNumParams() == 1) {
                    QualType paramType = FD->getParamDecl(0)->getType();
                    if (paramType->isIntegerType()) {
                        mangledName = "foo_int";
                    } else if (paramType->isFloatingType()) {
                        mangledName = "foo_double";
                    }
                } else if (FD->getNumParams() == 2) {
                    mangledName = "foo_int_int";
                }
                registry.registerOverload(baseName, FD, mangledName);
            }
        }
    }

    // Count should return 3
    size_t count = registry.countOverloads(baseName);
    ASSERT_EQ(count, 3u) << "Expected 3 overloads for foo";

    // Non-existent should return 0
    ASSERT_EQ(registry.countOverloads("nonexistent"), 0u) << "Non-existent should have 0 overloads";
}

// ============================================================================
// Test 15: Thread Safety (Basic Check)
// ============================================================================

TEST_F(OverloadRegistryTest, SingletonThreadSafety) {
    // This is a basic check - full thread safety would require
    // multi-threaded test infrastructure

    // Multiple calls to getInstance() should return same instance
    OverloadRegistry& r1 = OverloadRegistry::getInstance();
    OverloadRegistry& r2 = OverloadRegistry::getInstance();
    OverloadRegistry& r3 = OverloadRegistry::getInstance();

    ASSERT_EQ(&r1, &r2) << "All getInstance() calls must return same instance";
    ASSERT_EQ(&r2, &r3) << "All getInstance() calls must return same instance";
    ASSERT_EQ(&r1, &r3) << "All getInstance() calls must return same instance";
}
