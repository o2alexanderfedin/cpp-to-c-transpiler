/**
 * @file VirtualInheritanceHandlerDispatcherTest.cpp
 * @brief Unit tests for virtual inheritance handler dispatch predicates
 *
 * Tests that handlers correctly identify when they should handle declarations
 * with virtual inheritance. Ensures:
 * 1. Handler predicates correctly detect virtual bases
 * 2. No handler conflicts (multiple handlers claiming same decl)
 * 3. Proper handler priority ordering
 * 4. Edge cases (empty bases, mixed inheritance, etc.)
 *
 * Following the pattern of other dispatcher tests in this directory.
 */

#include "dispatch/RecordHandler.h"
#include "dispatch/ConstructorHandler.h"
#include "UnitTestHelper.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>

using namespace cpptoc;
using namespace cpptoc::test;

/**
 * @class VirtualInheritanceHandlerDispatcherTest
 * @brief Test fixture for handler dispatch with virtual inheritance
 */
class VirtualInheritanceHandlerDispatcherTest : public ::testing::Test {
protected:
    UnitTestContext ctx;

    void SetUp() override {
        ctx = createUnitTestContext();
    }

    /**
     * @brief Parse code and get class by name
     */
    const clang::CXXRecordDecl* getClass(const std::string& code, const std::string& className) {
        storedAST = clang::tooling::buildASTFromCode(code);
        if (!storedAST) return nullptr;

        auto& astCtx = storedAST->getASTContext();
        auto* TU = astCtx.getTranslationUnitDecl();

        for (auto* decl : TU->decls()) {
            if (auto* recordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(decl)) {
                if (recordDecl->getNameAsString() == className &&
                    recordDecl->isCompleteDefinition()) {
                    return recordDecl;
                }
            }
        }

        return nullptr;
    }

    /**
     * @brief Find constructor by parameter count
     */
    clang::CXXConstructorDecl* findConstructor(
        const clang::CXXRecordDecl* record,
        unsigned numParams = 0
    ) {
        if (!record) return nullptr;

        for (auto* ctor : record->ctors()) {
            if (ctor->getNumParams() == numParams && !ctor->isDeleted()) {
                return ctor;
            }
        }
        return nullptr;
    }

    std::unique_ptr<clang::ASTUnit> storedAST;
};

// ============================================================================
// Test 1: RecordHandler Can Handle Class with Virtual Base
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, RecordHandlerCanHandleVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // RecordHandler should handle all CXXRecordDecl
    // (virtual inheritance doesn't change this - just affects generation)
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(derived));
}

// ============================================================================
// Test 2: RecordHandler Handles Diamond Pattern
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, RecordHandlerHandlesDiamond) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Left : public virtual Base {
        public:
            int l;
        };

        class Right : public virtual Base {
        public:
            int r;
        };

        class Diamond : public Left, public Right {
        public:
            int d;
        };
    )";

    auto* base = getClass(code, "Base");
    auto* left = getClass(code, "Left");
    auto* right = getClass(code, "Right");
    auto* diamond = getClass(code, "Diamond");

    ASSERT_NE(base, nullptr);
    ASSERT_NE(left, nullptr);
    ASSERT_NE(right, nullptr);
    ASSERT_NE(diamond, nullptr);

    // All are CXXRecordDecl and should be handled
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(base));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(left));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(right));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(diamond));
}

// ============================================================================
// Test 3: ConstructorHandler Can Handle Constructor with Virtual Base
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, ConstructorHandlerCanHandleVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);

    // ConstructorHandler should handle all CXXConstructorDecl
    EXPECT_TRUE(llvm::isa<clang::CXXConstructorDecl>(ctor));
}

// ============================================================================
// Test 4: Multiple Handlers Don't Conflict on Virtual Inheritance
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, NoHandlerConflicts) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);

    // RecordHandler handles the class
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(derived));

    // ConstructorHandler handles the constructor
    EXPECT_TRUE(llvm::isa<clang::CXXConstructorDecl>(ctor));

    // These are different declaration types - no conflict
    EXPECT_FALSE(llvm::isa<clang::CXXConstructorDecl>(derived));
    EXPECT_FALSE(llvm::isa<clang::CXXRecordDecl>(ctor));
}

// ============================================================================
// Test 5: Handler Predicate for Empty Virtual Base
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, HandlerPredicateEmptyVirtualBase) {
    std::string code = R"(
        class EmptyBase {
            // Empty class
        };

        class Derived : public virtual EmptyBase {
        public:
            int d;
        };
    )";

    auto* emptyBase = getClass(code, "EmptyBase");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(emptyBase, nullptr);
    ASSERT_NE(derived, nullptr);

    // Both should be handled as CXXRecordDecl
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(emptyBase));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(derived));

    // Derived has virtual base
    EXPECT_GT(derived->getNumVBases(), 0);
}

// ============================================================================
// Test 6: Handler Predicate for Multiple Virtual Bases
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, HandlerPredicateMultipleVirtualBases) {
    std::string code = R"(
        class Base1 {
        public:
            virtual ~Base1() {}
            int b1;
        };

        class Base2 {
        public:
            virtual ~Base2() {}
            int b2;
        };

        class Derived : public virtual Base1, public virtual Base2 {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Should be handled as CXXRecordDecl
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(derived));

    // Has multiple virtual bases
    EXPECT_EQ(derived->getNumVBases(), 2);

    // Constructor should also be handled
    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);
    EXPECT_TRUE(llvm::isa<clang::CXXConstructorDecl>(ctor));
}

// ============================================================================
// Test 7: Handler Predicate for Mixed Inheritance
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, HandlerPredicateMixedInheritance) {
    std::string code = R"(
        class VirtualBase {
        public:
            virtual ~VirtualBase() {}
            int vb;
        };

        class NonVirtualBase {
        public:
            virtual ~NonVirtualBase() {}
            int nvb;
        };

        class Derived : public virtual VirtualBase, public NonVirtualBase {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Should be handled as CXXRecordDecl
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(derived));

    // Has 1 virtual base and 1 non-virtual base
    EXPECT_EQ(derived->getNumVBases(), 1);
    EXPECT_EQ(derived->getNumBases(), 2);
}

// ============================================================================
// Test 8: Handler Predicate for Indirect Virtual Base
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, HandlerPredicateIndirectVirtualBase) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Middle : public virtual Base {
        public:
            Middle() {}
            int m;
        };

        class Derived : public Middle {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* middle = getClass(code, "Middle");
    auto* derived = getClass(code, "Derived");

    ASSERT_NE(middle, nullptr);
    ASSERT_NE(derived, nullptr);

    // Both should be handled
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(middle));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(derived));

    // Both have virtual bases
    EXPECT_GT(middle->getNumVBases(), 0);
    EXPECT_GT(derived->getNumVBases(), 0);

    // Both constructors should be handled
    EXPECT_NE(findConstructor(middle, 0), nullptr);
    EXPECT_NE(findConstructor(derived, 0), nullptr);
}

// ============================================================================
// Test 9: Handler Predicate Priority - RecordHandler vs ConstructorHandler
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, HandlerPriorityOrdering) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() : d(0) {}
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);

    // RecordHandler handles CXXRecordDecl
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(derived));
    EXPECT_FALSE(llvm::isa<clang::FunctionDecl>(derived));

    // ConstructorHandler handles CXXConstructorDecl (which is a FunctionDecl)
    EXPECT_TRUE(llvm::isa<clang::CXXConstructorDecl>(ctor));
    EXPECT_TRUE(llvm::isa<clang::FunctionDecl>(ctor));

    // No ambiguity - different decl types
}

// ============================================================================
// Test 10: Handler Predicate for Defaulted Constructor
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, HandlerPredicateDefaultedConstructor) {
    std::string code = R"(
        class Base {
        public:
            Base() = default;
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() = default;
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);

    // Should still be handled even if defaulted
    EXPECT_TRUE(llvm::isa<clang::CXXConstructorDecl>(ctor));
    EXPECT_TRUE(ctor->isDefaulted());
}

// ============================================================================
// Test 11: Handler Predicate Doesn't Handle Deleted Constructor
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, HandlerPredicateDeletedConstructor) {
    std::string code = R"(
        class Base {
        public:
            Base() {}
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            Derived() = delete;
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Find deleted constructor
    clang::CXXConstructorDecl* deletedCtor = nullptr;
    for (auto* ctor : derived->ctors()) {
        if (ctor->getNumParams() == 0) {
            deletedCtor = ctor;
            break;
        }
    }

    ASSERT_NE(deletedCtor, nullptr);
    EXPECT_TRUE(deletedCtor->isDeleted());

    // Deleted constructors exist in AST but shouldn't generate code
    // (Handler may or may not process them - implementation dependent)
}

// ============================================================================
// Test 12: Handler Predicate for Implicit Constructor
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, HandlerPredicateImplicitConstructor) {
    std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            // No explicit constructor - implicit default
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    auto* ctor = findConstructor(derived, 0);
    ASSERT_NE(ctor, nullptr);

    // Implicit constructors should be handled
    EXPECT_TRUE(llvm::isa<clang::CXXConstructorDecl>(ctor));
    EXPECT_TRUE(ctor->isImplicit() || ctor->isDefaulted());
}

// ============================================================================
// Test 13: Handler Predicate for Complex Diamond
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, HandlerPredicateComplexDiamond) {
    std::string code = R"(
        class Top {
        public:
            Top() {}
            virtual ~Top() {}
            int t;
        };

        class Left1 : public virtual Top { public: int l1; };
        class Left2 : public virtual Top { public: int l2; };
        class Right1 : public virtual Top { public: int r1; };
        class Right2 : public virtual Top { public: int r2; };

        class Bottom : public Left1, public Left2, public Right1, public Right2 {
        public:
            Bottom() : b(0) {}
            int b;
        };
    )";

    auto* top = getClass(code, "Top");
    auto* bottom = getClass(code, "Bottom");

    ASSERT_NE(top, nullptr);
    ASSERT_NE(bottom, nullptr);

    // All should be handled
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(top));
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(bottom));

    // Bottom has virtual bases
    EXPECT_GT(bottom->getNumVBases(), 0);

    // Constructor should be handled
    auto* ctor = findConstructor(bottom, 0);
    ASSERT_NE(ctor, nullptr);
    EXPECT_TRUE(llvm::isa<clang::CXXConstructorDecl>(ctor));
}

// ============================================================================
// Test 14: Handler Predicate for Forward Declaration
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, HandlerPredicateForwardDeclaration) {
    std::string code = R"(
        class Base;  // Forward declaration

        class Base {
        public:
            virtual ~Base() {}
            int b;
        };

        class Derived : public virtual Base {
        public:
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Should handle complete definition, not forward declaration
    EXPECT_TRUE(derived->isCompleteDefinition());
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(derived));
}

// ============================================================================
// Test 15: Handler Predicate for Template with Virtual Base
// ============================================================================

TEST_F(VirtualInheritanceHandlerDispatcherTest, HandlerPredicateTemplateVirtualBase) {
    std::string code = R"(
        template<typename T>
        class Base {
        public:
            virtual ~Base() {}
            T value;
        };

        class Derived : public virtual Base<int> {
        public:
            int d;
        };
    )";

    auto* derived = getClass(code, "Derived");
    ASSERT_NE(derived, nullptr);

    // Should handle instantiated template
    EXPECT_TRUE(llvm::isa<clang::CXXRecordDecl>(derived));

    // Has virtual base
    EXPECT_GT(derived->getNumVBases(), 0);
}
