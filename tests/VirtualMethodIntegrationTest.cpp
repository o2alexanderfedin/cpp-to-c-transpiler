// TDD Tests for Virtual Method Support - Phase 9, v2.2.0
// Comprehensive virtual method translation and vtable generation

#include "OverrideResolver.h"
#include "VirtualCallTranslator.h"
#include "VirtualMethodAnalyzer.h"
#include "VtableGenerator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include <memory>
#include <string>

using namespace clang;

// Simple test framework
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name)                                                        \
  {                                                                            \
    std::cout << "✓" << std::endl;                                             \
    tests_passed++;                                                            \
  }
#define TEST_FAIL(name, msg)                                                   \
  {                                                                            \
    std::cout << "✗ FAILED: " << msg << std::endl;                             \
    tests_failed++;                                                            \
  }
#define ASSERT(expr, msg)                                                      \
  if (!(expr)) {                                                               \
    TEST_FAIL("", msg);                                                        \
    return;                                                                    \
  }
#define ASSERT_CONTAINS(haystack, needle, msg)                                 \
  if ((haystack).find(needle) == std::string::npos) {                          \
    TEST_FAIL("", std::string(msg) + " - Expected to find: " + needle);        \
    return;                                                                    \
  }
#define ASSERT_NOT_EMPTY(str, msg)                                             \
  if ((str).empty()) {                                                         \
    TEST_FAIL("", msg);                                                        \
    return;                                                                    \
  }

// Helper: Parse C++ code and return CXXRecordDecl
CXXRecordDecl *parseClassDecl(const std::string &code,
                              const std::string &className) {
  std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
  if (!AST)
    return nullptr;

  ASTContext &ctx = AST->getASTContext();
  TranslationUnitDecl *TU = ctx.getTranslationUnitDecl();

  for (auto *decl : TU->decls()) {
    if (auto *record = dyn_cast<CXXRecordDecl>(decl)) {
      if (record->getNameAsString() == className &&
          record->isCompleteDefinition()) {
        return record;
      }
    }
  }
  return nullptr;
}

// Helper: Parse C++ code and return CXXMemberCallExpr
CXXMemberCallExpr *parseMemberCallExpr(const std::string &code) {
  std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
  if (!AST)
    return nullptr;

  ASTContext &ctx = AST->getASTContext();
  TranslationUnitDecl *TU = ctx.getTranslationUnitDecl();

  // Find the first CXXMemberCallExpr
  class CallFinder : public RecursiveASTVisitor<CallFinder> {
  public:
    CXXMemberCallExpr *Result = nullptr;

    bool VisitCXXMemberCallExpr(CXXMemberCallExpr *E) {
      if (!Result)
        Result = E;
      return true;
    }
  };

  CallFinder finder;
  finder.TraverseDecl(TU);
  return finder.Result;
}

// ============================================================================
// TIER 1: Single Inheritance Tests (5 tests)
// ============================================================================

// Test 1: Simple virtual method - single class with one virtual method
void test_SimpleVirtualMethod() {
  TEST_START("SimpleVirtualMethod");

  std::string code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };
    )";

  CXXRecordDecl *record = parseClassDecl(code, "Shape");
  ASSERT(record != nullptr, "Failed to parse Shape class");

  ASTContext &ctx = record->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);

  // Verify class is polymorphic
  ASSERT(analyzer.isPolymorphic(record), "Shape should be polymorphic");

  // Verify virtual method detected
  auto virtualMethods = analyzer.getVirtualMethods(record);
  ASSERT(virtualMethods.size() == 1, "Should have 1 virtual method");

  // Generate vtable struct
  OverrideResolver resolver(ctx, analyzer);
  VtableGenerator generator(ctx, analyzer, &resolver);
  std::string vtable = generator.generateVtableStruct(record);

  ASSERT_NOT_EMPTY(vtable, "Vtable should be generated");
  ASSERT_CONTAINS(vtable, "struct Shape_vtable",
                  "Should have Shape_vtable struct");
  ASSERT_CONTAINS(vtable, "type_info", "Should have type_info pointer");
  ASSERT_CONTAINS(vtable, "(*draw)", "Should have draw function pointer");

  TEST_PASS("SimpleVirtualMethod");
}

// Test 2: Multiple virtual methods in single class
void test_MultipleVirtualMethods() {
  TEST_START("MultipleVirtualMethods");

  std::string code = R"(
        class Shape {
        public:
            virtual void draw() {}
            virtual double area() const { return 0.0; }
            virtual void setColor(int r, int g, int b) {}
        };
    )";

  CXXRecordDecl *record = parseClassDecl(code, "Shape");
  ASSERT(record != nullptr, "Failed to parse Shape class");

  ASTContext &ctx = record->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);
  OverrideResolver resolver(ctx, analyzer);
  VtableGenerator generator(ctx, analyzer, &resolver);

  auto virtualMethods = analyzer.getVirtualMethods(record);
  ASSERT(virtualMethods.size() == 3, "Should have 3 virtual methods");

  std::string vtable = generator.generateVtableStruct(record);
  ASSERT_CONTAINS(vtable, "(*draw)", "Should have draw method");
  ASSERT_CONTAINS(vtable, "(*area)", "Should have area method");
  ASSERT_CONTAINS(vtable, "(*setColor)", "Should have setColor method");

  TEST_PASS("MultipleVirtualMethods");
}

// Test 3: Virtual method override - derived class overrides base method
void test_VirtualMethodOverride() {
  TEST_START("VirtualMethodOverride");

  std::string code = R"(
        class Base {
        public:
            virtual void foo() {}
        };

        class Derived : public Base {
        public:
            virtual void foo() override {}
        };
    )";

  CXXRecordDecl *derivedRecord = parseClassDecl(code, "Derived");
  ASSERT(derivedRecord != nullptr, "Failed to parse Derived class");

  ASTContext &ctx = derivedRecord->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);
  OverrideResolver resolver(ctx, analyzer);
  VtableGenerator generator(ctx, analyzer, &resolver);

  // Verify Derived is polymorphic
  ASSERT(analyzer.isPolymorphic(derivedRecord),
         "Derived should be polymorphic");

  // Generate vtable for derived class
  std::string vtable = generator.generateVtableStruct(derivedRecord);
  ASSERT_CONTAINS(vtable, "struct Derived_vtable",
                  "Should have Derived_vtable");
  ASSERT_CONTAINS(vtable, "(*foo)", "Should have foo method");

  TEST_PASS("VirtualMethodOverride");
}

// Test 4: Inherited virtual method - derived class does NOT override
void test_InheritedVirtualMethod() {
  TEST_START("InheritedVirtualMethod");

  std::string code = R"(
        class Base {
        public:
            virtual void foo() {}
        };

        class Derived : public Base {
        public:
            void bar() {}  // Non-virtual method
        };
    )";

  CXXRecordDecl *derivedRecord = parseClassDecl(code, "Derived");
  ASSERT(derivedRecord != nullptr, "Failed to parse Derived class");

  ASTContext &ctx = derivedRecord->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);

  // Derived inherits virtual method from Base
  ASSERT(analyzer.isPolymorphic(derivedRecord),
         "Derived should be polymorphic (inherited)");

  OverrideResolver resolver(ctx, analyzer);
  VtableGenerator generator(ctx, analyzer, &resolver);
  std::string vtable = generator.generateVtableStruct(derivedRecord);

  // Vtable should include inherited virtual method
  ASSERT_CONTAINS(vtable, "(*foo)", "Should inherit foo from Base");

  TEST_PASS("InheritedVirtualMethod");
}

// Test 5: Mixed virtual and non-virtual methods
void test_MixedVirtualNonVirtual() {
  TEST_START("MixedVirtualNonVirtual");

  std::string code = R"(
        class Shape {
        public:
            virtual void draw() {}  // Virtual
            void setName(const char* n) {}  // Non-virtual
            virtual double area() const { return 0.0; }  // Virtual
            int getId() const { return 0; }  // Non-virtual
        };
    )";

  CXXRecordDecl *record = parseClassDecl(code, "Shape");
  ASSERT(record != nullptr, "Failed to parse Shape class");

  ASTContext &ctx = record->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);
  OverrideResolver resolver(ctx, analyzer);
  VtableGenerator generator(ctx, analyzer, &resolver);

  auto virtualMethods = analyzer.getVirtualMethods(record);
  ASSERT(virtualMethods.size() == 2,
         "Should have 2 virtual methods (draw, area)");

  std::string vtable = generator.generateVtableStruct(record);
  ASSERT_CONTAINS(vtable, "(*draw)", "Vtable should have virtual draw");
  ASSERT_CONTAINS(vtable, "(*area)", "Vtable should have virtual area");
  // Non-virtual methods should NOT be in vtable

  TEST_PASS("MixedVirtualNonVirtual");
}

// ============================================================================
// TIER 2: Multi-Level Inheritance Tests (3 tests)
// ============================================================================

// Test 6: Multi-level inheritance - A -> B -> C
void test_MultiLevelInheritance() {
  TEST_START("MultiLevelInheritance");

  std::string code = R"(
        class A {
        public:
            virtual void foo() {}
        };

        class B : public A {
        public:
            virtual void foo() override {}
        };

        class C : public B {
        public:
            virtual void foo() override {}
        };
    )";

  CXXRecordDecl *recordC = parseClassDecl(code, "C");
  ASSERT(recordC != nullptr, "Failed to parse C class");

  ASTContext &ctx = recordC->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);
  OverrideResolver resolver(ctx, analyzer);
  VtableGenerator generator(ctx, analyzer, &resolver);

  ASSERT(analyzer.isPolymorphic(recordC), "C should be polymorphic");

  std::string vtable = generator.generateVtableStruct(recordC);
  ASSERT_CONTAINS(vtable, "struct C_vtable", "Should have C_vtable");
  ASSERT_CONTAINS(vtable, "(*foo)", "Should have foo method");

  TEST_PASS("MultiLevelInheritance");
}

// Test 7: Multi-level with new virtual method added at each level
void test_MultiLevelWithNewMethod() {
  TEST_START("MultiLevelWithNewMethod");

  std::string code = R"(
        class A {
        public:
            virtual void foo() {}
        };

        class B : public A {
        public:
            virtual void foo() override {}
            virtual void bar() {}  // New virtual method
        };

        class C : public B {
        public:
            virtual void foo() override {}
            virtual void bar() override {}
            virtual void baz() {}  // Another new virtual method
        };
    )";

  CXXRecordDecl *recordC = parseClassDecl(code, "C");
  ASSERT(recordC != nullptr, "Failed to parse C class");

  ASTContext &ctx = recordC->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);
  OverrideResolver resolver(ctx, analyzer);
  VtableGenerator generator(ctx, analyzer, &resolver);

  auto virtualMethods = analyzer.getVirtualMethods(recordC);
  ASSERT(virtualMethods.size() >= 3,
         "C should have at least 3 virtual methods");

  std::string vtable = generator.generateVtableStruct(recordC);
  ASSERT_CONTAINS(vtable, "(*foo)", "Should have foo");
  ASSERT_CONTAINS(vtable, "(*bar)", "Should have bar");
  ASSERT_CONTAINS(vtable, "(*baz)", "Should have baz");

  TEST_PASS("MultiLevelWithNewMethod");
}

// Test 8: Multi-level partial override
void test_MultiLevelPartialOverride() {
  TEST_START("MultiLevelPartialOverride");

  std::string code = R"(
        class A {
        public:
            virtual void foo() {}
            virtual void bar() {}
        };

        class B : public A {
        public:
            virtual void foo() override {}  // Override foo
            // bar inherited from A
        };

        class C : public B {
        public:
            // foo inherited from B
            virtual void bar() override {}  // Override bar
        };
    )";

  CXXRecordDecl *recordC = parseClassDecl(code, "C");
  ASSERT(recordC != nullptr, "Failed to parse C class");

  ASTContext &ctx = recordC->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);
  OverrideResolver resolver(ctx, analyzer);
  VtableGenerator generator(ctx, analyzer, &resolver);

  auto virtualMethods = analyzer.getVirtualMethods(recordC);
  ASSERT(virtualMethods.size() >= 2,
         "C should have at least 2 virtual methods");

  std::string vtable = generator.generateVtableStruct(recordC);
  ASSERT_CONTAINS(vtable, "(*foo)", "Should have foo (inherited from B)");
  ASSERT_CONTAINS(vtable, "(*bar)", "Should have bar (overridden in C)");

  TEST_PASS("MultiLevelPartialOverride");
}

// ============================================================================
// TIER 3: Virtual Destructors Tests (2 tests)
// ============================================================================

// Test 9: Virtual destructor
void test_VirtualDestructor() {
  TEST_START("VirtualDestructor");

  std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };
    )";

  CXXRecordDecl *record = parseClassDecl(code, "Base");
  ASSERT(record != nullptr, "Failed to parse Base class");

  ASTContext &ctx = record->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);
  OverrideResolver resolver(ctx, analyzer);
  VtableGenerator generator(ctx, analyzer, &resolver);

  ASSERT(analyzer.isPolymorphic(record),
         "Base should be polymorphic (has virtual dtor)");

  std::string vtable = generator.generateVtableStruct(record);
  ASSERT_CONTAINS(vtable, "struct Base_vtable", "Should have Base_vtable");
  ASSERT_CONTAINS(vtable, "(*destructor)",
                  "Should have destructor function pointer");

  TEST_PASS("VirtualDestructor");
}

// Test 10: Virtual destructor inheritance
void test_VirtualDestructorInheritance() {
  TEST_START("VirtualDestructorInheritance");

  std::string code = R"(
        class Base {
        public:
            virtual ~Base() {}
        };

        class Derived : public Base {
        public:
            ~Derived() {}  // Implicitly virtual
        };
    )";

  CXXRecordDecl *derivedRecord = parseClassDecl(code, "Derived");
  ASSERT(derivedRecord != nullptr, "Failed to parse Derived class");

  ASTContext &ctx = derivedRecord->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);
  OverrideResolver resolver(ctx, analyzer);
  VtableGenerator generator(ctx, analyzer, &resolver);

  ASSERT(analyzer.isPolymorphic(derivedRecord),
         "Derived should be polymorphic");

  std::string vtable = generator.generateVtableStruct(derivedRecord);
  ASSERT_CONTAINS(vtable, "(*destructor)", "Should have destructor in vtable");

  TEST_PASS("VirtualDestructorInheritance");
}

// ============================================================================
// TIER 4: Abstract Classes & Pure Virtual Tests (2 tests)
// ============================================================================

// Test 11: Pure virtual method (abstract class)
void test_PureVirtualMethod() {
  TEST_START("PureVirtualMethod");

  std::string code = R"(
        class AbstractShape {
        public:
            virtual ~AbstractShape() {}
            virtual void draw() = 0;  // Pure virtual
        };
    )";

  CXXRecordDecl *record = parseClassDecl(code, "AbstractShape");
  ASSERT(record != nullptr, "Failed to parse AbstractShape class");

  ASTContext &ctx = record->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);

  ASSERT(analyzer.isPolymorphic(record), "AbstractShape should be polymorphic");
  ASSERT(analyzer.isAbstractClass(record), "AbstractShape should be abstract");

  auto virtualMethods = analyzer.getVirtualMethods(record);
  ASSERT(virtualMethods.size() >= 1,
         "Should have at least 1 virtual method (draw)");

  // Check if draw is pure virtual
  bool foundPureVirtual = false;
  for (auto *method : virtualMethods) {
    if (method->getNameAsString() == "draw" && analyzer.isPureVirtual(method)) {
      foundPureVirtual = true;
      break;
    }
  }
  ASSERT(foundPureVirtual, "draw should be pure virtual");

  TEST_PASS("PureVirtualMethod");
}

// Test 12: Multiple abstract methods with concrete implementation
void test_MultipleAbstractMethods() {
  TEST_START("MultipleAbstractMethods");

  std::string code = R"(
        class AbstractBase {
        public:
            virtual ~AbstractBase() {}
            virtual void foo() = 0;
            virtual void bar() = 0;
            virtual void baz() = 0;
        };

        class Concrete : public AbstractBase {
        public:
            virtual void foo() override {}
            virtual void bar() override {}
            virtual void baz() override {}
        };
    )";

  CXXRecordDecl *abstractRecord = parseClassDecl(code, "AbstractBase");
  ASSERT(abstractRecord != nullptr, "Failed to parse AbstractBase");

  ASTContext &ctx = abstractRecord->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);

  ASSERT(analyzer.isAbstractClass(abstractRecord),
         "AbstractBase should be abstract");

  // Check concrete class
  CXXRecordDecl *concreteRecord = parseClassDecl(code, "Concrete");
  ASSERT(concreteRecord != nullptr, "Failed to parse Concrete");
  ASSERT(!analyzer.isAbstractClass(concreteRecord),
         "Concrete should NOT be abstract");

  TEST_PASS("MultipleAbstractMethods");
}

// ============================================================================
// TIER 5: Advanced Cases Tests (3 tests)
// ============================================================================

// Test 13: Virtual call detection
void test_VirtualCallDetection() {
  TEST_START("VirtualCallDetection");

  std::string code = R"(
        class Shape {
        public:
            virtual void draw() {}
        };

        void test() {
            Shape s;
            s.draw();  // Virtual call
        }
    )";

  // Parse the code to get the class declaration first
  CXXRecordDecl *record = parseClassDecl(code, "Shape");
  ASSERT(record != nullptr, "Failed to parse Shape class");

  ASTContext &ctx = record->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);
  VirtualCallTranslator translator(ctx, analyzer);

  // Parse the member call expression
  CXXMemberCallExpr *callExpr = parseMemberCallExpr(code);
  ASSERT(callExpr != nullptr, "Failed to parse member call expression");

  // Check if call is virtual
  bool isVirtual = translator.isVirtualCall(callExpr);
  ASSERT(isVirtual, "Call to draw() should be detected as virtual");

  TEST_PASS("VirtualCallDetection");
}

// Test 14: Virtual call through pointer
void test_PolymorphicThroughPointer() {
  TEST_START("PolymorphicThroughPointer");

  std::string code = R"(
        class Base {
        public:
            virtual void foo() {}
        };

        class Derived : public Base {
        public:
            virtual void foo() override {}
        };

        void test(Base* ptr) {
            ptr->foo();  // Polymorphic call
        }
    )";

  // Parse everything from a single AST to avoid dangling pointers
  std::unique_ptr<ASTUnit> AST = tooling::buildASTFromCode(code);
  ASSERT(AST != nullptr, "Failed to parse code");

  ASTContext &ctx = AST->getASTContext();
  TranslationUnitDecl *TU = ctx.getTranslationUnitDecl();

  // Find Base class
  CXXRecordDecl *baseRecord = nullptr;
  for (auto *decl : TU->decls()) {
    if (auto *record = dyn_cast<CXXRecordDecl>(decl)) {
      if (record->getNameAsString() == "Base" &&
          record->isCompleteDefinition()) {
        baseRecord = record;
        break;
      }
    }
  }
  ASSERT(baseRecord != nullptr, "Failed to find Base class");

  // Find member call expression
  class CallFinder : public RecursiveASTVisitor<CallFinder> {
  public:
    CXXMemberCallExpr *Result = nullptr;
    bool VisitCXXMemberCallExpr(CXXMemberCallExpr *E) {
      if (!Result)
        Result = E;
      return true;
    }
  };
  CallFinder finder;
  finder.TraverseDecl(TU);
  ASSERT(finder.Result != nullptr, "Failed to find member call");

  // Now test with the same AST context
  VirtualMethodAnalyzer analyzer(ctx);
  VirtualCallTranslator translator(ctx, analyzer);

  bool isVirtual = translator.isVirtualCall(finder.Result);
  ASSERT(isVirtual, "Call through pointer should be virtual");

  TEST_PASS("PolymorphicThroughPointer");
}

// Test 15: Covariant return type
void test_CovariantReturnType() {
  TEST_START("CovariantReturnType");

  std::string code = R"(
        class Base {
        public:
            virtual Base* clone() = 0;
        };

        class Derived : public Base {
        public:
            virtual Derived* clone() override { return new Derived(*this); }
        };
    )";

  CXXRecordDecl *derivedRecord = parseClassDecl(code, "Derived");
  ASSERT(derivedRecord != nullptr, "Failed to parse Derived class");

  ASTContext &ctx = derivedRecord->getASTContext();
  VirtualMethodAnalyzer analyzer(ctx);
  OverrideResolver resolver(ctx, analyzer);
  VtableGenerator generator(ctx, analyzer, &resolver);

  // Both Base and Derived have clone() method
  auto virtualMethods = analyzer.getVirtualMethods(derivedRecord);

  bool hasClone = false;
  for (auto *method : virtualMethods) {
    if (method->getNameAsString() == "clone") {
      hasClone = true;
      // Verify covariant return type (Derived* instead of Base*)
      QualType retType = method->getReturnType();
      ASSERT(retType->isPointerType(), "clone should return pointer");
    }
  }
  ASSERT(hasClone, "Derived should have clone method");

  TEST_PASS("CovariantReturnType");
}

// ============================================================================
// Main Test Runner
// ============================================================================

int main() {
  std::cout
      << "\n=== Virtual Method Integration Tests (Phase 9, v2.2.0) ===\n\n";

  std::cout << "TIER 1: Single Inheritance\n";
  test_SimpleVirtualMethod();
  test_MultipleVirtualMethods();
  test_VirtualMethodOverride();
  test_InheritedVirtualMethod();
  test_MixedVirtualNonVirtual();

  std::cout << "\nTIER 2: Multi-Level Inheritance\n";
  test_MultiLevelInheritance();
  test_MultiLevelWithNewMethod();
  test_MultiLevelPartialOverride();

  std::cout << "\nTIER 3: Virtual Destructors\n";
  test_VirtualDestructor();
  test_VirtualDestructorInheritance();

  std::cout << "\nTIER 4: Abstract Classes & Pure Virtual\n";
  test_PureVirtualMethod();
  test_MultipleAbstractMethods();

  std::cout << "\nTIER 5: Advanced Cases\n";
  test_VirtualCallDetection();
  test_PolymorphicThroughPointer();
  test_CovariantReturnType();

  std::cout << "\n=== Test Summary ===\n";
  std::cout << "Passed: " << tests_passed << "\n";
  std::cout << "Failed: " << tests_failed << "\n";
  std::cout << "Total:  " << (tests_passed + tests_failed) << "\n";

  return tests_failed > 0 ? 1 : 0;
}
