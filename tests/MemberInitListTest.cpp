// TDD Tests for Member Initialization List Translation - Story #178
// Epic #7: Advanced Constructor/Destructor Features
//
// Acceptance Criteria:
// - Member init lists parsed from C++ constructors
// - Translated to C assignments in correct declaration order
// - Handles all basic types (int, double, char*, etc.)
// - Unit tests verify correct translation

#include "CppToCVisitor.h"
#include "CNodeBuilder.h"
#include "CodeGenerator.h"
#include "clang/AST/ASTContext.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include "llvm/Support/raw_ostream.h"
#include <memory>
#include <string>
#include <sstream>

using namespace clang;
using namespace llvm;

#define TEST_START(name) outs() << "\n=== Test: " << name << " ===\n"
#define TEST_PASS(name) outs() << "✓ PASS: " << name << "\n"
#define TEST_FAIL(name, reason) outs() << "✗ FAIL: " << name << " - " << reason << "\n"; return false

bool contains(const std::string &haystack, const std::string &needle) {
    return haystack.find(needle) != std::string::npos;
}

/**
 * Test Case 1: Basic Member Init List with Primitive Types
 *
 * C++ Input:
 *   class Vector {
 *       double x, y, z;
 *   public:
 *       Vector(double x, double y, double z) : x(x), y(y), z(z) {}
 *   };
 *
 * Expected C Output:
 *   void Vector__ctor(struct Vector *this, double x, double y, double z) {
 *       this->x = x;
 *       this->y = y;
 *       this->z = z;
 *   }
 *
 * Acceptance Criteria:
 * - Member init list parsed correctly
 * - Each member initialized with assignment
 * - Declaration order preserved (x, y, z)
 */
bool test_BasicMemberInitList() {
    TEST_START("BasicMemberInitList: Simple primitive member initialization");

    const char *cpp = R"(
        class Vector {
            double x, y, z;
        public:
            Vector(double x, double y, double z) : x(x), y(y), z(z) {}
        };
    )";

    auto AST = tooling::buildASTFromCode(cpp);
    if (!AST) {
        TEST_FAIL("BasicMemberInitList", "Failed to parse C++ code");
    }

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    // Get the generated constructor function
    FunctionDecl *CtorFunc = visitor.getCtor("Vector__ctor");
    if (!CtorFunc) {
        TEST_FAIL("BasicMemberInitList", "Constructor function not generated");
    }

    // Generate C code from the function
    std::string output;
    raw_string_ostream OS(output);
    CodeGenerator gen(OS, AST->getASTContext());
    gen.printDecl(CtorFunc);
    OS.flush();

    // Verify member assignments in correct order
    if (!contains(output, "this->x = x")) {
        TEST_FAIL("BasicMemberInitList", "Member x not initialized");
    }
    if (!contains(output, "this->y = y")) {
        TEST_FAIL("BasicMemberInitList", "Member y not initialized");
    }
    if (!contains(output, "this->z = z")) {
        TEST_FAIL("BasicMemberInitList", "Member z not initialized");
    }

    // Verify declaration order preserved (x before y before z)
    size_t x_pos = output.find("this->x = x");
    size_t y_pos = output.find("this->y = y");
    size_t z_pos = output.find("this->z = z");

    if (x_pos == std::string::npos || y_pos == std::string::npos || z_pos == std::string::npos) {
        TEST_FAIL("BasicMemberInitList", "Not all members found");
    }

    if (!(x_pos < y_pos && y_pos < z_pos)) {
        TEST_FAIL("BasicMemberInitList", "Declaration order not preserved");
    }

    TEST_PASS("BasicMemberInitList");
    return true;
}

/**
 * Test Case 2: Mixed Types Member Init List
 *
 * C++ Input:
 *   class Entity {
 *       int id;
 *       double health;
 *       char *name;
 *   public:
 *       Entity(int id, double health, char *name)
 *           : id(id), health(health), name(name) {}
 *   };
 *
 * Expected C Output:
 *   void Entity__ctor(struct Entity *this, int id, double health, char *name) {
 *       this->id = id;
 *       this->health = health;
 *       this->name = name;
 *   }
 *
 * Acceptance Criteria:
 * - Handles int, double, and pointer types
 * - All members initialized correctly
 */
bool test_MixedTypesMemberInitList() {
    TEST_START("MixedTypesMemberInitList: int, double, char* initialization");

    const char *cpp = R"(
        class Entity {
            int id;
            double health;
            char *name;
        public:
            Entity(int id, double health, char *name)
                : id(id), health(health), name(name) {}
        };
    )";

    auto AST = tooling::buildASTFromCode(cpp);
    if (!AST) {
        TEST_FAIL("MixedTypesMemberInitList", "Failed to parse C++ code");
    }

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CtorFunc = visitor.getCtor("Entity__ctor");
    if (!CtorFunc) {
        TEST_FAIL("MixedTypesMemberInitList", "Constructor function not generated");
    }

    std::string output;
    raw_string_ostream OS(output);
    CodeGenerator gen(OS, AST->getASTContext());
    gen.printDecl(CtorFunc);
    OS.flush();

    // Verify all three types initialized
    if (!contains(output, "this->id = id")) {
        TEST_FAIL("MixedTypesMemberInitList", "int member not initialized");
    }
    if (!contains(output, "this->health = health")) {
        TEST_FAIL("MixedTypesMemberInitList", "double member not initialized");
    }
    if (!contains(output, "this->name = name")) {
        TEST_FAIL("MixedTypesMemberInitList", "pointer member not initialized");
    }

    TEST_PASS("MixedTypesMemberInitList");
    return true;
}

/**
 * Test Case 3: Partial Member Init List
 *
 * C++ Input:
 *   class Particle {
 *       double x, y;
 *       int type;
 *   public:
 *       Particle(double x, double y) : x(x), y(y) {
 *           // type uninitialized in init list
 *       }
 *   };
 *
 * Expected C Output:
 *   void Particle__ctor(struct Particle *this, double x, double y) {
 *       this->x = x;
 *       this->y = y;
 *       // type not initialized (no assignment)
 *   }
 *
 * Acceptance Criteria:
 * - Only initialized members get assignments
 * - Uninitialized members are skipped
 */
bool test_PartialMemberInitList() {
    TEST_START("PartialMemberInitList: Only some members initialized");

    const char *cpp = R"(
        class Particle {
            double x, y;
            int type;
        public:
            Particle(double x, double y) : x(x), y(y) {}
        };
    )";

    auto AST = tooling::buildASTFromCode(cpp);
    if (!AST) {
        TEST_FAIL("PartialMemberInitList", "Failed to parse C++ code");
    }

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CtorFunc = visitor.getCtor("Particle__ctor");
    if (!CtorFunc) {
        TEST_FAIL("PartialMemberInitList", "Constructor function not generated");
    }

    std::string output;
    raw_string_ostream OS(output);
    CodeGenerator gen(OS, AST->getASTContext());
    gen.printDecl(CtorFunc);
    OS.flush();

    // Verify initialized members
    if (!contains(output, "this->x = x")) {
        TEST_FAIL("PartialMemberInitList", "Member x not initialized");
    }
    if (!contains(output, "this->y = y")) {
        TEST_FAIL("PartialMemberInitList", "Member y not initialized");
    }

    // Verify type is NOT initialized (should not have assignment)
    // Note: We check that if "type" appears, it's only in the struct, not in assignment
    size_t type_assign = output.find("this->type =");
    if (type_assign != std::string::npos) {
        TEST_FAIL("PartialMemberInitList", "Uninitialized member 'type' should not have assignment");
    }

    TEST_PASS("PartialMemberInitList");
    return true;
}

/**
 * Test Case 4: Member Init List with Constant Values
 *
 * C++ Input:
 *   class Config {
 *       int version;
 *       bool enabled;
 *   public:
 *       Config() : version(1), enabled(true) {}
 *   };
 *
 * Expected C Output:
 *   void Config__ctor_default(struct Config *this) {
 *       this->version = 1;
 *       this->enabled = 1;  // true -> 1
 *   }
 *
 * Acceptance Criteria:
 * - Constant values translated correctly
 * - bool true/false converted to 1/0
 */
bool test_MemberInitListWithConstants() {
    TEST_START("MemberInitListWithConstants: Constant value initialization");

    const char *cpp = R"(
        class Config {
            int version;
            bool enabled;
        public:
            Config() : version(1), enabled(true) {}
        };
    )";

    auto AST = tooling::buildASTFromCode(cpp);
    if (!AST) {
        TEST_FAIL("MemberInitListWithConstants", "Failed to parse C++ code");
    }

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CtorFunc = visitor.getCtor("Config__ctor");
    if (!CtorFunc) {
        TEST_FAIL("MemberInitListWithConstants", "Constructor function not generated");
    }

    std::string output;
    raw_string_ostream OS(output);
    CodeGenerator gen(OS, AST->getASTContext());
    gen.printDecl(CtorFunc);
    OS.flush();

    // Verify constant initialization
    if (!contains(output, "this->version = 1")) {
        TEST_FAIL("MemberInitListWithConstants", "version not initialized to 1");
    }

    // Check for boolean (could be 1 or true depending on translation)
    if (!contains(output, "this->enabled = ")) {
        TEST_FAIL("MemberInitListWithConstants", "enabled not initialized");
    }

    TEST_PASS("MemberInitListWithConstants");
    return true;
}

/**
 * Test Case 5: Declaration Order Verification
 *
 * C++ Input:
 *   class Test {
 *       int a, b, c;
 *   public:
 *       Test() : c(3), a(1), b(2) {}  // Init list order: c, a, b
 *   };
 *
 * Expected C Output (declaration order a, b, c):
 *   void Test__ctor_default(struct Test *this) {
 *       this->a = 1;  // Despite c being first in init list
 *       this->b = 2;
 *       this->c = 3;
 *   }
 *
 * Acceptance Criteria:
 * - Members initialized in DECLARATION order
 * - NOT in init list order
 */
bool test_DeclarationOrderPreserved() {
    TEST_START("DeclarationOrderPreserved: Init order follows declaration, not init list");

    const char *cpp = R"(
        class Test {
            int a, b, c;
        public:
            Test() : c(3), a(1), b(2) {}
        };
    )";

    auto AST = tooling::buildASTFromCode(cpp);
    if (!AST) {
        TEST_FAIL("DeclarationOrderPreserved", "Failed to parse C++ code");
    }

    CNodeBuilder builder(AST->getASTContext());
    CppToCVisitor visitor(AST->getASTContext(), builder);
    visitor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());

    FunctionDecl *CtorFunc = visitor.getCtor("Test__ctor");
    if (!CtorFunc) {
        TEST_FAIL("DeclarationOrderPreserved", "Constructor function not generated");
    }

    std::string output;
    raw_string_ostream OS(output);
    CodeGenerator gen(OS, AST->getASTContext());
    gen.printDecl(CtorFunc);
    OS.flush();

    // Verify all members initialized
    if (!contains(output, "this->a = 1") ||
        !contains(output, "this->b = 2") ||
        !contains(output, "this->c = 3")) {
        TEST_FAIL("DeclarationOrderPreserved", "Not all members initialized");
    }

    // Verify order: a before b before c
    size_t a_pos = output.find("this->a = 1");
    size_t b_pos = output.find("this->b = 2");
    size_t c_pos = output.find("this->c = 3");

    if (!(a_pos < b_pos && b_pos < c_pos)) {
        TEST_FAIL("DeclarationOrderPreserved",
                  "Members not in declaration order (should be a, b, c)");
    }

    TEST_PASS("DeclarationOrderPreserved");
    return true;
}

// Test runner
int main() {
    outs() << "\n";
    outs() << "========================================\n";
    outs() << "Story #178: Member Initialization List Translation Tests\n";
    outs() << "Epic #7: Advanced Constructor/Destructor Features\n";
    outs() << "========================================\n";

    int passed = 0;
    int total = 5;

    if (test_BasicMemberInitList()) passed++;
    if (test_MixedTypesMemberInitList()) passed++;
    if (test_PartialMemberInitList()) passed++;
    if (test_MemberInitListWithConstants()) passed++;
    if (test_DeclarationOrderPreserved()) passed++;

    outs() << "\n========================================\n";
    outs() << "Results: " << passed << "/" << total << " tests passed\n";

    if (passed == total) {
        outs() << "✓ ALL TESTS PASSED\n";
    } else {
        outs() << "✗ SOME TESTS FAILED\n";
    }
    outs() << "========================================\n\n";

    return (passed == total) ? 0 : 1;
}
