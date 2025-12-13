// ActionTableGeneratorTest.cpp - Tests for action table generation (Story #77)
// Following TDD: Write failing tests first

#include "ActionTableGenerator.h"
#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>

using namespace clang;

// ============================================================================
// Test Suite: CFG Analysis of Try Blocks (AC #1)
// ============================================================================

void test_IdentifyObjectsInTryBlock() {
    std::cout << "Running test_IdentifyObjectsInTryBlock... ";

    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
                Resource r2;
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Find the function
    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "test") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'test' not found");

    // Analyze try block
    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    // Expected: 2 objects constructed in try block
    assert(generator.getTryBlockCount() == 1 && "Expected 1 try block");
    assert(generator.getObjectCount(0) == 2 && "Expected 2 objects in try block");

    std::cout << "✓" << std::endl;
}

void test_EmptyTryBlock() {
    std::cout << "Running test_EmptyTryBlock... ";

    const char *Code = R"(
        void test() {
            try {
                // Empty
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "test") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'test' not found");

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    // Expected: 0 objects in empty try block
    assert(generator.getTryBlockCount() == 1 && "Expected 1 try block");
    assert(generator.getObjectCount(0) == 0 && "Expected 0 objects in try block");

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite: Reverse Ordering (AC #2)
// ============================================================================

void test_ReverseDestructorOrder() {
    std::cout << "Running test_ReverseDestructorOrder... ";

    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
                Resource r2;
                Resource r3;
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "test") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'test' not found");

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    // Get destruction order (should be r3, r2, r1 - reverse of construction)
    auto destructors = generator.getDestructorSequence(0);
    assert(destructors.size() == 3 && "Expected 3 destructors");

    // Check names are in reverse order
    assert(destructors[0].find("r3") != std::string::npos && "First destructor should be r3");
    assert(destructors[1].find("r2") != std::string::npos && "Second destructor should be r2");
    assert(destructors[2].find("r1") != std::string::npos && "Third destructor should be r1");

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite: Action Entry Generation (AC #3)
// ============================================================================

void test_GenerateActionEntry() {
    std::cout << "Running test_GenerateActionEntry... ";

    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "test") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'test' not found");

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    // Generate action table code
    std::string actionTable = generator.generateActionTable(0);

    // Expected: action entry array definition
    assert(actionTable.find("struct __cxx_action_entry") != std::string::npos);
    assert(actionTable.find("actions_try") != std::string::npos);

    std::cout << "✓" << std::endl;
}

void test_ActionEntryStructure() {
    std::cout << "Running test_ActionEntryStructure... ";

    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "test") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'test' not found");

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    std::string actionTable = generator.generateActionTable(0);

    // Should contain destructor function pointer cast
    assert(actionTable.find("(void(*)(void*))") != std::string::npos);
    // Should contain NULL for object pointer (set at runtime)
    assert(actionTable.find("NULL") != std::string::npos);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite: Sentinel Entry (AC #5)
// ============================================================================

void test_SentinelEntry() {
    std::cout << "Running test_SentinelEntry... ";

    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "test") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'test' not found");

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    std::string actionTable = generator.generateActionTable(0);

    // Should contain sentinel entry {NULL, NULL}
    assert(actionTable.find("{NULL, NULL}") != std::string::npos);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite: Nested Try Blocks (AC #6)
// ============================================================================

void test_NestedTryBlocks() {
    std::cout << "Running test_NestedTryBlocks... ";

    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
                try {
                    Resource r2;
                } catch (...) {}
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "test") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'test' not found");

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    // Expected: 2 separate try blocks
    assert(generator.getTryBlockCount() == 2 && "Expected 2 try blocks");

    // Outer try block has r1
    assert(generator.getObjectCount(0) == 1 && "Outer try should have 1 object");

    // Inner try block has r2
    assert(generator.getObjectCount(1) == 1 && "Inner try should have 1 object");

    std::cout << "✓" << std::endl;
}

void test_SeparateActionTablesForNestedTry() {
    std::cout << "Running test_SeparateActionTablesForNestedTry... ";

    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
                try {
                    Resource r2;
                } catch (...) {}
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "test") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'test' not found");

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    // Generate both action tables
    std::string actionTable0 = generator.generateActionTable(0);
    std::string actionTable1 = generator.generateActionTable(1);

    // Should have different names
    assert(actionTable0.find("actions_try0") != std::string::npos);
    assert(actionTable1.find("actions_try1") != std::string::npos);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Test Suite: Runtime Address Binding (AC #4)
// ============================================================================

void test_RuntimeAddressBinding() {
    std::cout << "Running test_RuntimeAddressBinding... ";

    const char *Code = R"(
        class Resource {
        public:
            Resource();
            ~Resource();
        };

        void test() {
            try {
                Resource r1;
            } catch (...) {}
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "test") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'test' not found");

    ActionTableGenerator generator;
    generator.analyzeTryBlocks(FD);

    // Generate runtime binding code
    std::string bindingCode = generator.generateRuntimeBinding(0);

    // Should contain assignments to action table object pointers
    assert(bindingCode.find("actions_try") != std::string::npos);
    assert(bindingCode.find(".object = &") != std::string::npos);

    std::cout << "✓" << std::endl;
}

// ============================================================================
// Main
// ============================================================================

int main() {
    std::cout << "===================================" << std::endl;
    std::cout << "Action Table Generator Tests" << std::endl;
    std::cout << "Story #77" << std::endl;
    std::cout << "===================================" << std::endl;

    // CFG Analysis Tests (AC #1)
    test_IdentifyObjectsInTryBlock();
    test_EmptyTryBlock();

    // Reverse Ordering Tests (AC #2)
    test_ReverseDestructorOrder();

    // Action Entry Generation Tests (AC #3)
    test_GenerateActionEntry();
    test_ActionEntryStructure();

    // Sentinel Entry Tests (AC #5)
    test_SentinelEntry();

    // Nested Try Blocks Tests (AC #6)
    test_NestedTryBlocks();
    test_SeparateActionTablesForNestedTry();

    // Runtime Address Binding Tests (AC #4)
    test_RuntimeAddressBinding();

    std::cout << "===================================" << std::endl;
    std::cout << "All tests passed! ✓" << std::endl;
    std::cout << "===================================" << std::endl;

    return 0;
}
