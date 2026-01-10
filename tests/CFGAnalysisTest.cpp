// tests/CFGAnalysisTest.cpp
// Story #151: CFG (Control Flow Graph) Analysis Infrastructure
// Test-Driven Development: RED phase - Write failing tests first

#include "CFGAnalyzer.h"
#include "clang/Tooling/Tooling.h"
#include <cassert>
#include <iostream>

using namespace clang;

// Test 1: CFG detects all return statements
void test_CFGDetectsAllReturns() {
    std::cout << "Running test_CFGDetectsAllReturns... ";

    const char *Code = R"(
        void func(int flag) {
            int x = 10;
            if (flag) {
                return;  // Early return
            }
            int y = 20;
            return;  // Normal return
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Find the function
    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "func") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'func' not found");

    // Build CFG and analyze
    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: 2 exit points (2 return statements)
    assert(analyzer.getExitPointCount() == 2 && "Expected 2 exit points");

    std::cout << "✓" << std::endl;
}

// Test 2: CFG tracks local variable declarations
void test_CFGTracksLocalVars() {
    std::cout << "Running test_CFGTracksLocalVars... ";

    const char *Code = R"(
        void func() {
            int x = 10;
            int y = 20;
            float z = 3.14f;
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "func") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'func' not found");

    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: 3 local variables
    assert(analyzer.getLocalVarCount() == 3 && "Expected 3 local variables");

    std::cout << "✓" << std::endl;
}

// Test 3: CFG identifies nested scopes
void test_CFGIdentifiesNestedScopes() {
    std::cout << "Running test_CFGIdentifiesNestedScopes... ";

    const char *Code = R"(
        void func() {
            int x = 10;
            {
                int y = 20;
                {
                    int z = 30;
                }
            }
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "func") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'func' not found");

    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: 3 scopes (function body + 2 nested compound statements)
    assert(analyzer.getScopeCount() == 3 && "Expected 3 scopes");

    std::cout << "✓" << std::endl;
}

// Test 4: CFG detects break/continue statements
void test_CFGDetectsBreakContinue() {
    std::cout << "Running test_CFGDetectsBreakContinue... ";

    const char *Code = R"(
        void func(int count) {
            for (int i = 0; i < count; ++i) {
                if (i == 5) break;
                if (i == 3) continue;
            }
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "func") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'func' not found");

    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: CFG should detect break and continue
    assert(analyzer.getBreakContinueCount() == 2 && "Expected 2 break/continue statements");

    std::cout << "✓" << std::endl;
}

// Test 5: CFG detects goto statements
void test_CFGDetectsGoto() {
    std::cout << "Running test_CFGDetectsGoto... ";

    const char *Code = R"(
        void func(int flag) {
            int x = 10;
            int y;
            if (flag) {
                goto cleanup;
            }
            y = 20;
        cleanup:
            return;
        }
    )";

    auto AST = tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    FunctionDecl *FD = nullptr;
    for (auto *D : TU->decls()) {
        if (auto *Func = llvm::dyn_cast<FunctionDecl>(D)) {
            if (Func->getNameAsString() == "func") {
                FD = Func;
                break;
            }
        }
    }
    assert(FD && "Function 'func' not found");

    CFGAnalyzer analyzer;
    analyzer.analyzeCFG(FD);

    // Expected: CFG should detect goto
    assert(analyzer.getGotoCount() == 1 && "Expected 1 goto statement");

    std::cout << "✓" << std::endl;
}

int main() {
    std::cout << "\n=== CFG Analysis Tests (Story #151) ===\n\n";

    test_CFGDetectsAllReturns();
    test_CFGTracksLocalVars();
    test_CFGIdentifiesNestedScopes();
    test_CFGDetectsBreakContinue();
    test_CFGDetectsGoto();

    std::cout << "\n=== All Tests Passed ===\n";
    return 0;
}
