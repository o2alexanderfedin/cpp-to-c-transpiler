// Integration Tests for Epic #19 - Header File Generation
// Story #142: Integration Testing

#include "HeaderSeparator.h"
#include "IncludeGuardGenerator.h"
#include "DependencyAnalyzer.h"
#include "FileOutputManager.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>
#include <fstream>
#include <cstdio>

using namespace clang;

// Simple test counter
static int tests_passed = 0;
static int tests_failed = 0;

#define TEST_START(name) std::cout << "Running " << name << "... ";
#define TEST_PASS(name) { std::cout << "✓" << std::endl; tests_passed++; }
#define TEST_FAIL(name, msg) { std::cout << "✗ FAILED: " << msg << std::endl; tests_failed++; }
#define ASSERT(expr, msg) if (!(expr)) { TEST_FAIL("", msg); return; }

// Test 1: HeaderSeparator + IncludeGuardGenerator integration
void test_HeaderSeparationWithGuards() {
    TEST_START("HeaderSeparationWithGuards");

    const char *Code = R"(
        struct Point {
            int x, y;
        };

        void printPoint(struct Point *p);
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Separate headers
    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // Generate guards
    IncludeGuardGenerator guardGen;
    std::string guardName = guardGen.generateGuardName("Point.h");
    std::string guardBegin = guardGen.emitGuardBegin(guardName);
    std::string guardEnd = guardGen.emitGuardEnd(guardName);

    // Verify integration
    ASSERT(separator.getHeaderDecls().size() == 2,
           "Expected 2 header declarations (struct + function)");
    ASSERT(guardBegin.find("#ifndef POINT_H") != std::string::npos,
           "Expected include guard in output");
    ASSERT(guardEnd.find("#endif") != std::string::npos,
           "Expected #endif in output");

    TEST_PASS("HeaderSeparationWithGuards");
}

// Test 2: HeaderSeparator + Forward Declarations integration
void test_SeparationWithForwardDecls() {
    TEST_START("SeparationWithForwardDecls");

    const char *Code = R"(
        struct Node {
            int data;
            struct Node *next;
        };
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // Check forward declarations detected
    auto forwardDecls = separator.getForwardDecls();

    ASSERT(separator.getHeaderDecls().size() == 1,
           "Expected 1 header declaration");
    ASSERT(forwardDecls.count("Node") == 1,
           "Expected forward declaration for Node");

    TEST_PASS("SeparationWithForwardDecls");
}

// Test 3: DependencyAnalyzer + IncludeGuardGenerator integration
void test_DependenciesWithGuards() {
    TEST_START("DependenciesWithGuards");

    DependencyAnalyzer depAnalyzer("Example.h");
    IncludeGuardGenerator guardGen;

    std::string guardName = guardGen.generateGuardName("Example.h");
    std::string includes = depAnalyzer.emitIncludes();

    // Verify both work together
    ASSERT(guardName == "EXAMPLE_H",
           "Expected correct guard name");
    ASSERT(includes.find("#include \"Example.h\"") != std::string::npos,
           "Expected own header in includes");

    TEST_PASS("DependenciesWithGuards");
}

// Test 4: FileOutputManager actual file creation
void test_ActualFileCreation() {
    TEST_START("ActualFileCreation");

    FileOutputManager fileManager;
    fileManager.setInputFilename("TestIntegration.cpp");

    IncludeGuardGenerator guardGen;
    std::string guardName = guardGen.generateGuardName("TestIntegration.h");
    std::string guardBegin = guardGen.emitGuardBegin(guardName);
    std::string guardEnd = guardGen.emitGuardEnd(guardName);

    DependencyAnalyzer depAnalyzer("TestIntegration.h");
    std::string includes = depAnalyzer.emitIncludes();

    // Create header content
    std::string headerContent = guardBegin;
    headerContent += "\nstruct TestIntegration { int x; };\n\n";
    headerContent += guardEnd;

    // Create impl content
    std::string implContent = includes;
    implContent += "\nint testFunction() { return 42; }\n";

    bool success = fileManager.writeFiles(headerContent, implContent);

    ASSERT(success, "Expected file writing to succeed");

    // Verify files exist
    std::ifstream headerFile("TestIntegration.h");
    std::ifstream implFile("TestIntegration.c");

    ASSERT(headerFile.good(), "Expected header file to exist");
    ASSERT(implFile.good(), "Expected impl file to exist");

    headerFile.close();
    implFile.close();

    // Cleanup
    std::remove("TestIntegration.h");
    std::remove("TestIntegration.c");

    TEST_PASS("ActualFileCreation");
}

// Test 5: End-to-end scenario
void test_EndToEndScenario() {
    TEST_START("EndToEndScenario");

    const char *Code = R"(
        struct Calculator {
            int add(int a, int b);
            int subtract(int a, int b);
        };

        int Calculator::add(int a, int b) { return a + b; }
        int Calculator::subtract(int a, int b) { return a - b; }
    )";

    auto AST = clang::tooling::buildASTFromCode(Code);
    auto *TU = AST->getASTContext().getTranslationUnitDecl();

    // Step 1: Analyze and separate
    HeaderSeparator separator;
    separator.analyzeTranslationUnit(TU);

    // Step 2: Generate guards
    IncludeGuardGenerator guardGen;
    std::string guardName = guardGen.generateGuardName("Calculator.h");
    std::string guardBegin = guardGen.emitGuardBegin(guardName);
    std::string guardEnd = guardGen.emitGuardEnd(guardName);

    // Step 3: Track dependencies
    DependencyAnalyzer depAnalyzer("Calculator.h");

    // Step 4: Setup file manager
    FileOutputManager fileManager;
    fileManager.setInputFilename("Calculator.cpp");

    // Verify all components work
    ASSERT(separator.getHeaderDecls().size() >= 1,
           "Expected header declarations");
    ASSERT(separator.getImplDecls().size() >= 1,
           "Expected impl declarations");
    ASSERT(guardBegin.find("#ifndef CALCULATOR_H") != std::string::npos,
           "Expected correct guard");
    ASSERT(depAnalyzer.getRequiredIncludes().size() == 1,
           "Expected one include (own header)");
    ASSERT(fileManager.getHeaderFilename() == "Calculator.h",
           "Expected correct header filename");
    ASSERT(fileManager.getImplFilename() == "Calculator.c",
           "Expected correct impl filename");

    TEST_PASS("EndToEndScenario");
}

int main() {
    std::cout << "\n=== Integration Tests (Story #142) ===\n\n";

    // Run all tests
    test_HeaderSeparationWithGuards();
    test_SeparationWithForwardDecls();
    test_DependenciesWithGuards();
    test_ActualFileCreation();
    test_EndToEndScenario();

    // Summary
    std::cout << "\n=== Test Summary ===\n";
    std::cout << "Passed: " << tests_passed << "\n";
    std::cout << "Failed: " << tests_failed << "\n";

    return tests_failed > 0 ? 1 : 0;
}
