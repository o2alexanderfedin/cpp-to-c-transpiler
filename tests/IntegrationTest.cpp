// Integration Tests for Epic #19 - Header File Generation
// Story #142: Integration Testing
// Migrated to Google Test

#include "HeaderSeparator.h"
#include "IncludeGuardGenerator.h"
#include "DependencyAnalyzer.h"
#include "FileOutputManager.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <iostream>
#include <fstream>
#include <cstdio>

using namespace clang;

// Test 1: HeaderSeparator + IncludeGuardGenerator integration
TEST(IntegrationTest, HeaderSeparationWithGuards) {
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
    EXPECT_EQ(separator.getHeaderDecls().size(), 2)
        << "Expected 2 header declarations (struct + function)";
    EXPECT_NE(guardBegin.find("#ifndef POINT_H"), std::string::npos)
        << "Expected include guard in output";
    EXPECT_NE(guardEnd.find("#endif"), std::string::npos)
        << "Expected #endif in output";
}

// Test 2: HeaderSeparator + Forward Declarations integration
TEST(IntegrationTest, SeparationWithForwardDecls) {
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

    EXPECT_EQ(separator.getHeaderDecls().size(), 1)
        << "Expected 1 header declaration";
    EXPECT_EQ(forwardDecls.count("Node"), 1)
        << "Expected forward declaration for Node";
}

// Test 3: DependencyAnalyzer + IncludeGuardGenerator integration
TEST(IntegrationTest, DependenciesWithGuards) {
    DependencyAnalyzer depAnalyzer("Example.h");
    IncludeGuardGenerator guardGen;

    std::string guardName = guardGen.generateGuardName("Example.h");
    std::string includes = depAnalyzer.emitIncludes();

    // Verify both work together
    EXPECT_EQ(guardName, "EXAMPLE_H")
        << "Expected correct guard name";
    EXPECT_NE(includes.find("#include \"Example.h\""), std::string::npos)
        << "Expected own header in includes";
}

// Test 4: FileOutputManager actual file creation
TEST(IntegrationTest, ActualFileCreation) {
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

    ASSERT_TRUE(success) << "Expected file writing to succeed";

    // Verify files exist
    std::ifstream headerFile("TestIntegration.h");
    std::ifstream implFile("TestIntegration.c");

    EXPECT_TRUE(headerFile.good()) << "Expected header file to exist";
    EXPECT_TRUE(implFile.good()) << "Expected impl file to exist";

    headerFile.close();
    implFile.close();

    // Cleanup
    std::remove("TestIntegration.h");
    std::remove("TestIntegration.c");
}

// Test 5: End-to-end scenario
TEST(IntegrationTest, EndToEndScenario) {
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
    EXPECT_GE(separator.getHeaderDecls().size(), 1)
        << "Expected header declarations";
    EXPECT_GE(separator.getImplDecls().size(), 1)
        << "Expected impl declarations";
    EXPECT_NE(guardBegin.find("#ifndef CALCULATOR_H"), std::string::npos)
        << "Expected correct guard";
    EXPECT_EQ(depAnalyzer.getRequiredIncludes().size(), 1)
        << "Expected one include (own header)";
    EXPECT_EQ(fileManager.getHeaderFilename(), "Calculator.h")
        << "Expected correct header filename";
    EXPECT_EQ(fileManager.getImplFilename(), "Calculator.c")
        << "Expected correct impl filename";
}
