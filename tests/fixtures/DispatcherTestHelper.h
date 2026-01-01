/**
 * @file DispatcherTestHelper.h
 * @brief Helper functions for tests using CppToCVisitorDispatcher pattern
 *
 * Provides utility functions to set up dispatcher-based tests without requiring
 * a heavy test fixture. Tests can use these helpers directly.
 *
 * Usage Pattern:
 * @code
 * // In test:
 * auto [cppAST, cAST, dispatcher] = cpptoc::test::createDispatcherPipeline();
 *
 * // Register handlers
 * cpptoc::RecordHandler::registerWith(*dispatcher);
 * cpptoc::FunctionHandler::registerWith(*dispatcher);
 *
 * // Dispatch declarations
 * for (auto* decl : cppAST->getASTContext().getTranslationUnitDecl()->decls()) {
 *     dispatcher->dispatch(cppAST->getASTContext(), cAST->getASTContext(),
 *                         const_cast<clang::Decl*>(decl));
 * }
 *
 * // Generate C code
 * std::string cCode = cpptoc::test::generateCCode(cAST->getASTContext());
 * @endcode
 */

#pragma once

#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/PathMapper.h"
#include "mapping/DeclLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "mapping/ExprMapper.h"
#include "mapping/StmtMapper.h"
#include "CodeGenerator.h"
#include "clang/Tooling/Tooling.h"
#include <memory>
#include <string>
#include <tuple>
#include <fstream>
#include <iostream>
#include <cstdlib>

namespace cpptoc {
namespace test {

/**
 * @brief Pipeline components for dispatcher-based tests
 */
struct DispatcherPipeline {
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    // PathMapper is a singleton - store reference
    PathMapper* pathMapper;
    std::unique_ptr<DeclLocationMapper> declLocationMapper;
    std::unique_ptr<DeclMapper> declMapper;
    std::unique_ptr<TypeMapper> typeMapper;
    std::unique_ptr<ExprMapper> exprMapper;
    std::unique_ptr<StmtMapper> stmtMapper;
    std::unique_ptr<CppToCVisitorDispatcher> dispatcher;
};

/**
 * @brief Create a complete dispatcher pipeline for testing
 * @param cppCode C++ source code to parse
 * @return Pipeline with all components initialized
 *
 * Creates:
 * - C++ AST from source code
 * - C AST (empty context)
 * - All mappers
 * - Initialized dispatcher
 *
 * Usage:
 * @code
 * auto pipeline = cpptoc::test::createDispatcherPipeline("int main() { return 0; }");
 * // Register handlers...
 * // Dispatch declarations...
 * @endcode
 */
inline DispatcherPipeline createDispatcherPipeline(const std::string& cppCode = "int dummy;") {
    DispatcherPipeline pipeline;

    // CRITICAL: Reset PathMapper singleton state for test isolation
    // PathMapper is a singleton and retains state across tests
    PathMapper::reset();

    // Parse C++ code
    pipeline.cppAST = clang::tooling::buildASTFromCode(cppCode);
    if (!pipeline.cppAST) {
        throw std::runtime_error("Failed to parse C++ code");
    }

    // Create C context
    pipeline.cAST = clang::tooling::buildASTFromCode("int dummy;");
    if (!pipeline.cAST) {
        throw std::runtime_error("Failed to create C context");
    }

    // Create mappers
    // Get singleton PathMapper instance
    pipeline.pathMapper = &PathMapper::getInstance("/tmp/test_source", "/tmp/test_output");
    pipeline.declLocationMapper = std::make_unique<DeclLocationMapper>(*pipeline.pathMapper);
    pipeline.declMapper = std::make_unique<DeclMapper>();
    pipeline.typeMapper = std::make_unique<TypeMapper>();
    pipeline.exprMapper = std::make_unique<ExprMapper>();
    pipeline.stmtMapper = std::make_unique<StmtMapper>();

    // Create dispatcher with all mappers
    pipeline.dispatcher = std::make_unique<CppToCVisitorDispatcher>(
        *pipeline.pathMapper,
        *pipeline.declLocationMapper,
        *pipeline.declMapper,
        *pipeline.typeMapper,
        *pipeline.exprMapper,
        *pipeline.stmtMapper
    );

    return pipeline;
}

/**
 * @brief Generate C code from C AST using PathMapper (for dispatcher-based tests)
 * @param cASTContext C ASTContext
 * @param pathMapper PathMapper with all generated TUs
 * @return Generated C code as string
 *
 * This version iterates through all TUs created by PathMapper and prints them.
 * Use this for dispatcher-based tests where handlers create separate TUs per file.
 */
inline std::string generateCCode(clang::ASTContext& cASTContext, PathMapper& pathMapper) {
    std::string cCode;
    llvm::raw_string_ostream codeStream(cCode);
    CodeGenerator generator(codeStream, cASTContext);

    // Get all target files from PathMapper
    std::vector<std::string> targetFiles = pathMapper.getAllTargetFiles();

    // Print all TUs created by PathMapper (skip <stdin>.c - it's just the dummy TU)
    for (const auto& targetPath : targetFiles) {
        // Skip the dummy <stdin>.c TU (created when we initialized C ASTContext)
        if (targetPath.find("<stdin>") != std::string::npos) {
            continue;
        }

        llvm::outs() << "[DispatcherTestHelper] About to print TU for: " << targetPath << "\n";
        clang::TranslationUnitDecl* TU = pathMapper.getOrCreateTU(targetPath);
        if (TU) {
            llvm::outs() << "[DispatcherTestHelper] TU has " << std::distance(TU->decls_begin(), TU->decls_end()) << " decls\n";
            generator.printTranslationUnit(TU);
            llvm::outs() << "[DispatcherTestHelper] Finished printing TU\n";
        }
    }

    codeStream.flush();
    llvm::outs() << "[DispatcherTestHelper] Code generation complete\n";
    return cCode;
}

/**
 * @brief Generate C code from C AST (legacy version for non-dispatcher tests)
 * @param cASTContext C ASTContext
 * @return Generated C code as string
 */
inline std::string generateCCode(clang::ASTContext& cASTContext) {
    std::string cCode;
    llvm::raw_string_ostream codeStream(cCode);
    CodeGenerator generator(codeStream, cASTContext);
    generator.printTranslationUnit(cASTContext.getTranslationUnitDecl());
    codeStream.flush();
    return cCode;
}

/**
 * @brief Compile and run C code, return exit code
 * @param cCode C source code
 * @param testName Test name for temporary file
 * @return Exit code from execution, or -1 if compilation failed
 */
inline int compileAndRun(const std::string& cCode, const std::string& testName = "test") {
    // Write C code to temporary file
    std::string tmpFile = "/tmp/cpptoc_" + testName + "_" + std::to_string(rand()) + ".c";
    std::ofstream outFile(tmpFile);
    outFile << cCode;
    outFile.close();

    // Compile with gcc
    std::string compileCmd = "gcc -std=c99 " + tmpFile + " -o " + tmpFile + ".out 2>&1";
    int compileResult = system(compileCmd.c_str());
    if (compileResult != 0) {
        std::cerr << "Compilation failed for:\n" << cCode << "\n";
        system(("cat " + tmpFile).c_str());
        system(("rm -f " + tmpFile).c_str());
        return -1;
    }

    // Execute
    std::string execCmd = tmpFile + ".out";
    int execResult = system(execCmd.c_str());
    int actualExitCode = WEXITSTATUS(execResult);

    // Cleanup
    system(("rm -f " + tmpFile + " " + tmpFile + ".out").c_str());

    return actualExitCode;
}

} // namespace test
} // namespace cpptoc
