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
#include "TargetContext.h"
#include "clang/Tooling/Tooling.h"
#include <memory>
#include <string>
#include <tuple>
#include <fstream>
#include <iostream>
#include <cstdlib>
#include <thread>
#include <chrono>
#include <sstream>
#include <unistd.h>  // For getpid()

namespace cpptoc {
namespace test {

/**
 * @brief Pipeline components for dispatcher-based tests
 *
 * Uses RAII pattern: each test gets its own mapper instances
 * for complete test isolation. Mappers are automatically
 * cleaned up when pipeline goes out of scope.
 */
struct DispatcherPipeline {
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;

    // RAII: Own TargetContext instance (no singleton!)
    // Must be declared BEFORE mappers since they may depend on it
    // Each test gets its own isolated TargetContext
    std::unique_ptr<TargetContext> targetContext;

    // RAII: Own all mapper instances (no singletons!)
    // Each test gets its own isolated set of mappers
    std::unique_ptr<PathMapper> pathMapper;
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

    // RAII: Create TargetContext FIRST (before mappers that may depend on it)
    // Each test gets completely isolated TargetContext
    // No singleton, no shared state, no race conditions!
    pipeline.targetContext = std::make_unique<TargetContext>();

    // RAII: Create fresh mapper instances for THIS TEST ONLY
    // Each test gets completely isolated mapper state
    // No singletons, no shared state, no race conditions!
    // Pass TargetContext via dependency injection
    pipeline.pathMapper = std::make_unique<PathMapper>(*pipeline.targetContext, "/tmp/test_source", "/tmp/test_output");
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
        *pipeline.stmtMapper,
        *pipeline.targetContext
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

    // Print all TUs created by PathMapper
    // Note: We used to skip <stdin>.c assuming it was just the dummy TU,
    // but after fixing TranslationUnitHandler, actual code may be in <stdin>.c
    for (const auto& targetPath : targetFiles) {
        llvm::outs() << "[DispatcherTestHelper] About to print TU for: " << targetPath << "\n";
        clang::TranslationUnitDecl* TU = pathMapper.getOrCreateTU(targetPath);
        if (TU) {
            llvm::outs() << "[DispatcherTestHelper] TU has " << std::distance(TU->decls_begin(), TU->decls_end()) << " decls\n";

            // Only print if TU has declarations (skip empty dummy TUs)
            if (std::distance(TU->decls_begin(), TU->decls_end()) > 0) {
                generator.printTranslationUnit(TU);
                llvm::outs() << "[DispatcherTestHelper] Finished printing TU\n";
            } else {
                llvm::outs() << "[DispatcherTestHelper] Skipping empty TU\n";
            }
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
    // Write C code to temporary file with thread-safe unique name
    // Use thread ID + timestamp + process ID for guaranteed uniqueness in parallel execution
    std::ostringstream oss;
    oss << "/tmp/cpptoc_" << testName << "_"
        << std::this_thread::get_id() << "_"
        << std::chrono::high_resolution_clock::now().time_since_epoch().count() << "_"
        << getpid() << ".c";
    std::string tmpFile = oss.str();
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
