/**
 * @file ErrorHandlingTestFixture.h
 * @brief Shared test fixture for Error Handling test suite
 *
 * Provides common setup, helper functions, and utilities for all
 * error handling tests migrated to Google Test.
 */

#ifndef ERROR_HANDLING_TEST_FIXTURE_H
#define ERROR_HANDLING_TEST_FIXTURE_H

#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Basic/Diagnostic.h"
#include "clang/Basic/DiagnosticOptions.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <gtest/gtest.h>
#include <memory>
#include <string>
#include <vector>

using namespace clang;

/**
 * @brief Structure to hold AST parsing results with error information
 */
struct ParseResult {
    std::unique_ptr<ASTUnit> AST;
    bool hasErrors;
    std::string errorMessage;

    ParseResult() : hasErrors(false) {}
};

/**
 * @brief Base test fixture for Error Handling tests
 *
 * Provides common functionality:
 * - Building AST from C++ code with error detection
 * - Helpers for checking compilation errors
 * - Utilities for diagnosing error messages
 */
class ErrorHandlingTestFixture : public ::testing::Test {
protected:
    /**
     * @brief Try to create AST and capture errors
     * @param code C++ source code
     * @param std C++ standard (default: c++17)
     * @return ParseResult with AST and error information
     */
    ParseResult tryCreateAST(const std::string &code, const std::string &std = "c++17") {
        ParseResult result;
        std::vector<std::string> args = {"-std=" + std, "-Wno-unused-value"};

        // Create AST (may fail for invalid code)
        result.AST = clang::tooling::buildASTFromCodeWithArgs(code, args, "test.cpp");

        if (result.AST) {
            auto &Diags = result.AST->getDiagnostics();
            result.hasErrors = Diags.hasErrorOccurred();

            // Capture error messages if available
            if (result.hasErrors) {
                result.errorMessage = "Compilation errors occurred";
            }
        } else {
            result.hasErrors = true;
            result.errorMessage = "Failed to create AST";
        }

        return result;
    }

    /**
     * @brief Build AST from C++ code string (expects valid code)
     * @param code C++ source code
     * @return Unique pointer to ASTUnit
     */
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        return clang::tooling::buildASTFromCode(code);
    }

    /**
     * @brief Find a class by name in translation unit
     * @param TU Translation unit declaration
     * @param className Name of the class to find
     * @return Pointer to class or nullptr if not found
     */
    const CXXRecordDecl* findClassByName(const TranslationUnitDecl *TU, const std::string &className) {
        if (!TU) return nullptr;

        for (auto *D : TU->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == className && RD->isCompleteDefinition()) {
                    return RD;
                }
            }
        }
        return nullptr;
    }

    /**
     * @brief Find a function by name in translation unit
     * @param TU Translation unit declaration
     * @param functionName Name of the function to find
     * @return Pointer to function or nullptr if not found
     */
    const FunctionDecl* findFunctionByName(const TranslationUnitDecl *TU, const std::string &functionName) {
        if (!TU) return nullptr;

        for (auto *D : TU->decls()) {
            if (auto *FD = dyn_cast<FunctionDecl>(D)) {
                if (FD->getNameAsString() == functionName) {
                    return FD;
                }
            }
        }
        return nullptr;
    }

    /**
     * @brief Check if AST has compilation errors
     * @param AST The AST unit to check
     * @return true if there are errors
     */
    bool hasCompilationErrors(const std::unique_ptr<ASTUnit> &AST) {
        if (!AST) return true;
        return AST->getDiagnostics().hasErrorOccurred();
    }

    /**
     * @brief Check if a string contains a substring
     * @param str String to search
     * @param substr Substring to find
     * @return true if substring is found
     */
    bool contains(const std::string &str, const std::string &substr) {
        return str.find(substr) != std::string::npos;
    }
};

#endif // ERROR_HANDLING_TEST_FIXTURE_H
