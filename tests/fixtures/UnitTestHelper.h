/**
 * @file UnitTestHelper.h
 * @brief Lightweight helper for unit tests using dispatcher pattern
 *
 * Provides simplified setup for unit tests that need to test individual handlers
 * without the full E2E pipeline overhead. Based on DispatcherTestHelper but streamlined
 * for unit test needs.
 *
 * Usage Pattern:
 * @code
 * // In unit test:
 * auto ctx = cpptoc::test::createUnitTestContext("int main() { return 0; }");
 *
 * // Register specific handler(s) under test
 * cpptoc::FunctionHandler::registerWith(*ctx.dispatcher);
 *
 * // Find and dispatch specific AST nodes
 * auto* funcDecl = findFirstFunction(ctx.cppAST->getASTContext());
 * ctx.dispatcher->dispatch(ctx.cppAST->getASTContext(),
 *                          ctx.cAST->getASTContext(),
 *                          funcDecl);
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
#include "mapping/FieldOffsetMapper.h"
#include "TargetContext.h"
#include "CodeGenerator.h"
#include "clang/Tooling/Tooling.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <memory>
#include <string>

namespace cpptoc {
namespace test {

/**
 * @brief Lightweight context for unit tests
 *
 * Contains minimal components needed for testing individual handlers.
 * Simpler than DispatcherPipeline for focused unit tests.
 */
struct UnitTestContext {
    std::unique_ptr<clang::ASTUnit> cppAST;
    std::unique_ptr<clang::ASTUnit> cAST;
    // Target context for C AST creation (must be declared before PathMapper)
    std::unique_ptr<TargetContext> targetContext;
    // All mappers use RAII pattern
    std::unique_ptr<PathMapper> pathMapper;
    std::unique_ptr<DeclLocationMapper> declLocationMapper;
    std::unique_ptr<DeclMapper> declMapper;
    std::unique_ptr<TypeMapper> typeMapper;
    std::unique_ptr<ExprMapper> exprMapper;
    std::unique_ptr<StmtMapper> stmtMapper;
    std::unique_ptr<FieldOffsetMapper> fieldOffsetMapper;
    std::unique_ptr<CppToCVisitorDispatcher> dispatcher;
};

/**
 * @brief Create a unit test context with dispatcher
 * @param cppCode C++ source code to parse
 * @return Context with all components initialized
 *
 * Creates lightweight context for unit tests:
 * - C++ AST from source code
 * - C AST (empty context)
 * - All mappers
 * - Initialized dispatcher (no handlers registered)
 *
 * Usage:
 * @code
 * auto ctx = cpptoc::test::createUnitTestContext("class Foo {};");
 * cpptoc::RecordHandler::registerWith(*ctx.dispatcher);
 * // ... test handler behavior
 * @endcode
 */
inline UnitTestContext createUnitTestContext(const std::string& cppCode = "int dummy;") {
    UnitTestContext ctx;

    // Parse C++ code
    ctx.cppAST = clang::tooling::buildASTFromCode(cppCode);
    if (!ctx.cppAST) {
        throw std::runtime_error("Failed to parse C++ code: " + cppCode);
    }

    // Create C context
    ctx.cAST = clang::tooling::buildASTFromCode("int dummy;");
    if (!ctx.cAST) {
        throw std::runtime_error("Failed to create C context");
    }

    // Create target context for C AST creation (MUST be created before PathMapper)
    ctx.targetContext = std::make_unique<TargetContext>();

    // Create mappers using RAII pattern
    ctx.pathMapper = std::make_unique<PathMapper>(*ctx.targetContext, "/tmp/test_source", "/tmp/test_output");
    ctx.declLocationMapper = std::make_unique<DeclLocationMapper>(*ctx.pathMapper);
    ctx.declMapper = std::make_unique<DeclMapper>();
    ctx.typeMapper = std::make_unique<TypeMapper>();
    ctx.exprMapper = std::make_unique<ExprMapper>();
    ctx.stmtMapper = std::make_unique<StmtMapper>();
    ctx.fieldOffsetMapper = std::make_unique<FieldOffsetMapper>();

    // Create dispatcher (no handlers registered yet)
    ctx.dispatcher = std::make_unique<CppToCVisitorDispatcher>(
        *ctx.pathMapper,
        *ctx.declLocationMapper,
        *ctx.declMapper,
        *ctx.typeMapper,
        *ctx.exprMapper,
        *ctx.stmtMapper,
        *ctx.fieldOffsetMapper,
        *ctx.targetContext
    );

    return ctx;
}

// ============================================================================
// AST Node Finder Helpers
// ============================================================================

/**
 * @brief Find first node of type T in AST
 * @tparam T AST node type (e.g., clang::FunctionDecl)
 * @param ctx ASTContext to search
 * @return First node of type T, or nullptr if not found
 */
template <typename T>
class FirstNodeFinder : public clang::RecursiveASTVisitor<FirstNodeFinder<T>> {
public:
    T* result = nullptr;

    bool VisitDecl(clang::Decl* D) {
        if (!result) {
            // Only try to cast if T is derived from Decl
            if constexpr (std::is_base_of<clang::Decl, T>::value) {
                if (auto* Node = llvm::dyn_cast<T>(D)) {
                    result = Node;
                    return false; // Stop traversal
                }
            }
        }
        return true;
    }

    bool VisitStmt(clang::Stmt* S) {
        if (!result) {
            // Only try to cast if T is derived from Stmt
            if constexpr (std::is_base_of<clang::Stmt, T>::value) {
                if (auto* Node = llvm::dyn_cast<T>(S)) {
                    result = Node;
                    return false; // Stop traversal
                }
            }
        }
        return true;
    }

    bool VisitType(clang::Type* Ty) {
        if (!result) {
            // Only try to cast if T is derived from Type
            if constexpr (std::is_base_of<clang::Type, T>::value) {
                if (auto* Node = llvm::dyn_cast<T>(Ty)) {
                    result = Node;
                    return false; // Stop traversal
                }
            }
        }
        return true;
    }
};

template <typename T>
T* findFirst(clang::ASTContext& ctx) {
    FirstNodeFinder<T> finder;
    finder.TraverseDecl(ctx.getTranslationUnitDecl());
    return finder.result;
}

/**
 * @brief Find node by name
 * @tparam T AST node type with getName() or getNameAsString()
 * @param ctx ASTContext to search
 * @param name Name to search for
 * @return Node with matching name, or nullptr
 */
template <typename T>
class NamedNodeFinder : public clang::RecursiveASTVisitor<NamedNodeFinder<T>> {
public:
    std::string targetName;
    T* result = nullptr;

    explicit NamedNodeFinder(const std::string& name) : targetName(name) {}

    bool VisitDecl(clang::Decl* D) {
        if (!result) {
            if (auto* Node = llvm::dyn_cast<T>(D)) {
                if (auto* ND = llvm::dyn_cast<clang::NamedDecl>(Node)) {
                    if (ND->getNameAsString() == targetName) {
                        result = Node;
                        return false;
                    }
                }
            }
        }
        return true;
    }
};

template <typename T>
T* findByName(clang::ASTContext& ctx, const std::string& name) {
    NamedNodeFinder<T> finder(name);
    finder.TraverseDecl(ctx.getTranslationUnitDecl());
    return finder.result;
}

// Convenience shortcuts for common types
inline clang::FunctionDecl* findFirstFunction(clang::ASTContext& ctx) {
    return findFirst<clang::FunctionDecl>(ctx);
}

inline clang::CXXRecordDecl* findFirstClass(clang::ASTContext& ctx) {
    return findFirst<clang::CXXRecordDecl>(ctx);
}

inline clang::VarDecl* findFirstVariable(clang::ASTContext& ctx) {
    return findFirst<clang::VarDecl>(ctx);
}

inline clang::EnumDecl* findFirstEnum(clang::ASTContext& ctx) {
    return findFirst<clang::EnumDecl>(ctx);
}

inline clang::FunctionDecl* findFunctionByName(clang::ASTContext& ctx, const std::string& name) {
    return findByName<clang::FunctionDecl>(ctx, name);
}

inline clang::CXXRecordDecl* findClassByName(clang::ASTContext& ctx, const std::string& name) {
    return findByName<clang::CXXRecordDecl>(ctx, name);
}

inline clang::VarDecl* findVariableByName(clang::ASTContext& ctx, const std::string& name) {
    return findByName<clang::VarDecl>(ctx, name);
}

/**
 * @brief Generate C code from C AST using PathMapper
 * @param cASTContext C ASTContext
 * @param pathMapper PathMapper with all generated TUs
 * @return Generated C code as string
 */
inline std::string generateCCode(clang::ASTContext& cASTContext, PathMapper& pathMapper) {
    std::string cCode;
    llvm::raw_string_ostream codeStream(cCode);
    CodeGenerator generator(codeStream, cASTContext);

    // Get all target files from PathMapper
    std::vector<std::string> targetFiles = pathMapper.getAllTargetFiles();

    // Print all TUs created by PathMapper (skip <stdin>.c - it's just the dummy TU)
    for (const auto& targetPath : targetFiles) {
        if (targetPath.find("<stdin>") != std::string::npos) {
            continue;
        }

        clang::TranslationUnitDecl* TU = pathMapper.getOrCreateTU(targetPath);
        if (TU) {
            generator.printTranslationUnit(TU);
        }
    }

    codeStream.flush();
    return cCode;
}

/**
 * @brief Generate C code from single TU (legacy)
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

} // namespace test
} // namespace cpptoc
