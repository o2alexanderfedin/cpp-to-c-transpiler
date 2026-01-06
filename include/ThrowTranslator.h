// ThrowTranslator.h - Translate throw expressions to cxx_throw runtime calls
// Story #79: Implement Throw Expression Translation
// SOLID Principles:
//   - Single Responsibility: Translates throw expressions to C AST nodes
//   - Open/Closed: Extensible for different exception types
//   - Dependency Inversion: Depends on CppToCVisitorDispatcher abstraction

#ifndef THROW_TRANSLATOR_H
#define THROW_TRANSLATOR_H

#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Type.h"
#include "clang/AST/Stmt.h"
#include <string>
#include <vector>

// Forward declarations
class CppToCVisitorDispatcher;

namespace clang {
    class CNodeBuilder;
}

namespace clang {

/// @brief Translates C++ throw expressions into C AST nodes with cxx_throw runtime calls
///
/// This class generates C AST that:
/// 1. Allocates exception object on the heap (malloc)
/// 2. Calls exception constructor with arguments
/// 3. Extracts type_info string for type matching
/// 4. Invokes cxx_throw(exception_obj, type_info)
/// 5. Handles re-throw (throw;) using current frame's exception
///
/// Phase 3: Accepts dispatcher for recursive expression translation
/// Phase 5: Returns C AST nodes instead of strings (COMPLETE)
class ThrowTranslator {
public:
    /// @brief Generate complete throw translation as C AST (Phase 5: AST-based)
    /// @param throwExpr The CXXThrowExpr AST node to translate
    /// @param disp Dispatcher for recursive expression translation
    /// @param cppCtx Source C++ ASTContext
    /// @param cCtx Target C ASTContext
    /// @return CompoundStmt containing: allocation, constructor call, cxx_throw call
    CompoundStmt* generateThrowCode(
        const CXXThrowExpr *throwExpr,
        const ::CppToCVisitorDispatcher& disp,
        const ASTContext& cppCtx,
        ASTContext& cCtx
    ) const;

    /// @brief Generate re-throw as C AST (Phase 5: AST-based)
    /// @param cCtx Target C ASTContext
    /// @return CallExpr that re-throws current exception from frame
    CallExpr* generateRethrowCode(ASTContext& cCtx) const;

    /// @brief Generate exception object allocation as C AST (Phase 5: AST-based)
    /// @param exceptionType The type of exception to allocate
    /// @param cCtx Target C ASTContext
    /// @param exceptionVarName Name for allocated exception variable
    /// @return VarDecl: struct Type *__ex = (struct Type*)malloc(sizeof(struct Type));
    VarDecl* generateExceptionAllocation(
        QualType exceptionType,
        ASTContext& cCtx,
        const std::string& exceptionVarName
    ) const;

    /// @brief Generate exception constructor call as C AST (Phase 5: AST-based)
    /// @param throwExpr The throw expression containing constructor arguments
    /// @param exceptionVar VarDecl of allocated exception variable
    /// @param disp Dispatcher for argument translation
    /// @param cppCtx Source C++ ASTContext
    /// @param cCtx Target C ASTContext
    /// @return CallExpr calling constructor with arguments
    CallExpr* generateConstructorCall(
        const CXXThrowExpr *throwExpr,
        VarDecl* exceptionVar,
        const ::CppToCVisitorDispatcher& disp,
        const ASTContext& cppCtx,
        ASTContext& cCtx
    ) const;

    /// @brief Extract type info string literal as C AST (Phase 5: AST-based)
    /// @param exceptionType The exception type
    /// @param cCtx Target C ASTContext
    /// @return StringLiteral for runtime type matching (e.g., "Error")
    StringLiteral* extractTypeInfo(QualType exceptionType, ASTContext& cCtx) const;

    /// @brief Generate cxx_throw runtime call as C AST (Phase 5: AST-based)
    /// @param exceptionVar VarDecl of exception object variable
    /// @param typeInfoLiteral StringLiteral for type matching
    /// @param cCtx Target C ASTContext
    /// @return CallExpr: cxx_throw(exception_obj, type_info);
    CallExpr* generateCxxThrowCall(
        VarDecl* exceptionVar,
        StringLiteral* typeInfoLiteral,
        ASTContext& cCtx
    ) const;

private:
    /// @brief Get mangled type name for exception type
    /// @param type The exception type
    /// @return Mangled type name (simplified for now)
    std::string getMangledTypeName(QualType type) const;

    /// @brief Translate constructor arguments to C AST (Phase 5: AST-based)
    /// @param ctorExpr The constructor expression
    /// @param disp Dispatcher for argument translation
    /// @param cppCtx Source C++ ASTContext
    /// @param cCtx Target C ASTContext
    /// @return Vector of C Expr* for arguments
    std::vector<Expr*> translateArguments(
        const CXXConstructExpr *ctorExpr,
        const ::CppToCVisitorDispatcher& disp,
        const ASTContext& cppCtx,
        ASTContext& cCtx
    ) const;

    /// @brief Create FunctionDecl for malloc
    /// @param cCtx Target C ASTContext
    /// @return FunctionDecl for malloc(size_t) -> void*
    FunctionDecl* createMallocDecl(ASTContext& cCtx) const;

    /// @brief Create FunctionDecl for cxx_throw
    /// @param cCtx Target C ASTContext
    /// @return FunctionDecl for cxx_throw(void*, const char*)
    FunctionDecl* createCxxThrowDecl(ASTContext& cCtx) const;

    /// @brief Get FunctionDecl for constructor
    /// @param ctorDecl C++ constructor declaration
    /// @param disp Dispatcher (for accessing DeclMapper)
    /// @param cppCtx Source C++ ASTContext
    /// @param cCtx Target C ASTContext
    /// @return Translated C FunctionDecl
    FunctionDecl* getConstructorDecl(
        const CXXConstructorDecl* ctorDecl,
        const ::CppToCVisitorDispatcher& disp,
        const ASTContext& cppCtx,
        ASTContext& cCtx
    ) const;
};

} // namespace clang

#endif // THROW_TRANSLATOR_H
