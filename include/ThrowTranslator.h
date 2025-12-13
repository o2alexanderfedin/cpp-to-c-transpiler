// ThrowTranslator.h - Translate throw expressions to cxx_throw runtime calls
// Story #79: Implement Throw Expression Translation
// SOLID Principles:
//   - Single Responsibility: Translates throw expressions to C code
//   - Open/Closed: Extensible for different exception types
//   - Dependency Inversion: Depends on abstractions (string generation)

#ifndef THROW_TRANSLATOR_H
#define THROW_TRANSLATOR_H

#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Type.h"
#include <string>

namespace clang {

/// @brief Translates C++ throw expressions into C code with cxx_throw runtime calls
///
/// This class generates C code that:
/// 1. Allocates exception object on the heap (malloc)
/// 2. Calls exception constructor with arguments
/// 3. Extracts type_info string for type matching
/// 4. Invokes cxx_throw(exception_obj, type_info)
/// 5. Handles re-throw (throw;) using current frame's exception
class ThrowTranslator {
public:
    /// @brief Generate complete throw translation code
    /// @param throwExpr The CXXThrowExpr AST node to translate
    /// @return C code that allocates exception, calls constructor, and invokes cxx_throw
    std::string generateThrowCode(const CXXThrowExpr *throwExpr) const;

    /// @brief Generate re-throw code (throw; with no expression)
    /// @return C code that re-throws current exception from frame
    std::string generateRethrowCode() const;

    /// @brief Generate exception object allocation code
    /// @param exceptionType The type of exception to allocate
    /// @return C code: struct Type *__ex = (struct Type*)malloc(sizeof(struct Type));
    std::string generateExceptionAllocation(clang::QualType exceptionType) const;

    /// @brief Generate exception constructor call
    /// @param throwExpr The throw expression containing constructor arguments
    /// @param exceptionVarName Name of allocated exception variable
    /// @return C code calling constructor with arguments
    std::string generateConstructorCall(const CXXThrowExpr *throwExpr,
                                         const std::string& exceptionVarName) const;

    /// @brief Extract type info string from exception type
    /// @param exceptionType The exception type
    /// @return Type info string for runtime type matching (e.g., "Error")
    std::string extractTypeInfo(clang::QualType exceptionType) const;

    /// @brief Generate cxx_throw runtime call
    /// @param exceptionVarName Name of exception object variable
    /// @param typeInfo Type info string for matching
    /// @return C code: cxx_throw(exception_obj, type_info);
    std::string generateCxxThrowCall(const std::string& exceptionVarName,
                                      const std::string& typeInfo) const;

private:
    /// @brief Get mangled type name for exception type
    /// @param type The exception type
    /// @return Mangled type name (simplified for now)
    std::string getMangledTypeName(clang::QualType type) const;

    /// @brief Get constructor name for exception type
    /// @param recordDecl The class/struct record
    /// @return Mangled constructor name (e.g., "Error__ctor")
    std::string getConstructorName(const CXXRecordDecl *recordDecl) const;

    /// @brief Convert constructor arguments to C code string
    /// @param ctorExpr The constructor expression
    /// @return Comma-separated C code for arguments
    std::string argumentsToString(const CXXConstructExpr *ctorExpr) const;

    /// @brief Convert expression to C code string (placeholder)
    /// @param expr Expression to convert
    /// @return C code string representation
    std::string exprToString(const Expr *expr) const;
};

} // namespace clang

#endif // THROW_TRANSLATOR_H
