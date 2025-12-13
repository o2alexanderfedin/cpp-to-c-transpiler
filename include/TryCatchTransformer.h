// TryCatchTransformer.h - Transform try-catch blocks to setjmp/longjmp control flow
// Story #78: Implement setjmp/longjmp Injection for Try-Catch Blocks
// SOLID Principles:
//   - Single Responsibility: Transforms try-catch blocks to C control flow
//   - Open/Closed: Extensible for different exception handling patterns
//   - Dependency Inversion: Depends on ExceptionFrameGenerator abstraction

#ifndef TRY_CATCH_TRANSFORMER_H
#define TRY_CATCH_TRANSFORMER_H

#include "clang/AST/Decl.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/StmtCXX.h"
#include "ExceptionFrameGenerator.h"
#include <string>
#include <memory>

namespace clang {

/// @brief Transforms C++ try-catch blocks into setjmp/longjmp control flow
///
/// This class generates C code that implements SJLJ exception handling:
/// - try blocks → if (setjmp(frame.jmpbuf) == 0) { ... }
/// - catch blocks → else { ... } with type matching
/// - Frame push before setjmp, pop on normal path
/// - longjmp returns 1, directing execution to catch handlers
class TryCatchTransformer {
public:
    /// @brief Constructor with exception frame generator dependency
    /// @param frameGen Exception frame generator for frame operations
    explicit TryCatchTransformer(std::shared_ptr<ExceptionFrameGenerator> frameGen);

    /// @brief Default constructor (creates internal frame generator)
    TryCatchTransformer();

    /// @brief Transform a try-catch statement to C control flow
    /// @param tryStmt The CXXTryStmt AST node to transform
    /// @param frameVarName Name for the exception frame variable
    /// @param actionsTableName Name of the action table for this try block
    /// @return C code implementing setjmp/longjmp control flow
    std::string transformTryCatch(const CXXTryStmt *tryStmt,
                                   const std::string& frameVarName,
                                   const std::string& actionsTableName) const;

    /// @brief Generate setjmp injection code (if branch guard)
    /// @param frameVarName Name of the exception frame variable
    /// @return C code: if (setjmp(frame.jmpbuf) == 0)
    std::string generateSetjmpGuard(const std::string& frameVarName) const;

    /// @brief Generate try body code (normal execution path)
    /// @param tryStmt The try statement containing the body
    /// @param frameVarName Name for frame push/pop operations
    /// @return C code for try body with frame push/pop
    std::string generateTryBody(const CXXTryStmt *tryStmt,
                                 const std::string& frameVarName) const;

    /// @brief Generate catch handlers code (exception path)
    /// @param tryStmt The try statement containing catch handlers
    /// @param frameVarName Name of the exception frame variable
    /// @return C code for catch handlers with type matching
    std::string generateCatchHandlers(const CXXTryStmt *tryStmt,
                                       const std::string& frameVarName) const;

    /// @brief Generate single catch handler
    /// @param handler The catch handler statement
    /// @param frameVarName Name of the exception frame variable
    /// @param isFirst Whether this is the first catch handler (no else-if needed)
    /// @return C code for one catch handler with type check
    std::string generateCatchHandler(const CXXCatchStmt *handler,
                                      const std::string& frameVarName,
                                      bool isFirst) const;

    /// @brief Generate exception type check code
    /// @param exceptionType The caught exception type
    /// @param frameVarName Name of the exception frame variable
    /// @return C code: if (strcmp(frame.exception_type, "TypeName") == 0)
    std::string generateTypeCheck(QualType exceptionType,
                                   const std::string& frameVarName) const;

    /// @brief Generate exception object cast and assignment
    /// @param varDecl Variable declaration for caught exception
    /// @param frameVarName Name of the exception frame variable
    /// @return C code casting exception_object to proper type
    std::string generateExceptionObjectCast(const VarDecl *varDecl,
                                             const std::string& frameVarName) const;

    /// @brief Generate exception cleanup code (destructor + free)
    /// @param exceptionType The type of the exception to clean up
    /// @param varName Name of the exception variable
    /// @return C code calling destructor and freeing memory
    std::string generateExceptionCleanup(QualType exceptionType,
                                          const std::string& varName) const;

private:
    std::shared_ptr<ExceptionFrameGenerator> frameGenerator;

    /// @brief Get mangled type name for exception matching
    /// @param type The exception type
    /// @return Mangled type name as string
    std::string getMangledTypeName(QualType type) const;

    /// @brief Get destructor name for exception cleanup
    /// @param recordDecl The class/struct record
    /// @return Mangled destructor function name
    std::string getDestructorName(const CXXRecordDecl *recordDecl) const;

    /// @brief Convert Clang statement to C code string (placeholder)
    /// @param stmt Statement to convert
    /// @return C code string representation
    std::string stmtToString(const Stmt *stmt) const;
};

} // namespace clang

#endif // TRY_CATCH_TRANSFORMER_H
