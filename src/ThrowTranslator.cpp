// ThrowTranslator.cpp - Implementation of throw expression translator
// Story #79: Implement Throw Expression Translation
// Phase 3: Dispatcher integration for expression translation

#include "ThrowTranslator.h"
#include "NameMangler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/ExprMapper.h"
#include "CodeGenerator.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Type.h"
#include "clang/Lex/Lexer.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>

namespace clang {

// ============================================================================
// Phase 3: Dispatcher-based methods (NEW)
// ============================================================================

// Generate complete throw translation code (with dispatcher)
std::string ThrowTranslator::generateThrowCode(
    const CXXThrowExpr *throwExpr,
    const cpptoc::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    if (!throwExpr) {
        return "";
    }

    // Check for re-throw (throw; with no expression)
    const Expr *subExpr = throwExpr->getSubExpr();
    if (!subExpr) {
        return generateRethrowCode();
    }

    std::ostringstream oss;

    // Get the exception type
    QualType exceptionType = subExpr->getType();

    // 1. Generate exception object allocation
    oss << generateExceptionAllocation(exceptionType);
    oss << "\n";

    // 2. Generate constructor call (using dispatcher for arguments)
    std::string exceptionVarName = "__ex";
    oss << generateConstructorCall(throwExpr, exceptionVarName, disp, cppCtx, cCtx);
    oss << "\n";

    // 3. Extract type info
    std::string typeInfo = extractTypeInfo(exceptionType);

    // 4. Generate cxx_throw call
    oss << generateCxxThrowCall(exceptionVarName, typeInfo);

    return oss.str();
}

// Generate exception constructor call (with dispatcher)
std::string ThrowTranslator::generateConstructorCall(
    const CXXThrowExpr *throwExpr,
    const std::string& exceptionVarName,
    const cpptoc::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    std::ostringstream oss;

    const Expr *subExpr = throwExpr->getSubExpr();
    if (!subExpr) {
        return "";
    }

    // Recursively unwrap expression to find constructor
    const Expr *currentExpr = subExpr;
    const CXXConstructExpr *ctorExpr = nullptr;

    // Unwrap all wrapper expressions to find the constructor
    while (currentExpr && !ctorExpr) {
        // Try direct cast
        ctorExpr = dyn_cast<CXXConstructExpr>(currentExpr);
        if (ctorExpr) break;

        // Unwrap CXXFunctionalCastExpr (e.g., Error("msg"))
        if (const CXXFunctionalCastExpr *funcCast = dyn_cast<CXXFunctionalCastExpr>(currentExpr)) {
            currentExpr = funcCast->getSubExpr();
            continue;
        }

        // Unwrap MaterializeTemporaryExpr
        if (const MaterializeTemporaryExpr *matExpr = dyn_cast<MaterializeTemporaryExpr>(currentExpr)) {
            currentExpr = matExpr->getSubExpr();
            continue;
        }

        // Unwrap CXXBindTemporaryExpr
        if (const CXXBindTemporaryExpr *bindExpr = dyn_cast<CXXBindTemporaryExpr>(currentExpr)) {
            currentExpr = bindExpr->getSubExpr();
            continue;
        }

        // Unwrap implicit casts
        if (const ImplicitCastExpr *castExpr = dyn_cast<ImplicitCastExpr>(currentExpr)) {
            currentExpr = castExpr->getSubExpr();
            continue;
        }

        // Can't unwrap further
        break;
    }

    if (!ctorExpr) {
        // Fallback: simple assignment or copy (using dispatcher)
        oss << "// Initialize exception object (no constructor found)\n";
        oss << "*" << exceptionVarName << " = " << exprToString(subExpr, disp, cppCtx, cCtx) << ";";
        return oss.str();
    }

    // Get constructor name
    const CXXConstructorDecl *ctorDecl = ctorExpr->getConstructor();
    std::string ctorName = cpptoc::mangle_constructor(ctorDecl);

    // Generate constructor call with arguments (using dispatcher)
    std::string args = argumentsToString(ctorExpr, disp, cppCtx, cCtx);

    oss << ctorName << "(" << exceptionVarName;
    if (!args.empty()) {
        oss << ", " << args;
    }
    oss << ");";

    return oss.str();
}

// Convert constructor arguments to C code string (with dispatcher)
std::string ThrowTranslator::argumentsToString(
    const CXXConstructExpr *ctorExpr,
    const cpptoc::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    std::ostringstream oss;

    unsigned numArgs = ctorExpr->getNumArgs();
    for (unsigned i = 0; i < numArgs; ++i) {
        if (i > 0) {
            oss << ", ";
        }
        const Expr *arg = ctorExpr->getArg(i);
        oss << exprToString(arg, disp, cppCtx, cCtx);
    }

    return oss.str();
}

// Convert expression to C code string (with dispatcher)
std::string ThrowTranslator::exprToString(
    const Expr *expr,
    const cpptoc::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    if (!expr) {
        return "";
    }

    // Dispatch the expression through the dispatcher
    Expr* exprNonConst = const_cast<Expr*>(expr);
    bool handled = disp.dispatch(cppCtx, cCtx, exprNonConst);

    if (!handled) {
        llvm::errs() << "[ThrowTranslator] WARNING: Expression not handled by dispatcher: "
                     << expr->getStmtClassName() << "\n";
        return "/* unhandled expression */";
    }

    // Retrieve the translated C expression from ExprMapper
    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();
    Expr* cExpr = exprMapper.getCreated(expr);

    if (!cExpr) {
        llvm::errs() << "[ThrowTranslator] WARNING: Expression dispatched but not in ExprMapper: "
                     << expr->getStmtClassName() << "\n";
        return "/* expression not mapped */";
    }

    // Convert C Expr* to string using Clang's printPretty
    std::string result;
    llvm::raw_string_ostream OS(result);

    // Create C99 printing policy
    clang::LangOptions C99Opts;
    C99Opts.C99 = 1;
    clang::PrintingPolicy Policy(C99Opts);
    Policy.SuppressTagKeyword = false;  // Keep 'struct' keyword

    cExpr->printPretty(OS, nullptr, Policy, 0);
    OS.flush();

    return result;
}

// ============================================================================
// Legacy methods (backward compatibility - deprecated)
// ============================================================================

// Generate complete throw translation code
std::string ThrowTranslator::generateThrowCode(const CXXThrowExpr *throwExpr) const {
    if (!throwExpr) {
        return "";
    }

    // Check for re-throw (throw; with no expression)
    const Expr *subExpr = throwExpr->getSubExpr();
    if (!subExpr) {
        return generateRethrowCode();
    }

    std::ostringstream oss;

    // Get the exception type
    QualType exceptionType = subExpr->getType();

    // 1. Generate exception object allocation
    oss << generateExceptionAllocation(exceptionType);
    oss << "\n";

    // 2. Generate constructor call
    std::string exceptionVarName = "__ex";
    oss << generateConstructorCall(throwExpr, exceptionVarName);
    oss << "\n";

    // 3. Extract type info
    std::string typeInfo = extractTypeInfo(exceptionType);

    // 4. Generate cxx_throw call
    oss << generateCxxThrowCall(exceptionVarName, typeInfo);

    return oss.str();
}

// Generate re-throw code (throw; with no expression)
std::string ThrowTranslator::generateRethrowCode() const {
    std::ostringstream oss;

    // Re-throw uses current exception from frame
    // Assumes we're in a catch handler with access to frame
    oss << "// Re-throw current exception\n";
    oss << "cxx_throw(frame.exception_object, frame.exception_type);\n";

    return oss.str();
}

// Generate exception object allocation code
std::string ThrowTranslator::generateExceptionAllocation(QualType exceptionType) const {
    std::ostringstream oss;

    // Get type name
    std::string typeName;
    if (const RecordType *RT = exceptionType->getAs<RecordType>()) {
        if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(RT->getDecl())) {
            typeName = "struct " + RD->getNameAsString();
        } else {
            typeName = "struct " + exceptionType.getAsString();
        }
    } else {
        typeName = exceptionType.getAsString();
    }

    // Generate: struct Type *__ex = (struct Type*)malloc(sizeof(struct Type));
    oss << typeName << " *__ex = (" << typeName << "*)malloc(sizeof("
        << typeName << "));";

    return oss.str();
}

// Generate exception constructor call
std::string ThrowTranslator::generateConstructorCall(const CXXThrowExpr *throwExpr,
                                                      const std::string& exceptionVarName) const {
    std::ostringstream oss;

    const Expr *subExpr = throwExpr->getSubExpr();
    if (!subExpr) {
        return "";
    }

    // Recursively unwrap expression to find constructor
    const Expr *currentExpr = subExpr;
    const CXXConstructExpr *ctorExpr = nullptr;

    // Unwrap all wrapper expressions to find the constructor
    while (currentExpr && !ctorExpr) {
        // Try direct cast
        ctorExpr = dyn_cast<CXXConstructExpr>(currentExpr);
        if (ctorExpr) break;

        // Unwrap CXXFunctionalCastExpr (e.g., Error("msg"))
        if (const CXXFunctionalCastExpr *funcCast = dyn_cast<CXXFunctionalCastExpr>(currentExpr)) {
            currentExpr = funcCast->getSubExpr();
            continue;
        }

        // Unwrap MaterializeTemporaryExpr
        if (const MaterializeTemporaryExpr *matExpr = dyn_cast<MaterializeTemporaryExpr>(currentExpr)) {
            currentExpr = matExpr->getSubExpr();
            continue;
        }

        // Unwrap CXXBindTemporaryExpr
        if (const CXXBindTemporaryExpr *bindExpr = dyn_cast<CXXBindTemporaryExpr>(currentExpr)) {
            currentExpr = bindExpr->getSubExpr();
            continue;
        }

        // Unwrap implicit casts
        if (const ImplicitCastExpr *castExpr = dyn_cast<ImplicitCastExpr>(currentExpr)) {
            currentExpr = castExpr->getSubExpr();
            continue;
        }

        // Can't unwrap further
        break;
    }

    if (!ctorExpr) {
        // Fallback: simple assignment or copy
        oss << "// Initialize exception object (no constructor found)\n";
        oss << "*" << exceptionVarName << " = " << exprToString(subExpr) << ";";
        return oss.str();
    }

    // Get constructor name
    const CXXConstructorDecl *ctorDecl = ctorExpr->getConstructor();
    std::string ctorName = cpptoc::mangle_constructor(ctorDecl);

    // Generate constructor call with arguments
    std::string args = argumentsToString(ctorExpr);

    oss << ctorName << "(" << exceptionVarName;
    if (!args.empty()) {
        oss << ", " << args;
    }
    oss << ");";

    return oss.str();
}

// Extract type info string from exception type
std::string ThrowTranslator::extractTypeInfo(QualType exceptionType) const {
    // Use simplified type name for now (in production, use Itanium mangling)
    return "\"" + getMangledTypeName(exceptionType) + "\"";
}

// Generate cxx_throw runtime call
std::string ThrowTranslator::generateCxxThrowCall(const std::string& exceptionVarName,
                                                   const std::string& typeInfo) const {
    std::ostringstream oss;

    oss << "// Throw exception (initiates unwinding, longjmp to handler)\n";
    oss << "cxx_throw(" << exceptionVarName << ", " << typeInfo << ");";

    return oss.str();
}

// Get mangled type name for exception type
std::string ThrowTranslator::getMangledTypeName(QualType type) const {
    // Remove const, volatile, reference
    QualType actualType = type.getCanonicalType();
    actualType.removeLocalConst();
    actualType.removeLocalVolatile();

    if (actualType->isReferenceType()) {
        actualType = actualType.getNonReferenceType();
    }

    // Use NameMangler API for consistent name generation
    if (const RecordType *RT = actualType->getAs<RecordType>()) {
        if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(RT->getDecl())) {
            return cpptoc::mangle_class(RD);
        }
    }

    return actualType.getAsString();
}

// Get constructor name for exception type (deprecated - use cpptoc::mangle_constructor directly)
std::string ThrowTranslator::getConstructorName(const CXXRecordDecl *recordDecl) const {
    // This method is kept for backward compatibility but should not be used
    // Use cpptoc::mangle_constructor(ctorDecl) directly when constructor decl is available
    // Fallback: construct default constructor name
    return cpptoc::mangle_class(recordDecl) + "__ctor__void";
}

// Convert constructor arguments to C code string
std::string ThrowTranslator::argumentsToString(const CXXConstructExpr *ctorExpr) const {
    std::ostringstream oss;

    unsigned numArgs = ctorExpr->getNumArgs();
    for (unsigned i = 0; i < numArgs; ++i) {
        if (i > 0) {
            oss << ", ";
        }
        const Expr *arg = ctorExpr->getArg(i);
        oss << exprToString(arg);
    }

    return oss.str();
}

// Convert expression to C code string (placeholder)
std::string ThrowTranslator::exprToString(const Expr *expr) const {
    if (!expr) {
        return "";
    }

    std::string result;
    llvm::raw_string_ostream os(result);

    // Handle string literals
    if (const StringLiteral *strLit = dyn_cast<StringLiteral>(expr)) {
        os << "\"" << strLit->getString().str() << "\"";
        return os.str();
    }

    // Handle integer literals
    if (const IntegerLiteral *intLit = dyn_cast<IntegerLiteral>(expr)) {
        llvm::SmallString<64> intStr;
        intLit->getValue().toString(intStr, 10, true);
        os << intStr;
        return os.str();
    }

    // Handle implicit casts (unwrap)
    if (const ImplicitCastExpr *castExpr = dyn_cast<ImplicitCastExpr>(expr)) {
        return exprToString(castExpr->getSubExpr());
    }

    // Fallback: return placeholder
    return "/* expression */";
}

} // namespace clang
