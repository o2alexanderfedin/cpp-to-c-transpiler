// TryCatchTransformer.cpp - Implementation of try-catch to setjmp/longjmp transformation
// Story #78: Implement setjmp/longjmp Injection for Try-Catch Blocks

#include "TryCatchTransformer.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Type.h"
#include "clang/Lex/Lexer.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>

namespace clang {

// Constructor with frame generator dependency (Dependency Injection)
TryCatchTransformer::TryCatchTransformer(std::shared_ptr<ExceptionFrameGenerator> frameGen)
    : frameGenerator(frameGen) {}

// Default constructor creates internal frame generator
TryCatchTransformer::TryCatchTransformer()
    : frameGenerator(std::make_shared<ExceptionFrameGenerator>()) {}

// Transform complete try-catch statement to C control flow
std::string TryCatchTransformer::transformTryCatch(const CXXTryStmt *tryStmt,
                                                    const std::string& frameVarName,
                                                    const std::string& actionsTableName) const {
    std::ostringstream oss;

    // Generate frame push (before setjmp)
    oss << frameGenerator->generateFramePush(frameVarName, actionsTableName);
    oss << "\n";

    // Generate setjmp guard: if (setjmp(frame.jmpbuf) == 0)
    oss << generateSetjmpGuard(frameVarName) << " {\n";

    // Generate try body (normal execution path)
    oss << generateTryBody(tryStmt, frameVarName);

    oss << "} else {\n";

    // Generate catch handlers (exception path)
    oss << generateCatchHandlers(tryStmt, frameVarName);

    oss << "}\n";

    return oss.str();
}

// Generate setjmp injection code
std::string TryCatchTransformer::generateSetjmpGuard(const std::string& frameVarName) const {
    std::ostringstream oss;
    oss << "if (setjmp(" << frameVarName << ".jmpbuf) == 0)";
    return oss.str();
}

// Generate try body code with frame push/pop
std::string TryCatchTransformer::generateTryBody(const CXXTryStmt *tryStmt,
                                                  const std::string& frameVarName) const {
    std::ostringstream oss;

    // Push frame onto exception stack (already in frame struct, just activate)
    oss << "    // Normal execution path (try body)\n";
    oss << "    __cxx_exception_stack = &" << frameVarName << ";\n";
    oss << "    \n";

    // Try body statements
    const Stmt *tryBody = tryStmt->getTryBlock();
    if (const CompoundStmt *compound = dyn_cast<CompoundStmt>(tryBody)) {
        for (const Stmt *stmt : compound->body()) {
            oss << "    " << stmtToString(stmt) << "\n";
        }
    } else {
        oss << "    " << stmtToString(tryBody) << "\n";
    }

    // Pop frame from exception stack (normal path only)
    oss << "    \n";
    oss << "    // Pop frame on normal exit\n";
    oss << "    " << frameGenerator->generateFramePop(frameVarName);

    return oss.str();
}

// Generate catch handlers code
std::string TryCatchTransformer::generateCatchHandlers(const CXXTryStmt *tryStmt,
                                                        const std::string& frameVarName) const {
    std::ostringstream oss;

    oss << "    // Exception caught here (longjmp target)\n";
    oss << "    // frame.exception_object and frame.exception_type set by cxx_throw\n";
    oss << "    \n";

    // Generate each catch handler
    unsigned numHandlers = tryStmt->getNumHandlers();
    for (unsigned i = 0; i < numHandlers; ++i) {
        const CXXCatchStmt *handler = tryStmt->getHandler(i);
        bool isFirst = (i == 0);
        oss << generateCatchHandler(handler, frameVarName, isFirst);
    }

    return oss.str();
}

// Generate single catch handler
std::string TryCatchTransformer::generateCatchHandler(const CXXCatchStmt *handler,
                                                       const std::string& frameVarName,
                                                       bool isFirst) const {
    std::ostringstream oss;

    VarDecl *exceptionVar = handler->getExceptionDecl();

    // Check if catch-all (catch (...))
    if (!exceptionVar) {
        // Catch-all handler
        if (!isFirst) {
            oss << "    else {\n";
        } else {
            oss << "    {\n";
        }
        oss << "        // Catch-all handler\n";
        oss << "        " << stmtToString(handler->getHandlerBlock()) << "\n";
        oss << "    }\n";
        return oss.str();
    }

    // Typed catch handler
    QualType exceptionType = exceptionVar->getType();

    // Generate type check
    if (!isFirst) {
        oss << "    else ";
    } else {
        oss << "    ";
    }

    oss << generateTypeCheck(exceptionType, frameVarName) << " {\n";

    // Cast exception object to proper type
    oss << "        " << generateExceptionObjectCast(exceptionVar, frameVarName) << "\n";

    // Handler body
    if (const CompoundStmt *handlerBody = dyn_cast<CompoundStmt>(handler->getHandlerBlock())) {
        for (const Stmt *stmt : handlerBody->body()) {
            oss << "        " << stmtToString(stmt) << "\n";
        }
    } else {
        oss << "        " << stmtToString(handler->getHandlerBlock()) << "\n";
    }

    // Cleanup exception object
    oss << "        \n";
    oss << "        // Cleanup exception object\n";
    std::string varName = exceptionVar->getNameAsString();
    oss << "        " << generateExceptionCleanup(exceptionType, varName);

    oss << "    }\n";

    return oss.str();
}

// Generate exception type check code
std::string TryCatchTransformer::generateTypeCheck(QualType exceptionType,
                                                    const std::string& frameVarName) const {
    std::ostringstream oss;

    std::string typeName = getMangledTypeName(exceptionType);

    oss << "if (strcmp(" << frameVarName << ".exception_type, \""
        << typeName << "\") == 0)";

    return oss.str();
}

// Generate exception object cast and assignment
std::string TryCatchTransformer::generateExceptionObjectCast(const VarDecl *varDecl,
                                                               const std::string& frameVarName) const {
    std::ostringstream oss;

    QualType varType = varDecl->getType();
    std::string varName = varDecl->getNameAsString();

    // Get the pointed-to type (for references, get the underlying type)
    QualType pointeeType = varType;
    if (varType->isReferenceType()) {
        pointeeType = varType.getNonReferenceType();
    }

    // Generate cast
    std::string typeStr;
    if (const RecordType *RT = pointeeType->getAs<RecordType>()) {
        if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(RT->getDecl())) {
            typeStr = "struct " + RD->getNameAsString();
        } else {
            typeStr = "struct " + pointeeType.getAsString();
        }
    } else {
        typeStr = pointeeType.getAsString();
    }

    oss << typeStr << " *" << varName << " = (" << typeStr << "*)"
        << frameVarName << ".exception_object;";

    return oss.str();
}

// Generate exception cleanup code
std::string TryCatchTransformer::generateExceptionCleanup(QualType exceptionType,
                                                           const std::string& varName) const {
    std::ostringstream oss;

    // Get the actual type (not reference)
    QualType actualType = exceptionType;
    if (exceptionType->isReferenceType()) {
        actualType = exceptionType.getNonReferenceType();
    }

    // Check if type has destructor
    if (const RecordType *RT = actualType->getAs<RecordType>()) {
        if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(RT->getDecl())) {
            if (RD->hasNonTrivialDestructor()) {
                std::string dtorName = getDestructorName(RD);
                oss << dtorName << "(" << varName << ");\n";
                oss << "        ";
            }
        }
    }

    oss << "free(" << varName << ");\n";

    return oss.str();
}

// Get mangled type name for exception matching
std::string TryCatchTransformer::getMangledTypeName(QualType type) const {
    // Remove reference if present
    QualType actualType = type;
    if (type->isReferenceType()) {
        actualType = type.getNonReferenceType();
    }

    // For now, use simple name (in production, use Itanium mangling)
    if (const RecordType *RT = actualType->getAs<RecordType>()) {
        if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(RT->getDecl())) {
            return RD->getNameAsString();
        }
    }

    return actualType.getAsString();
}

// Get destructor name for exception cleanup
std::string TryCatchTransformer::getDestructorName(const CXXRecordDecl *recordDecl) const {
    // Use simple naming pattern: ClassName__dtor
    // In production, would use proper name mangling
    return recordDecl->getNameAsString() + "__dtor";
}

// Convert Clang statement to C code string (placeholder)
std::string TryCatchTransformer::stmtToString(const Stmt *stmt) const {
    if (!stmt) {
        return "";
    }

    // Use Clang's source locations to extract original text
    // For now, return placeholder
    // In production, would use Rewriter or proper AST-to-C translation

    std::string result;
    llvm::raw_string_ostream os(result);

    // Simple fallback: just indicate statement type
    if (isa<DeclStmt>(stmt)) {
        return "/* declaration */;";
    } else if (isa<CallExpr>(stmt)) {
        return "/* function call */;";
    } else if (isa<ReturnStmt>(stmt)) {
        return "/* return */;";
    } else if (isa<CompoundStmt>(stmt)) {
        std::ostringstream oss;
        oss << "{\n";
        const CompoundStmt *compound = cast<CompoundStmt>(stmt);
        for (const Stmt *child : compound->body()) {
            oss << "        " << stmtToString(child) << "\n";
        }
        oss << "    }";
        return oss.str();
    }

    return "/* statement */;";
}

} // namespace clang
