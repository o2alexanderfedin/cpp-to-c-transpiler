/**
 * @file ParameterHandler.cpp
 * @brief Implementation of ParameterHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle parameter translation.
 * Follows Chain of Responsibility pattern - each AST node type has its own handler.
 */

#include "dispatch/ParameterHandler.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void ParameterHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &ParameterHandler::canHandle,
        &ParameterHandler::handleParameter
    );
}

bool ParameterHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // Use exact type matching (getKind) for ParmVarDecl
    return D->getKind() == clang::Decl::ParmVar;
}

void ParameterHandler::handleParameter(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(D->getKind() == clang::Decl::ParmVar && "Must be ParmVarDecl");

    const auto* cppParam = llvm::cast<clang::ParmVarDecl>(D);

    // Extract parameter name
    std::string paramName = cppParam->getNameAsString();
    clang::IdentifierInfo& II = cASTContext.Idents.get(paramName);

    // Translate parameter type via TypeHandler (convert references to pointers)
    clang::QualType cppParamType = cppParam->getType();
    const clang::Type* cppParamTypePtr = cppParamType.getTypePtr();

    // Dispatch the parameter type to TypeHandler, which stores mapping in TypeMapper
    bool typeHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Type*>(cppParamTypePtr));

    // Retrieve translated type from TypeMapper
    cpptoc::TypeMapper& typeMapper = disp.getTypeMapper();
    clang::QualType cParamType = typeMapper.getCreatedType(cppParamTypePtr);

    // If TypeHandler didn't handle this type (pass-through), use original type
    if (cParamType.isNull()) {
        cParamType = cppParamType;
        llvm::outs() << "[ParameterHandler] TypeHandler pass-through for parameter type: "
                     << cppParamType.getAsString() << "\n";
    }

    // Create C parameter with translated type
    // Using TranslationUnitDecl as DeclContext (standard pattern for parameters)
    clang::ParmVarDecl* cParam = clang::ParmVarDecl::Create(
        cASTContext,
        cASTContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        cParamType,
        cASTContext.getTrivialTypeSourceInfo(cParamType),
        clang::SC_None,
        nullptr  // No default argument
    );

    assert(cParam && "Failed to create C ParmVarDecl");

    // Store mapping so FunctionHandler can retrieve this created parameter
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    declMapper.setCreatedDecl(cppParam, cParam);

    // Debug output for verification
    llvm::outs() << "[ParameterHandler] Translated parameter: " << paramName
                 << " (" << cppParamType.getAsString() << " → "
                 << cParamType.getAsString() << ")\n";

    // NOTE: Parameters are not added to TranslationUnit directly
    // They will be associated with their parent FunctionDecl by FunctionHandler
}

} // namespace cpptoc
