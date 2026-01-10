/**
 * @file ParameterHandler.cpp
 * @brief Implementation of ParameterHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle parameter translation.
 * Follows Chain of Responsibility pattern - each AST node type has its own handler.
 */

#include "dispatch/ParameterHandler.h"
#include "dispatch/TypeHandler.h"
#include "mapping/DeclMapper.h"
#include "mapping/TypeMapper.h"
#include "SourceLocationMapper.h"
#include "TargetContext.h"
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

    // Get target location for this declaration
    std::string targetPath = disp.getCurrentTargetPath();
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, D);
    }
    SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
    clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

    // Extract parameter name
    std::string paramName = cppParam->getNameAsString();
    clang::IdentifierInfo& II = cASTContext.Idents.get(paramName);

    // Translate parameter type via TypeHandler (convert references to pointers)
    clang::QualType cppParamType = cppParam->getType();

    // Use TypeHandler::translateType() to properly translate C++ types to C types
    clang::QualType cParamType = TypeHandler::translateType(cppParamType, cppASTContext, cASTContext);

    llvm::outs() << "[ParameterHandler] Translated parameter type: "
                 << cppParamType.getAsString() << " → " << cParamType.getAsString() << "\n";

    // Create C parameter with translated type
    // Using TranslationUnitDecl as DeclContext (standard pattern for parameters)
    clang::ParmVarDecl* cParam = clang::ParmVarDecl::Create(
        cASTContext,
        cASTContext.getTranslationUnitDecl(),
        targetLoc,
        targetLoc,
        &II,
        cParamType,
        cASTContext.getTrivialTypeSourceInfo(cParamType),
        clang::SC_None,
        nullptr
    );

    assert(cParam && "Failed to create C ParmVarDecl");

    // Store mapping so FunctionHandler can retrieve this created parameter
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    declMapper.setCreated(cppParam, cParam);

    llvm::outs() << "[ParameterHandler] Created C parameter: " << paramName
                 << " (type: " << cParamType.getAsString() << ")\n";

    // NOTE: Parameters are not added to TranslationUnit directly
    // They will be associated with their parent FunctionDecl by FunctionHandler
}

} // namespace cpptoc
