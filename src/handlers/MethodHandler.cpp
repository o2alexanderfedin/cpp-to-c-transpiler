/**
 * @file MethodHandler.cpp
 * @brief Implementation of MethodHandler
 *
 * TDD Implementation: Start minimal, add complexity as tests demand.
 *
 * Implementation follows the specification in:
 * @see include/handlers/MethodHandler.h
 */

#include "handlers/MethodHandler.h"
#include "handlers/HandlerContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Type.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

bool MethodHandler::canHandle(const clang::Decl* D) const {
    // Only handle CXXMethodDecl, but exclude constructors and destructors
    // Constructors and destructors are handled by separate handlers
    if (const auto* MD = llvm::dyn_cast<clang::CXXMethodDecl>(D)) {
        // Exclude constructors and destructors
        if (llvm::isa<clang::CXXConstructorDecl>(MD) ||
            llvm::isa<clang::CXXDestructorDecl>(MD)) {
            return false;
        }
        return true;
    }
    return false;
}

clang::Decl* MethodHandler::handleDecl(const clang::Decl* D, HandlerContext& ctx) {
    const auto* cppMethod = llvm::cast<clang::CXXMethodDecl>(D);

    // Step 1: Extract class name and method name
    std::string className = getClassName(cppMethod);
    std::string methodName = cppMethod->getNameAsString();

    // Step 2: Mangle method name
    std::string mangledName = mangleMethodName(className, methodName);

    // Step 3: Translate return type
    clang::QualType cppReturnType = cppMethod->getReturnType();
    clang::QualType cReturnType = ctx.translateType(cppReturnType);

    // Step 4: Prepare parameters
    std::vector<clang::ParmVarDecl*> cParams;

    // Add "this" parameter ONLY if not a static method
    if (!cppMethod->isStatic()) {
        clang::ParmVarDecl* thisParam = createThisParameter(className, ctx);
        cParams.push_back(thisParam);
    }

    // Step 5: Translate method parameters
    std::vector<clang::ParmVarDecl*> methodParams = translateParameters(cppMethod, ctx);
    cParams.insert(cParams.end(), methodParams.begin(), methodParams.end());

    // Step 6: Create C function declaration
    clang::ASTContext& cCtx = ctx.getCContext();

    // Create identifier for function name
    clang::IdentifierInfo& funcII = cCtx.Idents.get(mangledName);
    clang::DeclarationName funcDeclName(&funcII);

    // Create function type
    llvm::SmallVector<clang::QualType, 8> paramTypes;
    for (const auto* param : cParams) {
        paramTypes.push_back(param->getType());
    }

    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = cCtx.getFunctionType(
        cReturnType,
        paramTypes,
        EPI
    );

    // Create function declaration
    clang::FunctionDecl* cFunc = clang::FunctionDecl::Create(
        cCtx,
        cCtx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        funcDeclName,
        funcType,
        cCtx.getTrivialTypeSourceInfo(funcType),
        clang::SC_None
    );

    // Step 7: Set parameters
    cFunc->setParams(cParams);

    // Step 8: Translate method body (if present)
    if (cppMethod->hasBody()) {
        const clang::Stmt* cppBody = cppMethod->getBody();
        // TODO: Translate body using StatementHandler
        // For now, we'll create an empty body
        // Body translation will be handled in integration with StatementHandler
        // which will use ExpressionHandler for member access translation

        // Create empty compound statement as placeholder
        clang::CompoundStmt* emptyBody = clang::CompoundStmt::Create(
            cCtx,
            {},
            clang::FPOptionsOverride(),
            clang::SourceLocation(),
            clang::SourceLocation()
        );
        cFunc->setBody(emptyBody);
    }

    // Step 9: Register mapping in context
    ctx.registerDecl(cppMethod, cFunc);

    return cFunc;
}

std::string MethodHandler::mangleMethodName(
    const std::string& className,
    const std::string& methodName
) const {
    // Simple mangling: ClassName_methodName
    // For basic overloading, we use same name (C doesn't support overloading)
    // Full mangling with parameter types is deferred to Phase 46
    return className + "_" + methodName;
}

clang::ParmVarDecl* MethodHandler::createThisParameter(
    const std::string& className,
    HandlerContext& ctx
) {
    clang::ASTContext& cCtx = ctx.getCContext();

    // Create struct type for the class
    // We need to create: struct ClassName* this

    // Step 1: Create identifier for the class name
    clang::IdentifierInfo& classII = cCtx.Idents.get(className);

    // Step 2: Create ElaboratedType for "struct ClassName"
    // We need to find or create the RecordDecl for this class
    // For now, we'll create a forward declaration if needed

    // Look up if we already have this struct in the translation unit
    clang::RecordDecl* classRecord = nullptr;
    auto* TU = cCtx.getTranslationUnitDecl();

    for (auto* D : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
            if (RD->getName() == className) {
                classRecord = RD;
                break;
            }
        }
    }

    // If not found, create a forward declaration
    if (!classRecord) {
        classRecord = clang::RecordDecl::Create(
            cCtx,
            clang::TagTypeKind::Struct,
            TU,
            clang::SourceLocation(),
            clang::SourceLocation(),
            &classII
        );
        // Note: Don't complete the definition, just a forward decl
    }

    // Step 3: Create struct type
    clang::QualType structType = cCtx.getRecordType(classRecord);

    // Step 4: Create pointer to struct type
    clang::QualType pointerType = cCtx.getPointerType(structType);

    // Step 5: Create parameter declaration
    clang::IdentifierInfo& thisII = cCtx.Idents.get("this");

    clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
        cCtx,
        nullptr, // No parent DeclContext yet
        clang::SourceLocation(),
        clang::SourceLocation(),
        &thisII,
        pointerType,
        cCtx.getTrivialTypeSourceInfo(pointerType),
        clang::SC_None,
        nullptr // No default argument
    );

    return thisParam;
}

std::vector<clang::ParmVarDecl*> MethodHandler::translateParameters(
    const clang::CXXMethodDecl* cppMethod,
    HandlerContext& ctx
) {
    std::vector<clang::ParmVarDecl*> cParams;
    clang::ASTContext& cCtx = ctx.getCContext();

    // Translate each parameter
    for (unsigned i = 0; i < cppMethod->getNumParams(); ++i) {
        const clang::ParmVarDecl* cppParam = cppMethod->getParamDecl(i);

        // Extract parameter properties
        std::string paramName = cppParam->getNameAsString();
        clang::QualType cppType = cppParam->getType();

        // Translate type
        clang::QualType cType = ctx.translateType(cppType);

        // Create parameter declaration
        clang::IdentifierInfo* paramII = nullptr;
        if (!paramName.empty()) {
            paramII = &cCtx.Idents.get(paramName);
        }

        clang::ParmVarDecl* cParam = clang::ParmVarDecl::Create(
            cCtx,
            nullptr, // No parent DeclContext yet
            clang::SourceLocation(),
            clang::SourceLocation(),
            paramII,
            cType,
            cCtx.getTrivialTypeSourceInfo(cType),
            clang::SC_None,
            nullptr // No default argument
        );

        cParams.push_back(cParam);
    }

    return cParams;
}

std::string MethodHandler::getClassName(const clang::CXXMethodDecl* cppMethod) const {
    // Get the parent class of this method
    const clang::CXXRecordDecl* classDecl = cppMethod->getParent();
    return classDecl->getNameAsString();
}

} // namespace cpptoc
