/**
 * @file MethodHandler.cpp
 * @brief Implementation of MethodHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle method translation.
 * Translates C++ methods to C free functions with explicit "this" parameter
 * for instance methods.
 *
 * Uses NameMangler for all name mangling following the dispatcher pattern.
 */

#include "dispatch/MethodHandler.h"
#include "CNodeBuilder.h"
#include "NameMangler.h"
#include "mapping/DeclMapper.h"
#include "mapping/StmtMapper.h"
#include "mapping/TypeMapper.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void MethodHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &MethodHandler::canHandle,
        &MethodHandler::handleMethod
    );
}

bool MethodHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // Accept CXXMethodDecl but exclude constructors and destructors
    if (D->getKind() != clang::Decl::CXXMethod) {
        return false;
    }

    const auto* method = llvm::cast<clang::CXXMethodDecl>(D);

    // Exclude constructors and destructors (they have dedicated handlers)
    if (llvm::isa<clang::CXXConstructorDecl>(method) ||
        llvm::isa<clang::CXXDestructorDecl>(method)) {
        return false;
    }

    return true;
}

void MethodHandler::handleMethod(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(D->getKind() == clang::Decl::CXXMethod && "Must be CXXMethodDecl");

    const auto* cppMethod = llvm::cast<clang::CXXMethodDecl>(D);

    // Check if already translated (avoid duplicates)
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    if (declMapper.hasCreated(cppMethod)) {
        llvm::outs() << "[MethodHandler] Already translated method: "
                     << cppMethod->getNameAsString() << " (skipping)\n";
        return;
    }

    // Get parent class
    const clang::CXXRecordDecl* classDecl = cppMethod->getParent();
    assert(classDecl && "Method must have parent class");

    // Use NameMangler free function API for name mangling
    // mangle_method() handles namespace prefix, class prefix, and overload resolution
    std::string mangledName = cpptoc::mangle_method(cppMethod);

    // Extract method properties
    clang::QualType cppReturnType = cppMethod->getReturnType();

    // Translate return type via TypeHandler (convert references to pointers)
    const clang::Type* cppReturnTypePtr = cppReturnType.getTypePtr();
    bool typeHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Type*>(cppReturnTypePtr));

    // Retrieve translated type from TypeMapper
    cpptoc::TypeMapper& typeMapper = disp.getTypeMapper();
    clang::QualType cReturnType = typeMapper.getCreated(cppReturnTypePtr);

    // If TypeHandler didn't handle this type (pass-through), use original type
    if (cReturnType.isNull()) {
        cReturnType = cppReturnType;
        llvm::outs() << "[MethodHandler] TypeHandler pass-through for return type: "
                     << cppReturnType.getAsString() << "\n";
    }

    // Prepare parameters vector
    std::vector<clang::ParmVarDecl*> allParams;

    // Add "this" parameter ONLY if not a static method
    if (!cppMethod->isStatic()) {
        clang::ParmVarDecl* thisParam = createThisParameter(classDecl, cASTContext);
        assert(thisParam && "Failed to create 'this' parameter");
        allParams.push_back(thisParam);
    }

    // Translate method parameters
    std::vector<clang::ParmVarDecl*> methodParams = translateParameters(cppMethod, disp, cppASTContext, cASTContext);
    allParams.insert(allParams.end(), methodParams.begin(), methodParams.end());

    // Translate function body (if exists) via CompoundStmtHandler
    clang::CompoundStmt* cBody = nullptr;
    if (cppMethod->hasBody()) {
        const clang::Stmt* cppBody = cppMethod->getBody();
        if (cppBody) {
            // Dispatch body to CompoundStmtHandler
            bool bodyHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppBody));
            if (bodyHandled) {
                // Retrieve created C body from StmtMapper
                cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
                clang::Stmt* cStmt = stmtMapper.getCreated(cppBody);

                if (cStmt) {
                    cBody = llvm::dyn_cast<clang::CompoundStmt>(cStmt);
                    if (cBody) {
                        llvm::outs() << "[MethodHandler] Body dispatched and retrieved successfully "
                                     << "(" << cBody->size() << " statements)\n";
                    } else {
                        llvm::errs() << "[MethodHandler] Error: Retrieved statement is not CompoundStmt for method: "
                                     << mangledName << "\n";
                    }
                } else {
                    llvm::errs() << "[MethodHandler] Warning: CompoundStmtHandler did not create C body for method: "
                                 << mangledName << "\n";
                }
            }
        }
    }

    // Create C function using CNodeBuilder
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* cFunc = builder.funcDecl(
        mangledName,
        cReturnType,
        allParams,
        cBody
    );

    assert(cFunc && "Failed to create C FunctionDecl");

    // Verify body was properly attached
    if (cBody) {
        assert(cFunc->hasBody() && "Function should have body after creation");
        assert(cFunc->getBody() == cBody && "Function body should match provided body");
        llvm::outs() << "[MethodHandler] Function body successfully attached to: " << mangledName << "\n";
    }

    // Get target path for this C++ source file
    std::string targetPath = disp.getTargetPath(cppASTContext, D);

    // Get or create C TranslationUnit for this target file
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* cTU = pathMapper.getOrCreateTU(targetPath);
    assert(cTU && "Failed to get/create C TranslationUnit");

    // Add C function to C TranslationUnit
    cFunc->setDeclContext(cTU);
    cTU->addDecl(cFunc);

    // Register node location in PathMapper for tracking
    pathMapper.setNodeLocation(cFunc, targetPath);

    // Store declaration mapping in DeclMapper
    declMapper.setCreated(cppMethod, cFunc);

    // Debug output for verification
    const char* methodType = cppMethod->isStatic() ? "static" : "instance";
    llvm::outs() << "[MethodHandler] Translated " << methodType << " method: "
                 << classDecl->getNameAsString() << "::" << cppMethod->getNameAsString()
                 << " → " << mangledName;

    if (!cppMethod->isStatic()) {
        llvm::outs() << "(struct " << classDecl->getNameAsString() << "* this, ...)";
    } else {
        llvm::outs() << "(...)";
    }

    llvm::outs() << " → " << targetPath << "\n";
}

clang::ParmVarDecl* MethodHandler::createThisParameter(
    const clang::CXXRecordDecl* classDecl,
    clang::ASTContext& cASTContext
) {
    // Use NameMangler API to get properly mangled class name (includes namespace prefix)
    std::string className = cpptoc::mangle_class(classDecl);

    // Create struct type with properly mangled class name
    clang::IdentifierInfo& structII = cASTContext.Idents.get(className);
    clang::RecordDecl* structDecl = clang::RecordDecl::Create(
        cASTContext,
        clang::TagTypeKind::Struct,
        cASTContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &structII
    );

    // Create pointer type: struct ClassName*
    clang::QualType structType = cASTContext.getRecordType(structDecl);
    clang::QualType pointerType = cASTContext.getPointerType(structType);

    // Create "this" parameter
    clang::IdentifierInfo& thisII = cASTContext.Idents.get("this");
    clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
        cASTContext,
        nullptr,  // DeclContext set later by FunctionDecl
        clang::SourceLocation(),
        clang::SourceLocation(),
        &thisII,
        pointerType,
        cASTContext.getTrivialTypeSourceInfo(pointerType),
        clang::SC_None,
        nullptr  // No default argument
    );

    return thisParam;
}

std::vector<clang::ParmVarDecl*> MethodHandler::translateParameters(
    const clang::CXXMethodDecl* method,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext
) {
    std::vector<clang::ParmVarDecl*> cParams;

    // Dispatch each parameter to ParameterHandler
    // Following Chain of Responsibility pattern
    for (const auto* cppParam : method->parameters()) {
        // Cast away const for dispatch
        clang::ParmVarDecl* cppParamNonConst = const_cast<clang::ParmVarDecl*>(cppParam);

        // Dispatch parameter to ParameterHandler
        bool handled = disp.dispatch(cppASTContext, cASTContext, cppParamNonConst);

        if (!handled) {
            llvm::errs() << "[MethodHandler] Error: No handler for parameter: "
                         << cppParam->getNameAsString() << "\n";
            continue;
        }

        // Retrieve created C parameter from DeclMapper
        cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
        clang::Decl* cDecl = declMapper.getCreated(cppParam);

        if (!cDecl) {
            llvm::errs() << "[MethodHandler] Error: ParameterHandler did not create C parameter for: "
                         << cppParam->getNameAsString() << "\n";
            continue;
        }

        // Cast to ParmVarDecl
        clang::ParmVarDecl* cParam = llvm::cast<clang::ParmVarDecl>(cDecl);
        cParams.push_back(cParam);
    }

    return cParams;
}

} // namespace cpptoc
