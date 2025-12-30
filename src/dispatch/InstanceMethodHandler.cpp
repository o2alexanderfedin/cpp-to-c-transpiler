/**
 * @file InstanceMethodHandler.cpp
 * @brief Implementation of InstanceMethodHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle instance method translation.
 * Translates C++ instance methods to C free functions with explicit "this" parameter
 * and class/namespace name prefixing.
 *
 * Phase 3: OverloadRegistry Integration
 * - Uses NameMangler for all name mangling (replaces custom getMangledName)
 * - Ensures deterministic cross-file naming via OverloadRegistry
 */

#include "dispatch/InstanceMethodHandler.h"
#include "dispatch/NamespaceHandler.h"
#include "CNodeBuilder.h"
#include "NameMangler.h"
#include "OverloadRegistry.h"
#include "mapping/DeclMapper.h"
#include "mapping/StmtMapper.h"
#include "mapping/TypeMapper.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void InstanceMethodHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &InstanceMethodHandler::canHandle,
        &InstanceMethodHandler::handleInstanceMethod
    );
}

bool InstanceMethodHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // CRITICAL: Must use exact type checking (getKind), NOT isa<>
    // We want CXXMethodDecl, but ONLY non-static, non-virtual instance methods
    if (D->getKind() != clang::Decl::CXXMethod) {
        return false;
    }

    // Cast to CXXMethodDecl to check properties
    const auto* method = llvm::cast<clang::CXXMethodDecl>(D);

    // Exclude constructors and destructors (they have dedicated handlers)
    if (llvm::isa<clang::CXXConstructorDecl>(method) ||
        llvm::isa<clang::CXXDestructorDecl>(method)) {
        return false;
    }

    // Exclude static methods (handled by StaticMethodHandler)
    if (method->isStatic()) {
        return false;
    }

    // Exclude virtual methods (will be handled by VirtualMethodHandler in future)
    if (method->isVirtual()) {
        return false;
    }

    // Accept ONLY regular instance methods
    return true;
}

void InstanceMethodHandler::handleInstanceMethod(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(D->getKind() == clang::Decl::CXXMethod && "Must be CXXMethodDecl");

    const auto* cppMethod = llvm::cast<clang::CXXMethodDecl>(D);

    // Additional safety checks: Must be instance method
    if (cppMethod->isStatic()) {
        llvm::errs() << "InstanceMethodHandler: Unexpected static method - should be filtered by canHandle\n";
        return;
    }
    if (cppMethod->isVirtual()) {
        llvm::errs() << "InstanceMethodHandler: Unexpected virtual method - should be filtered by canHandle\n";
        return;
    }

    // Get parent class
    const clang::CXXRecordDecl* classDecl = cppMethod->getParent();
    assert(classDecl && "Instance method must have parent class");

    // Phase 3: Use NameMangler with OverloadRegistry for deterministic naming
    // NameMangler handles: namespace prefix, class prefix, overload resolution
    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    NameMangler mangler(const_cast<clang::ASTContext&>(cppASTContext), registry);
    std::string mangledName = mangler.mangleName(const_cast<clang::CXXMethodDecl*>(cppMethod));

    // Extract method properties
    clang::QualType cppReturnType = cppMethod->getReturnType();

    // Translate return type via TypeHandler (convert references to pointers)
    // Dispatch the return type to TypeHandler, which stores mapping in TypeMapper
    const clang::Type* cppReturnTypePtr = cppReturnType.getTypePtr();
    bool typeHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Type*>(cppReturnTypePtr));

    // Retrieve translated type from TypeMapper
    cpptoc::TypeMapper& typeMapper = disp.getTypeMapper();
    clang::QualType cReturnType = typeMapper.getCreated(cppReturnTypePtr);

    // If TypeHandler didn't handle this type (pass-through), use original type
    if (cReturnType.isNull()) {
        cReturnType = cppReturnType;
        llvm::outs() << "[InstanceMethodHandler] TypeHandler pass-through for return type: "
                     << cppReturnType.getAsString() << "\n";
    }

    // Create "this" parameter (FIRST parameter)
    clang::ParmVarDecl* thisParam = createThisParameter(classDecl, cASTContext);
    assert(thisParam && "Failed to create 'this' parameter");

    // Translate method parameters by dispatching to ParameterHandler
    std::vector<clang::ParmVarDecl*> methodParams = translateParameters(cppMethod, disp, cppASTContext, cASTContext);

    // Combine parameters: [this] + methodParams
    std::vector<clang::ParmVarDecl*> allParams;
    allParams.push_back(thisParam);
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
                    // Ensure it's a CompoundStmt as expected for function bodies
                    cBody = llvm::dyn_cast<clang::CompoundStmt>(cStmt);
                    if (cBody) {
                        llvm::outs() << "[InstanceMethodHandler] Body dispatched and retrieved successfully "
                                     << "(" << cBody->size() << " statements)\n";
                    } else {
                        llvm::errs() << "[InstanceMethodHandler] Error: Retrieved statement is not CompoundStmt for instance method: "
                                     << mangledName << "\n";
                    }
                } else {
                    llvm::errs() << "[InstanceMethodHandler] Warning: CompoundStmtHandler did not create C body for instance method: "
                                 << mangledName << "\n";
                }
            }
        }
    }

    // Create C function using CNodeBuilder
    // CNodeBuilder will set the body on the function if cBody is not nullptr
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* cFunc = builder.funcDecl(
        mangledName,
        cReturnType,
        allParams,  // Includes "this" as first parameter
        cBody       // Body is nullptr if not translated, or CompoundStmt if successfully translated
    );

    assert(cFunc && "Failed to create C FunctionDecl");

    // Verify body was properly attached
    if (cBody) {
        assert(cFunc->hasBody() && "Function should have body after creation");
        assert(cFunc->getBody() == cBody && "Function body should match provided body");
        llvm::outs() << "[InstanceMethodHandler] Function body successfully attached to: " << mangledName << "\n";
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
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    declMapper.setCreated(cppMethod, cFunc);

    // Debug output for verification
    llvm::outs() << "[InstanceMethodHandler] Translated instance method: "
                 << classDecl->getNameAsString() << "::" << cppMethod->getNameAsString()
                 << " → " << mangledName << "(struct " << classDecl->getNameAsString() << "* this, ...)"
                 << " → " << targetPath << "\n";
}

// Phase 3: Removed custom getMangledName() - now uses NameMangler::mangleName()
// This ensures deterministic naming via OverloadRegistry across all translation units

clang::ParmVarDecl* InstanceMethodHandler::createThisParameter(
    const clang::CXXRecordDecl* classDecl,
    clang::ASTContext& cASTContext
) {
    // Get class name with namespace prefix
    std::string className = classDecl->getNameAsString();

    // Check if class is in namespace and apply namespace prefix
    if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
            classDecl->getDeclContext())) {
        std::string nsPath = NamespaceHandler::getNamespacePath(ns);
        if (!nsPath.empty()) {
            // Apply namespace prefix to class name
            className = nsPath + "__" + className;
        }
    }

    // Create struct type with prefixed class name
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

std::vector<clang::ParmVarDecl*> InstanceMethodHandler::translateParameters(
    const clang::CXXMethodDecl* method,
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext
) {
    std::vector<clang::ParmVarDecl*> cParams;

    // Dispatch each parameter to ParameterHandler
    // Following Chain of Responsibility pattern: Let child handler translate children
    // NOTE: This returns ONLY method parameters (NOT "this" - that's created separately)
    for (const auto* cppParam : method->parameters()) {
        // Cast away const for dispatch (dispatcher interface requires non-const)
        clang::ParmVarDecl* cppParamNonConst = const_cast<clang::ParmVarDecl*>(cppParam);

        // Dispatch parameter to ParameterHandler
        // ParameterHandler will create C parameter and store mapping in DeclMapper
        bool handled = disp.dispatch(cppASTContext, cASTContext, cppParamNonConst);

        if (!handled) {
            llvm::errs() << "[InstanceMethodHandler] Error: No handler for parameter: "
                         << cppParam->getNameAsString() << "\n";
            continue;
        }

        // Retrieve created C parameter from DeclMapper
        cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
        clang::Decl* cDecl = declMapper.getCreated(cppParam);

        if (!cDecl) {
            llvm::errs() << "[InstanceMethodHandler] Error: ParameterHandler did not create C parameter for: "
                         << cppParam->getNameAsString() << "\n";
            continue;
        }

        // Cast to ParmVarDecl (we know ParameterHandler creates ParmVarDecl)
        clang::ParmVarDecl* cParam = llvm::cast<clang::ParmVarDecl>(cDecl);
        cParams.push_back(cParam);
    }

    return cParams;
}

} // namespace cpptoc
