/**
 * @file VirtualMethodHandler.cpp
 * @brief Implementation of VirtualMethodHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle virtual method translation.
 * Translates C++ virtual methods to C free functions with explicit "this" parameter,
 * class/namespace name prefixing, and COM-style vtable generation.
 *
 * Phase 3: OverloadRegistry Integration
 * - Uses NameMangler for all name mangling (replaces custom getMangledName)
 * - Ensures deterministic cross-file naming via OverloadRegistry
 */

#include "dispatch/VirtualMethodHandler.h"
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
#include <sstream>

namespace cpptoc {

void VirtualMethodHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &VirtualMethodHandler::canHandle,
        &VirtualMethodHandler::handleVirtualMethod
    );
}

bool VirtualMethodHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // CRITICAL: Must use exact type checking (getKind), NOT isa<>
    // We want CXXMethodDecl, but ONLY virtual instance methods
    if (D->getKind() != clang::Decl::CXXMethod) {
        return false;
    }

    // Cast to CXXMethodDecl to check properties
    const auto* method = llvm::cast<clang::CXXMethodDecl>(D);

    // Exclude constructors and destructors (they have dedicated handlers)
    // NOTE: Even virtual destructors are excluded (handled by destructor handler)
    if (llvm::isa<clang::CXXConstructorDecl>(method) ||
        llvm::isa<clang::CXXDestructorDecl>(method)) {
        return false;
    }

    // Exclude static methods (handled by StaticMethodHandler)
    if (method->isStatic()) {
        return false;
    }

    // ONLY virtual methods (this is the key filter for VirtualMethodHandler)
    // Non-virtual instance methods are handled by InstanceMethodHandler
    return method->isVirtual();
}

void VirtualMethodHandler::handleVirtualMethod(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(D->getKind() == clang::Decl::CXXMethod && "Must be CXXMethodDecl");

    const auto* cppMethod = llvm::cast<clang::CXXMethodDecl>(D);

    // Additional safety checks: Must be virtual method
    if (cppMethod->isStatic()) {
        llvm::errs() << "VirtualMethodHandler: Unexpected static method - should be filtered by canHandle\n";
        return;
    }
    if (!cppMethod->isVirtual()) {
        llvm::errs() << "VirtualMethodHandler: Unexpected non-virtual method - should be filtered by canHandle\n";
        return;
    }

    // Get parent class
    const clang::CXXRecordDecl* classDecl = cppMethod->getParent();
    assert(classDecl && "Virtual method must have parent class");

    // Phase 3: Use NameMangler with OverloadRegistry for deterministic naming
    // NameMangler handles: namespace prefix, class prefix, overload resolution
    cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
    NameMangler mangler(const_cast<clang::ASTContext&>(cppASTContext), registry);
    std::string mangledName = mangler.mangleName(const_cast<clang::CXXMethodDecl*>(cppMethod));

    // Generate COM-style static declaration (for compile-time type safety)
    // This is output before vtable struct definitions
    // Phase 3: Pass mangledName directly (already computed via NameMangler above)
    std::string staticDecl = generateStaticDeclaration(cppMethod, classDecl, cASTContext, mangledName);
    // TODO: Store static declaration for later output
    // For now, we just log it
    llvm::outs() << "[VirtualMethodHandler] Static declaration: " << staticDecl << "\n";

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
        llvm::outs() << "[VirtualMethodHandler] TypeHandler pass-through for return type: "
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
    // Pure virtual methods have no body
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
                        llvm::outs() << "[VirtualMethodHandler] Body dispatched and retrieved successfully "
                                     << "(" << cBody->size() << " statements)\n";
                    } else {
                        llvm::errs() << "[VirtualMethodHandler] Error: Retrieved statement is not CompoundStmt for virtual method: "
                                     << mangledName << "\n";
                    }
                } else {
                    llvm::errs() << "[VirtualMethodHandler] Warning: CompoundStmtHandler did not create C body for virtual method: "
                                 << mangledName << "\n";
                }
            }
        }
    } else if (cppMethod->isPureVirtual()) {
        llvm::outs() << "[VirtualMethodHandler] Pure virtual method (no body): " << mangledName << "\n";
    }

    // Create C function using CNodeBuilder
    // CNodeBuilder will set the body on the function if cBody is not nullptr
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* cFunc = builder.funcDecl(
        mangledName,
        cReturnType,
        allParams,  // Includes "this" as first parameter
        cBody       // Body is nullptr for pure virtual, or CompoundStmt if successfully translated
    );

    assert(cFunc && "Failed to create C FunctionDecl");

    // Verify body was properly attached (if not pure virtual)
    if (cBody) {
        assert(cFunc->hasBody() && "Function should have body after creation");
        assert(cFunc->getBody() == cBody && "Function body should match provided body");
        llvm::outs() << "[VirtualMethodHandler] Function body successfully attached to: " << mangledName << "\n";
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

    // TODO: Register in vtable tracking for later vtable generation
    // - Add method to class vtable method list
    // - Track method signature for vtable struct field
    // - Track method pointer for vtable instance initializer

    // TODO: Coordinate with RecordHandler to mark class as polymorphic
    // - RecordHandler will add __vptr field when it processes the class

    // Debug output for verification
    llvm::outs() << "[VirtualMethodHandler] Translated virtual method: "
                 << classDecl->getNameAsString() << "::" << cppMethod->getNameAsString()
                 << " → " << mangledName << "(struct " << classDecl->getNameAsString() << "* this, ...)"
                 << " → " << targetPath;
    if (cppMethod->isPureVirtual()) {
        llvm::outs() << " [PURE VIRTUAL]";
    }
    llvm::outs() << "\n";
}

// Phase 3: Removed custom getMangledName() - now uses NameMangler::mangleName()
// This ensures deterministic naming via OverloadRegistry across all translation units

clang::ParmVarDecl* VirtualMethodHandler::createThisParameter(
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

std::string VirtualMethodHandler::generateStaticDeclaration(
    const clang::CXXMethodDecl* method,
    const clang::CXXRecordDecl* classDecl,
    clang::ASTContext& cASTContext,
    const std::string& mangledName
) {
    // Phase 3: mangledName now passed as parameter (computed via NameMangler by caller)

    // Get return type as string
    std::string returnType = method->getReturnType().getAsString();

    // Get class name with namespace prefix (for struct this parameter)
    std::string className = classDecl->getNameAsString();
    if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
            classDecl->getDeclContext())) {
        std::string nsPath = NamespaceHandler::getNamespacePath(ns);
        if (!nsPath.empty()) {
            className = nsPath + "__" + className;
        }
    }

    // Build parameter list starting with "this"
    std::string params = "struct " + className + " *this";

    // Add method parameters
    for (const auto* param : method->parameters()) {
        params += ", ";
        params += param->getType().getAsString();
        params += " ";
        params += param->getNameAsString();
    }

    // Format: static ReturnType MangledName(params);
    std::string declaration = "static " + returnType + " " + mangledName + "(" + params + ");";

    return declaration;
}

std::vector<clang::ParmVarDecl*> VirtualMethodHandler::translateParameters(
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
            llvm::errs() << "[VirtualMethodHandler] Error: No handler for parameter: "
                         << cppParam->getNameAsString() << "\n";
            continue;
        }

        // Retrieve created C parameter from DeclMapper
        cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
        clang::Decl* cDecl = declMapper.getCreated(cppParam);

        if (!cDecl) {
            llvm::errs() << "[VirtualMethodHandler] Error: ParameterHandler did not create C parameter for: "
                         << cppParam->getNameAsString() << "\n";
            continue;
        }

        // Cast to ParmVarDecl (we know ParameterHandler creates ParmVarDecl)
        clang::ParmVarDecl* cParam = llvm::cast<clang::ParmVarDecl>(cDecl);
        cParams.push_back(cParam);
    }

    return cParams;
}

std::string VirtualMethodHandler::getNamespacePrefix(const clang::CXXRecordDecl* classDecl) {
    // Check if class is in namespace
    if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
            classDecl->getDeclContext())) {
        std::string nsPath = NamespaceHandler::getNamespacePath(ns);
        if (!nsPath.empty()) {
            // Return namespace path with trailing __
            return nsPath + "__";
        }
    }
    // No namespace
    return "";
}

std::string VirtualMethodHandler::getVtableStructName(const clang::CXXRecordDecl* classDecl) {
    std::string className = classDecl->getNameAsString();

    // Apply namespace prefix if in namespace
    if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
            classDecl->getDeclContext())) {
        std::string nsPath = NamespaceHandler::getNamespacePath(ns);
        if (!nsPath.empty()) {
            className = nsPath + "__" + className;
        }
    }

    return className + "__vtable";
}

std::string VirtualMethodHandler::getVtableInstanceName(const clang::CXXRecordDecl* classDecl) {
    std::string className = classDecl->getNameAsString();

    // Apply namespace prefix if in namespace
    if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
            classDecl->getDeclContext())) {
        std::string nsPath = NamespaceHandler::getNamespacePath(ns);
        if (!nsPath.empty()) {
            className = nsPath + "__" + className;
        }
    }

    return className + "__vtable_instance";
}

std::string VirtualMethodHandler::generateFunctionPointerType(
    const clang::CXXMethodDecl* method,
    const std::string& className,
    clang::ASTContext& cASTContext)
{
    std::string result;

    // Get return type
    clang::QualType returnType = method->getReturnType();
    std::string returnTypeStr = returnType.getAsString();

    // Build parameter list: struct ClassName *this + method parameters
    std::string params = "struct " + className + " *this";

    for (const auto* param : method->parameters()) {
        params += ", ";
        params += param->getType().getAsString();
    }

    // Format: ReturnType (*)(params)
    result = returnTypeStr + " (*)(" + params + ")";

    return result;
}

std::string VirtualMethodHandler::generateVtableStruct(
    const clang::CXXRecordDecl* classDecl,
    const std::vector<const clang::CXXMethodDecl*>& virtualMethods,
    clang::ASTContext& cASTContext)
{
    std::string className = classDecl->getNameAsString();

    // Apply namespace prefix if needed
    if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
            classDecl->getDeclContext())) {
        std::string nsPath = NamespaceHandler::getNamespacePath(ns);
        if (!nsPath.empty()) {
            className = nsPath + "__" + className;
        }
    }

    std::string vtableStructName = className + "__vtable";

    std::stringstream ss;
    ss << "struct " << vtableStructName << " {\n";

    // RTTI type_info pointer (first field - Itanium ABI)
    ss << "    const struct __class_type_info *type_info;\n";

    // Virtual methods (destructor first if present, then in declaration order)
    for (const auto* method : virtualMethods) {
        std::string fieldName = method->getNameAsString();

        // Special case for destructor
        if (llvm::isa<clang::CXXDestructorDecl>(method)) {
            ss << "    void (*destructor)(struct " << className << " *this);\n";
        } else {
            // Generate strongly typed function pointer
            std::string returnType = method->getReturnType().getAsString();

            // Build parameter list
            std::string params = "struct " + className + " *this";
            for (const auto* param : method->parameters()) {
                params += ", ";
                params += param->getType().getAsString();
            }

            ss << "    " << returnType << " (*" << fieldName << ")(" << params << ");\n";
        }
    }

    ss << "};\n";

    return ss.str();
}

std::string VirtualMethodHandler::generateVtableInstance(
    const clang::CXXRecordDecl* classDecl,
    const std::vector<const clang::CXXMethodDecl*>& virtualMethods,
    clang::ASTContext& cASTContext)
{
    std::string className = classDecl->getNameAsString();

    // Apply namespace prefix
    if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(
            classDecl->getDeclContext())) {
        std::string nsPath = NamespaceHandler::getNamespacePath(ns);
        if (!nsPath.empty()) {
            className = nsPath + "__" + className;
        }
    }

    std::string vtableStructName = className + "__vtable";
    std::string vtableInstanceName = className + "__vtable_instance";

    std::stringstream ss;
    ss << "static struct " << vtableStructName << " " << vtableInstanceName << " = {\n";

    // RTTI type_info pointer
    ss << "    .type_info = &" << className << "__type_info,\n";

    // Virtual method pointers
    // Phase 3: Use NameMangler with OverloadRegistry for each method
    for (const auto* method : virtualMethods) {
        // Get method's source ASTContext and use NameMangler
        cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
        NameMangler mangler(const_cast<clang::ASTContext&>(method->getASTContext()), registry);
        std::string methodName = mangler.mangleName(const_cast<clang::CXXMethodDecl*>(method));
        std::string fieldName = method->getNameAsString();

        if (llvm::isa<clang::CXXDestructorDecl>(method)) {
            ss << "    .destructor = " << className << "__dtor,\n";
        } else {
            ss << "    ." << fieldName << " = " << methodName << ",\n";
        }
    }

    ss << "};\n";

    return ss.str();
}

} // namespace cpptoc
