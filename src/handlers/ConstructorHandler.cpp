/**
 * @file ConstructorHandler.cpp
 * @brief Implementation of ConstructorHandler
 *
 * TDD Implementation: Start minimal, add complexity as tests demand.
 *
 * Translation Strategy:
 * 1. Detect CXXConstructorDecl
 * 2. Extract class name
 * 3. Generate mangled function name (ClassName_init or ClassName_init_types)
 * 4. Create 'this' parameter: struct ClassName* this
 * 5. Add constructor parameters after 'this'
 * 6. Handle member initializer list (convert to assignments)
 * 7. Translate constructor body
 * 8. Return C FunctionDecl with void return type
 */

#include "handlers/ConstructorHandler.h"
#include "handlers/HandlerContext.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

bool ConstructorHandler::canHandle(const clang::Decl* D) const {
    // Check if this is a CXXConstructorDecl
    return llvm::isa<clang::CXXConstructorDecl>(D);
}

clang::Decl* ConstructorHandler::handleDecl(const clang::Decl* D, HandlerContext& ctx) {
    const auto* ctor = llvm::cast<clang::CXXConstructorDecl>(D);

    // Get parent class (the class this constructor belongs to)
    const auto* parentClass = ctor->getParent();
    if (!parentClass) {
        return nullptr; // Should never happen
    }

    std::string className = parentClass->getNameAsString();

    // Generate mangled function name
    std::string funcName = generateConstructorName(className, ctor);

    // Create 'this' parameter
    // IMPORTANT: Must use C RecordDecl, not C++ RecordDecl
    // Look up the C RecordDecl by name (similar to MethodHandler approach)
    clang::ASTContext& cCtx = ctx.getCContext();
    clang::RecordDecl* cRecordDecl = nullptr;

    // Try to find the C RecordDecl in the translation unit
    auto* TU = cCtx.getTranslationUnitDecl();
    for (auto* D : TU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(D)) {
            if (RD->getName() == className) {
                cRecordDecl = RD;
                break;
            }
        }
    }

    if (!cRecordDecl) {
        // RecordHandler should have created the struct already
        // This shouldn't happen if RecordHandler was called first
        return nullptr;
    }

    clang::QualType classType = cCtx.getRecordType(cRecordDecl);
    clang::ParmVarDecl* thisParam = createThisParameter(classType, ctx);

    // Translate constructor parameters
    std::vector<clang::ParmVarDecl*> ctorParams = translateParameters(ctor, ctx);

    // Combine 'this' parameter with constructor parameters
    std::vector<clang::ParmVarDecl*> allParams;
    allParams.push_back(thisParam);
    allParams.insert(allParams.end(), ctorParams.begin(), ctorParams.end());

    // Get void return type
    clang::ASTContext& cContext = ctx.getCContext();
    clang::QualType returnType = cContext.VoidTy;

    // Create C function using CNodeBuilder
    clang::CNodeBuilder& builder = ctx.getBuilder();
    clang::FunctionDecl* cFunc = builder.funcDecl(
        funcName,
        returnType,
        allParams,
        nullptr      // No body yet (body translation handled separately)
    );

    // Register mapping
    ctx.registerDecl(ctor, cFunc);

    // TODO: Handle member initializer list (convert : field(value) to assignments)
    // This will be implemented when StatementHandler/ExpressionHandler integration is done
    // For now, we just create the function signature

    return cFunc;
}

std::string ConstructorHandler::generateConstructorName(
    const std::string& className,
    const clang::CXXConstructorDecl* ctor
) {
    // Base name: ClassName_init
    std::string baseName = className + "_init";

    // If no parameters, just return base name
    if (ctor->getNumParams() == 0) {
        return baseName;
    }

    // Add parameter types to name for overload resolution
    // Format: ClassName_init_type1_type2_...
    std::string mangledName = baseName;

    for (const auto* param : ctor->parameters()) {
        clang::QualType paramType = param->getType();
        std::string typeName = getSimpleTypeName(paramType);
        mangledName += "_" + typeName;
    }

    return mangledName;
}

std::vector<clang::ParmVarDecl*> ConstructorHandler::translateParameters(
    const clang::CXXConstructorDecl* ctor,
    HandlerContext& ctx
) {
    std::vector<clang::ParmVarDecl*> cParams;
    clang::ASTContext& cContext = ctx.getCContext();

    // Translate each parameter
    for (const auto* cppParam : ctor->parameters()) {
        // Create identifier for parameter name
        clang::IdentifierInfo& II = cContext.Idents.get(cppParam->getNameAsString());

        // Translate parameter type (convert references to pointers)
        clang::QualType cppParamType = cppParam->getType();
        clang::QualType cParamType = translateType(cppParamType, ctx);

        // Create C parameter with translated type
        clang::ParmVarDecl* cParam = clang::ParmVarDecl::Create(
            cContext,
            cContext.getTranslationUnitDecl(),
            clang::SourceLocation(),
            clang::SourceLocation(),
            &II,
            cParamType,
            cContext.getTrivialTypeSourceInfo(cParamType),
            clang::SC_None,
            nullptr  // No default argument
        );

        cParams.push_back(cParam);

        // Register parameter mapping for later reference
        ctx.registerDecl(cppParam, cParam);
    }

    return cParams;
}

clang::ParmVarDecl* ConstructorHandler::createThisParameter(
    clang::QualType recordType,
    HandlerContext& ctx
) {
    clang::ASTContext& cContext = ctx.getCContext();

    // Create identifier for 'this'
    clang::IdentifierInfo& II = cContext.Idents.get("this");

    // Create pointer type: struct ClassName* this
    clang::QualType thisType = cContext.getPointerType(recordType);

    // Create parameter declaration
    clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
        cContext,
        cContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        thisType,
        cContext.getTrivialTypeSourceInfo(thisType),
        clang::SC_None,
        nullptr  // No default argument
    );

    return thisParam;
}

clang::QualType ConstructorHandler::translateType(
    clang::QualType cppType,
    HandlerContext& ctx
) {
    clang::ASTContext& cCtx = ctx.getCContext();

    // Check for lvalue reference (T&)
    if (const auto* lvalRefType = llvm::dyn_cast<clang::LValueReferenceType>(cppType.getTypePtr())) {
        // Transform T& → T*
        clang::QualType pointeeType = lvalRefType->getPointeeType();
        return cCtx.getPointerType(pointeeType);
    }

    // Check for rvalue reference (T&&)
    if (const auto* rvalRefType = llvm::dyn_cast<clang::RValueReferenceType>(cppType.getTypePtr())) {
        // Transform T&& → T*
        clang::QualType pointeeType = rvalRefType->getPointeeType();
        return cCtx.getPointerType(pointeeType);
    }

    // For non-reference types, pass through unchanged
    return cppType;
}

std::string ConstructorHandler::getSimpleTypeName(clang::QualType type) const {
    // Remove qualifiers (const, volatile)
    type = type.getUnqualifiedType();

    // Check for pointer types
    if (type->isPointerType()) {
        clang::QualType pointeeType = type->getPointeeType();
        std::string pointeeName = getSimpleTypeName(pointeeType);
        return pointeeName + "ptr";
    }

    // Check for reference types (should be converted to pointers by translateType)
    if (type->isReferenceType()) {
        clang::QualType pointeeType = type.getNonReferenceType();
        std::string pointeeName = getSimpleTypeName(pointeeType);
        return pointeeName + "ptr";
    }

    // Check for built-in types
    if (type->isBuiltinType()) {
        const auto* builtinType = llvm::cast<clang::BuiltinType>(type.getTypePtr());
        switch (builtinType->getKind()) {
            case clang::BuiltinType::Void:
                return "void";
            case clang::BuiltinType::Bool:
                return "bool";
            case clang::BuiltinType::Char_S:
            case clang::BuiltinType::Char_U:
            case clang::BuiltinType::Char8:
            case clang::BuiltinType::Char16:
            case clang::BuiltinType::Char32:
                return "char";
            case clang::BuiltinType::Short:
            case clang::BuiltinType::UShort:
                return "short";
            case clang::BuiltinType::Int:
            case clang::BuiltinType::UInt:
                return "int";
            case clang::BuiltinType::Long:
            case clang::BuiltinType::ULong:
                return "long";
            case clang::BuiltinType::LongLong:
            case clang::BuiltinType::ULongLong:
                return "longlong";
            case clang::BuiltinType::Float:
                return "float";
            case clang::BuiltinType::Double:
                return "double";
            case clang::BuiltinType::LongDouble:
                return "longdouble";
            default:
                return "unknown";
        }
    }

    // Check for record types (struct/class)
    if (type->isRecordType()) {
        const auto* recordType = llvm::cast<clang::RecordType>(type.getTypePtr());
        const auto* recordDecl = recordType->getDecl();
        return recordDecl->getNameAsString();
    }

    // Check for enum types
    if (type->isEnumeralType()) {
        const auto* enumType = llvm::cast<clang::EnumType>(type.getTypePtr());
        const auto* enumDecl = enumType->getDecl();
        return enumDecl->getNameAsString();
    }

    // Default: use type as string
    return type.getAsString();
}

} // namespace cpptoc
