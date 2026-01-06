/**
 * @file VtableTypedefGenerator.cpp
 * @brief Implementation of VtableTypedefGenerator
 *
 * Generates strongly-typed function pointer typedefs for COM-style vtables.
 * Maintains type safety by avoiding void* pointers.
 */

#include "helpers/VtableTypedefGenerator.h"
#include "clang/AST/RecordLayout.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace cpptoc;

TypedefDecl* VtableTypedefGenerator::generateTypedef(
    const CXXMethodDecl *Method,
    llvm::StringRef ClassName) {

    if (!Method) {
        return nullptr;
    }

    // Build return type (convert to C)
    QualType returnType = convertTypeToC(Method->getReturnType());

    // Build parameter types
    llvm::SmallVector<QualType, 8> paramTypes;

    // First parameter: this (struct ClassName *this or const struct ClassName *this)
    bool isConst = Method->isConst();
    QualType thisType = buildThisParameterType(ClassName, isConst);
    paramTypes.push_back(thisType);

    // Add method parameters (converted to C)
    for (unsigned i = 0; i < Method->getNumParams(); ++i) {
        const ParmVarDecl *Param = Method->getParamDecl(i);
        QualType paramType = convertTypeToC(Param->getType());
        paramTypes.push_back(paramType);
    }

    // Build function pointer type: RetType (*)(Params)
    QualType funcPtrType = buildFunctionPointerType(returnType, paramTypes);

    // Generate typedef name: ClassName_methodName_fn
    std::string typedefName = generateTypedefName(ClassName, Method->getNameAsString());

    // Create TypedefDecl
    IdentifierInfo &II = C_Ctx.Idents.get(typedefName);
    TypeSourceInfo *TInfo = C_Ctx.getTrivialTypeSourceInfo(funcPtrType);

    TypedefDecl *TD = TypedefDecl::Create(
        C_Ctx,
        C_Ctx.getTranslationUnitDecl(),
        SourceLocation(),
        SourceLocation(),
        &II,
        TInfo
    );

    // Add to translation unit
    C_Ctx.getTranslationUnitDecl()->addDecl(TD);

    return TD;
}

TypedefDecl* VtableTypedefGenerator::generateTypedefForDestructor(
    const CXXDestructorDecl *Dtor,
    llvm::StringRef ClassName) {

    if (!Dtor) {
        return nullptr;
    }

    // Destructor signature: void (struct ClassName *this)
    QualType returnType = C_Ctx.VoidTy;

    // Build parameter: this (non-const for destructor)
    llvm::SmallVector<QualType, 1> paramTypes;
    QualType thisType = buildThisParameterType(ClassName, false);
    paramTypes.push_back(thisType);

    // Build function pointer type
    QualType funcPtrType = buildFunctionPointerType(returnType, paramTypes);

    // Generate typedef name: ClassName_destructor_fn
    std::string typedefName = generateTypedefName(ClassName, "destructor");

    // Create TypedefDecl
    IdentifierInfo &II = C_Ctx.Idents.get(typedefName);
    TypeSourceInfo *TInfo = C_Ctx.getTrivialTypeSourceInfo(funcPtrType);

    TypedefDecl *TD = TypedefDecl::Create(
        C_Ctx,
        C_Ctx.getTranslationUnitDecl(),
        SourceLocation(),
        SourceLocation(),
        &II,
        TInfo
    );

    // Add to translation unit
    C_Ctx.getTranslationUnitDecl()->addDecl(TD);

    return TD;
}

QualType VtableTypedefGenerator::buildFunctionPointerType(
    QualType ReturnType,
    llvm::ArrayRef<QualType> ParamTypes) {

    // Create function prototype type
    FunctionProtoType::ExtProtoInfo EPI;
    QualType funcType = C_Ctx.getFunctionType(ReturnType, ParamTypes, EPI);

    // Wrap in pointer type
    QualType funcPtrType = C_Ctx.getPointerType(funcType);

    return funcPtrType;
}

QualType VtableTypedefGenerator::convertTypeToC(QualType CppType) {
    // Handle references → pointers
    if (CppType->isReferenceType()) {
        QualType pointeeType = CppType->getPointeeType();

        // Preserve const qualification
        if (pointeeType.isConstQualified()) {
            QualType nonConstPointee = pointeeType.getUnqualifiedType();
            QualType ptrType = C_Ctx.getPointerType(nonConstPointee);
            return C_Ctx.getConstType(ptrType.withConst());
        }

        return C_Ctx.getPointerType(pointeeType);
    }

    // Handle class types → we'll use the type as-is since it will be
    // converted to struct type during full translation
    // For now, just return the type (it will be struct in C AST)

    return CppType;
}

QualType VtableTypedefGenerator::buildThisParameterType(
    llvm::StringRef ClassName,
    bool IsConst) {

    // Create struct type: struct ClassName
    // We need to create or find the RecordDecl for this struct

    // For now, create a simple struct type
    // In full implementation, this would look up the actual C struct

    IdentifierInfo &II = C_Ctx.Idents.get(ClassName);

    // Try to find existing RecordDecl in C translation unit
    RecordDecl *RD = nullptr;

    // Search for existing struct declaration
    DeclContext *DC = C_Ctx.getTranslationUnitDecl();
    for (auto *D : DC->decls()) {
        if (auto *Record = dyn_cast<RecordDecl>(D)) {
            if (Record->getName() == ClassName) {
                RD = Record;
                break;
            }
        }
    }

    // If not found, create a new forward declaration
    if (!RD) {
        RD = RecordDecl::Create(
            C_Ctx,
            TagTypeKind::Struct,
            C_Ctx.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            &II
        );
        C_Ctx.getTranslationUnitDecl()->addDecl(RD);
    }

    // Create struct type
    QualType structType = C_Ctx.getRecordType(RD);

    // Apply const if needed
    if (IsConst) {
        structType = C_Ctx.getConstType(structType);
    }

    // Create pointer to struct
    QualType ptrType = C_Ctx.getPointerType(structType);

    return ptrType;
}

std::string VtableTypedefGenerator::generateTypedefName(
    llvm::StringRef ClassName,
    llvm::StringRef MethodName) {

    // Pattern: ClassName_methodName_fn
    std::string name;
    llvm::raw_string_ostream OS(name);
    OS << ClassName << "_" << MethodName << "_fn";
    return OS.str();
}
