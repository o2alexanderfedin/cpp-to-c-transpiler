/**
 * @file TemplateMonomorphizer.cpp
 * @brief Implementation of TemplateMonomorphizer class
 *
 * Story #68: Template Monomorphization and Code Generation
 */

#include "TemplateMonomorphizer.h"
#include "llvm/ADT/SmallString.h"
#include <sstream>

using namespace clang;

TemplateMonomorphizer::TemplateMonomorphizer(ASTContext& Context, NameMangler& Mangler)
    : Context(Context), Mangler(Mangler) {
}

std::string TemplateMonomorphizer::monomorphizeClass(ClassTemplateSpecializationDecl* D) {
    if (!D) return "";

    // Generate mangled name for this instantiation
    std::string mangledName = generateMangledName(
        D->getSpecializedTemplate()->getNameAsString(),
        D->getTemplateArgs()
    );

    // Generate struct definition
    std::string result = generateStruct(D, mangledName);

    // Generate method declarations
    for (auto* Decl : D->decls()) {
        if (auto* Method = dyn_cast<CXXMethodDecl>(Decl)) {
            // Skip compiler-generated methods
            if (Method->isImplicit()) continue;

            result += generateMethod(Method, mangledName, D->getTemplateArgs());
        }
    }

    return result;
}

std::string TemplateMonomorphizer::monomorphizeFunction(FunctionDecl* D) {
    if (!D) return "";

    // Get function template specialization info
    FunctionTemplateSpecializationInfo* FTSI = D->getTemplateSpecializationInfo();
    if (!FTSI) return "";

    std::ostringstream code;

    // Return type
    QualType returnType = D->getReturnType();
    code << typeToString(returnType) << " ";

    // Function name with template args
    code << D->getNameAsString();

    // Add template argument suffix
    const TemplateArgumentList* TemplateArgs = FTSI->TemplateArguments;
    if (TemplateArgs && TemplateArgs->size() > 0) {
        code << "_";
        for (unsigned i = 0; i < TemplateArgs->size(); ++i) {
            const TemplateArgument& arg = TemplateArgs->get(i);
            if (arg.getKind() == TemplateArgument::Type) {
                QualType argType = arg.getAsType();
                code << typeToString(argType);
                if (i + 1 < TemplateArgs->size()) code << "_";
            }
        }
    }

    // Parameters
    code << "(";
    for (unsigned i = 0; i < D->getNumParams(); ++i) {
        if (i > 0) code << ", ";
        ParmVarDecl* param = D->getParamDecl(i);
        code << typeToString(param->getType()) << " " << param->getNameAsString();
    }
    code << ");\n";

    return code.str();
}

QualType TemplateMonomorphizer::substituteType(QualType Type,
                                               const TemplateArgumentList& TemplateArgs) {
    // For now, types are already substituted by Clang during instantiation
    // This method is for future enhancements if needed
    return Type;
}

std::string TemplateMonomorphizer::generateStruct(ClassTemplateSpecializationDecl* D,
                                                 const std::string& MangledName) {
    std::ostringstream code;

    code << "typedef struct " << MangledName << " {\n";

    // Generate fields
    for (auto* Field : D->fields()) {
        code << "    ";

        // Field type (already substituted by Clang)
        QualType fieldType = Field->getType();

        // Handle arrays - get element type first
        if (fieldType->isConstantArrayType()) {
            const ConstantArrayType* arrayType = Context.getAsConstantArrayType(fieldType);
            if (arrayType) {
                // Get element type (e.g., int from int[10])
                QualType elementType = arrayType->getElementType();
                code << typeToString(elementType);
                code << " " << Field->getNameAsString();
                code << "[" << arrayType->getSize().getZExtValue() << "]";
            }
        } else {
            // Non-array types
            code << typeToString(fieldType);
            code << " " << Field->getNameAsString();
        }

        code << ";\n";
    }

    code << "} " << MangledName << ";\n\n";

    return code.str();
}

std::string TemplateMonomorphizer::generateMethod(CXXMethodDecl* Method,
                                                 const std::string& ClassName,
                                                 const TemplateArgumentList& TemplateArgs) {
    std::ostringstream code;

    // Return type (already substituted by Clang)
    QualType returnType = Method->getReturnType();
    code << typeToString(returnType) << " ";

    // Method name: ClassName_methodName
    code << ClassName << "_" << Method->getNameAsString();

    // Parameters (with 'this' pointer)
    code << "(" << ClassName << "* this";

    for (unsigned i = 0; i < Method->getNumParams(); ++i) {
        code << ", ";
        ParmVarDecl* param = Method->getParamDecl(i);

        // Parameter type (already substituted by Clang)
        QualType paramType = param->getType();
        code << typeToString(paramType);

        code << " " << param->getNameAsString();
    }

    code << ");\n";

    return code.str();
}

std::string TemplateMonomorphizer::typeToString(QualType Type) {
    // Handle references as pointers in C
    if (Type->isReferenceType()) {
        QualType pointeeType = Type->getPointeeType();
        return typeToString(pointeeType) + "*";
    }

    // Get canonical type string
    std::string typeStr = Type.getAsString();

    // Clean up type string for C
    // Remove "class " prefix
    size_t classPos = typeStr.find("class ");
    if (classPos != std::string::npos) {
        typeStr.erase(classPos, 6);
    }

    // Remove "struct " prefix
    size_t structPos = typeStr.find("struct ");
    if (structPos != std::string::npos) {
        typeStr.erase(structPos, 7);
    }

    // Normalize pointer spacing: "int *" -> "int*", "int **" -> "int**"
    size_t pos = 0;
    while ((pos = typeStr.find(" *", pos)) != std::string::npos) {
        typeStr.erase(pos, 1);  // Remove the space before *
    }

    return typeStr;
}

std::string TemplateMonomorphizer::typeToIdentifierString(QualType Type) {
    // Convert type to valid C identifier component (no *, <, >, ::, etc.)

    // Handle references as pointers in C
    if (Type->isReferenceType()) {
        QualType pointeeType = Type->getPointeeType();
        return typeToIdentifierString(pointeeType) + "_ref";
    }

    // Handle pointer types recursively
    if (Type->isPointerType()) {
        QualType pointeeType = Type->getPointeeType();
        return typeToIdentifierString(pointeeType) + "_ptr";
    }

    // Get canonical type
    QualType canonicalType = Type.getCanonicalType();

    // Handle builtin types
    if (const BuiltinType* BT = canonicalType->getAs<BuiltinType>()) {
        switch (BT->getKind()) {
            case BuiltinType::Void: return "void";
            case BuiltinType::Bool: return "bool";
            case BuiltinType::Char_S:
            case BuiltinType::Char_U: return "char";
            case BuiltinType::SChar: return "schar";
            case BuiltinType::UChar: return "uchar";
            case BuiltinType::Short: return "short";
            case BuiltinType::UShort: return "ushort";
            case BuiltinType::Int: return "int";
            case BuiltinType::UInt: return "uint";
            case BuiltinType::Long: return "long";
            case BuiltinType::ULong: return "ulong";
            case BuiltinType::LongLong: return "llong";
            case BuiltinType::ULongLong: return "ullong";
            case BuiltinType::Float: return "float";
            case BuiltinType::Double: return "double";
            case BuiltinType::LongDouble: return "ldouble";
            default: break;
        }
    }

    // For record types (struct/class), use the simple name
    if (const RecordType* RT = canonicalType->getAs<RecordType>()) {
        RecordDecl* RD = RT->getDecl();
        return RD->getNameAsString();
    }

    // Fallback: get type string and sanitize it
    std::string typeStr = canonicalType.getAsString();

    // Remove "class " and "struct " prefixes
    size_t classPos = typeStr.find("class ");
    if (classPos != std::string::npos) {
        typeStr.erase(classPos, 6);
    }
    size_t structPos = typeStr.find("struct ");
    if (structPos != std::string::npos) {
        typeStr.erase(structPos, 7);
    }

    // Replace invalid identifier characters with underscores
    for (char& c : typeStr) {
        if (!std::isalnum(c) && c != '_') {
            c = '_';
        }
    }

    return typeStr;
}

std::string TemplateMonomorphizer::generateMangledName(const std::string& BaseName,
                                                      const TemplateArgumentList& TemplateArgs) {
    std::ostringstream name;
    name << BaseName;

    // Append template arguments
    for (unsigned i = 0; i < TemplateArgs.size(); ++i) {
        const TemplateArgument& arg = TemplateArgs[i];
        name << "_";

        switch (arg.getKind()) {
            case TemplateArgument::Type: {
                QualType argType = arg.getAsType();
                // Use typeToIdentifierString instead of typeToString for valid C identifiers
                name << typeToIdentifierString(argType);
                break;
            }
            case TemplateArgument::Integral: {
                llvm::SmallString<16> IntStr;
                arg.getAsIntegral().toString(IntStr, 10);
                name << IntStr.str().str();
                break;
            }
            case TemplateArgument::Expression:
                name << "expr";
                break;
            default:
                name << "arg";
                break;
        }
    }

    return name.str();
}
