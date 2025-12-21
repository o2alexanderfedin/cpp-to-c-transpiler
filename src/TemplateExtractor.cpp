/**
 * @file TemplateExtractor.cpp
 * @brief Implementation of TemplateExtractor class
 *
 * Story #67: Template Instantiation Extraction from AST
 */

#include "TemplateExtractor.h"
#include "clang/AST/DeclTemplate.h"
#include "llvm/ADT/SmallString.h"
#include <sstream>

using namespace clang;

TemplateExtractor::TemplateExtractor(ASTContext& Context)
    : Context(Context) {
}

void TemplateExtractor::extractTemplateInstantiations(TranslationUnitDecl* TU) {
    // Traverse the entire AST starting from translation unit
    // RecursiveASTVisitor will call Visit* methods for each node
    TraverseDecl(TU);
}

std::vector<ClassTemplateSpecializationDecl*> TemplateExtractor::getClassInstantiations() const {
    return classInstantiations;
}

std::vector<FunctionDecl*> TemplateExtractor::getFunctionInstantiations() const {
    return functionInstantiations;
}

bool TemplateExtractor::VisitClassTemplateDecl(ClassTemplateDecl* D) {
    // ClassTemplateDecl stores its specializations internally
    // We need to manually iterate through them since RecursiveASTVisitor doesn't do this
    for (auto* Spec : D->specializations()) {
        // Process each specialization
        VisitClassTemplateSpecializationDecl(Spec);
    }
    return true;
}

bool TemplateExtractor::VisitFunctionTemplateDecl(FunctionTemplateDecl* D) {
    // FunctionTemplateDecl stores its specializations internally
    // Similar to ClassTemplateDecl, we need to manually iterate
    for (auto* Spec : D->specializations()) {
        // Process each function specialization
        VisitFunctionDecl(Spec);
    }
    return true;
}

bool TemplateExtractor::VisitClassTemplateSpecializationDecl(ClassTemplateSpecializationDecl* D) {
    // Only process valid template specializations
    if (!D) {
        return true;
    }

    // Accept all template specializations that are used in the code
    // Even TSK_Undeclared specializations are needed when they're used as template arguments
    // Example: Vector<Pair<int, double>> - both Vector and Pair specializations are needed
    TemplateSpecializationKind TSK = D->getSpecializationKind();

    // Only skip forward declarations without any actual usage
    // If a specialization exists in the specializations list, it's being used somewhere
    // Note: Removed the TSK_Undeclared check because nested template arguments
    // create undeclared specializations that are still needed for monomorphization

    // Generate unique key for this instantiation
    std::string key = getClassInstantiationKey(D);

    // Check if we've already seen this instantiation
    if (seenClassInstantiations.find(key) == seenClassInstantiations.end()) {
        // New instantiation - add it
        classInstantiations.push_back(D);
        seenClassInstantiations.insert(key);
    }

    return true;
}

bool TemplateExtractor::VisitFunctionDecl(FunctionDecl* D) {
    // Check if this is a template instantiation
    if (!D || !isFunctionTemplateInstantiation(D)) {
        return true;
    }

    // Generate unique key for this instantiation
    std::string key = getFunctionInstantiationKey(D);

    // Check if we've already seen this instantiation
    if (seenFunctionInstantiations.find(key) == seenFunctionInstantiations.end()) {
        // New instantiation - add it
        functionInstantiations.push_back(D);
        seenFunctionInstantiations.insert(key);
    }

    return true;
}

std::string TemplateExtractor::getClassInstantiationKey(ClassTemplateSpecializationDecl* D) {
    // Generate unique key: TemplateName<arg1, arg2, ...>
    std::ostringstream key;

    // Template name
    key << D->getSpecializedTemplate()->getNameAsString();

    // Template arguments
    const TemplateArgumentList& args = D->getTemplateArgs();
    key << "<";
    for (unsigned i = 0; i < args.size(); ++i) {
        if (i > 0) key << ",";

        const TemplateArgument& arg = args[i];
        switch (arg.getKind()) {
            case TemplateArgument::Type:
                key << arg.getAsType().getAsString();
                break;
            case TemplateArgument::Integral: {
                llvm::SmallString<16> IntStr;
                arg.getAsIntegral().toString(IntStr, 10);
                key << IntStr.str().str();
                break;
            }
            case TemplateArgument::Expression:
                key << "expr";
                break;
            case TemplateArgument::Pack: {
                // Handle parameter packs - expand them inline
                for (unsigned j = 0; j < arg.pack_size(); ++j) {
                    if (i > 0 || j > 0) key << ",";
                    const TemplateArgument& packArg = arg.pack_elements()[j];
                    if (packArg.getKind() == TemplateArgument::Type) {
                        key << packArg.getAsType().getAsString();
                    } else {
                        key << "arg";
                    }
                }
                break;
            }
            default:
                key << "arg";
                break;
        }
    }
    key << ">";

    return key.str();
}

std::string TemplateExtractor::getFunctionInstantiationKey(FunctionDecl* D) {
    // Generate unique key: functionName<arg1, arg2, ...>(param1Type, param2Type, ...)
    std::ostringstream key;

    // Function name
    key << D->getNameAsString();

    // Template arguments (if this is a template instantiation)
    if (FunctionTemplateSpecializationInfo* FTSI = D->getTemplateSpecializationInfo()) {
        const TemplateArgumentList* args = FTSI->TemplateArguments;
        if (args && args->size() > 0) {
            key << "<";
            for (unsigned i = 0; i < args->size(); ++i) {
                if (i > 0) key << ",";

                const TemplateArgument& arg = args->get(i);
                switch (arg.getKind()) {
                    case TemplateArgument::Type:
                        key << arg.getAsType().getAsString();
                        break;
                    case TemplateArgument::Integral: {
                        llvm::SmallString<16> IntStr;
                        arg.getAsIntegral().toString(IntStr, 10);
                        key << IntStr.str().str();
                        break;
                    }
                    case TemplateArgument::Expression:
                        key << "expr";
                        break;
                    case TemplateArgument::Pack: {
                        // Handle parameter packs
                        key << "pack(";
                        for (unsigned j = 0; j < arg.pack_size(); ++j) {
                            if (j > 0) key << ",";
                            const TemplateArgument& packArg = arg.pack_elements()[j];
                            if (packArg.getKind() == TemplateArgument::Type) {
                                key << packArg.getAsType().getAsString();
                            } else {
                                key << "arg";
                            }
                        }
                        key << ")";
                        break;
                    }
                    default:
                        key << "arg";
                        break;
                }
            }
            key << ">";
        }
    }

    // Parameter types
    key << "(";
    for (unsigned i = 0; i < D->getNumParams(); ++i) {
        if (i > 0) key << ",";
        key << D->getParamDecl(i)->getType().getAsString();
    }
    key << ")";

    return key.str();
}

bool TemplateExtractor::isFunctionTemplateInstantiation(FunctionDecl* D) {
    // A function is a template instantiation if:
    // 1. It has template specialization info (explicit or implicit instantiation)
    // 2. It's from a function template specialization kind

    if (FunctionTemplateSpecializationInfo* FTSI = D->getTemplateSpecializationInfo()) {
        // Check if it's an actual instantiation (not the template itself)
        switch (FTSI->getTemplateSpecializationKind()) {
            case TSK_ImplicitInstantiation:
            case TSK_ExplicitInstantiationDefinition:
            case TSK_ExplicitInstantiationDeclaration:
            case TSK_ExplicitSpecialization:
                return true;
            default:
                return false;
        }
    }

    return false;
}
