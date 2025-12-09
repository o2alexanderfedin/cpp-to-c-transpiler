/**
 * @file OverrideResolver.cpp
 * @brief Implementation of Story #170: Virtual Function Override Resolution
 */

#include "OverrideResolver.h"
#include "clang/AST/DeclCXX.h"
#include <sstream>

using namespace clang;

OverrideResolver::OverrideResolver(ASTContext& Context, VirtualMethodAnalyzer& Analyzer)
    : Context(Context), Analyzer(Analyzer) {}

std::vector<CXXMethodDecl*> OverrideResolver::resolveVtableLayout(const CXXRecordDecl* Record) {
    std::vector<CXXMethodDecl*> vtableLayout;

    if (!Record || !Analyzer.isPolymorphic(Record)) {
        return vtableLayout;
    }

    // Map of method signature -> vtable slot
    std::map<std::string, VtableSlot> slots;
    unsigned slotIndex = 0;

    // Collect all virtual methods from hierarchy
    collectVirtualMethods(Record, slots, slotIndex);

    // Convert map to ordered vector
    // Sort by slot index to maintain order
    std::vector<std::pair<unsigned, CXXMethodDecl*>> sortedMethods;

    for (const auto& pair : slots) {
        sortedMethods.push_back({pair.second.slotIndex, pair.second.method});
    }

    // Sort by slot index
    std::sort(sortedMethods.begin(), sortedMethods.end(),
              [](const auto& a, const auto& b) { return a.first < b.first; });

    // Extract methods
    for (const auto& pair : sortedMethods) {
        vtableLayout.push_back(pair.second);
    }

    return vtableLayout;
}

bool OverrideResolver::isOverride(const CXXMethodDecl* Method,
                                   const CXXMethodDecl* BaseMethod) const {
    if (!Method || !BaseMethod) {
        return false;
    }

    // Check if both are virtual
    if (!Method->isVirtual() || !BaseMethod->isVirtual()) {
        return false;
    }

    // Check if signatures match
    return getMethodSignature(Method) == getMethodSignature(BaseMethod);
}

std::string OverrideResolver::getMethodSignature(const CXXMethodDecl* Method) const {
    if (!Method) {
        return "";
    }

    std::ostringstream sig;

    // Special handling for destructors
    if (isa<CXXDestructorDecl>(Method)) {
        sig << "~destructor";
        return sig.str();
    }

    // Method name
    sig << Method->getNameAsString();

    // Parameter types
    sig << "(";
    for (unsigned i = 0; i < Method->getNumParams(); ++i) {
        if (i > 0) sig << ",";
        sig << getTypeSignature(Method->getParamDecl(i)->getType());
    }
    sig << ")";

    // Const qualifier
    if (Method->isConst()) {
        sig << " const";
    }

    return sig.str();
}

void OverrideResolver::collectVirtualMethods(const CXXRecordDecl* Record,
                                              std::map<std::string, VtableSlot>& slots,
                                              unsigned& slotIndex) {
    if (!Record) {
        return;
    }

    // Process base classes first (depth-first)
    for (const auto& Base : Record->bases()) {
        if (const auto* BaseRecord = Base.getType()->getAsCXXRecordDecl()) {
            collectVirtualMethods(BaseRecord, slots, slotIndex);
        }
    }

    // Process virtual methods in this class
    for (auto* method : Record->methods()) {
        if (!method->isVirtual()) {
            continue;
        }

        std::string signature = getMethodSignature(method);

        // Check if this method overrides a base method
        auto it = slots.find(signature);
        if (it != slots.end()) {
            // Override: replace base implementation with derived
            it->second.method = method;
            // Keep the original slot index (maintain slot consistency)
        } else {
            // New virtual method: add new slot
            VtableSlot slot;
            slot.signature = signature;
            slot.method = method;
            slot.slotIndex = slotIndex++;
            slots[signature] = slot;
        }
    }
}

std::string OverrideResolver::getTypeSignature(QualType Type) const {
    std::ostringstream sig;

    // Remove qualifiers for signature matching
    Type = Type.getUnqualifiedType();

    const clang::Type* T = Type.getTypePtr();

    if (T->isVoidType()) {
        sig << "void";
    } else if (T->isBooleanType()) {
        sig << "bool";
    } else if (T->isIntegerType()) {
        if (const BuiltinType* BT = T->getAs<BuiltinType>()) {
            switch (BT->getKind()) {
                case BuiltinType::Char_S:
                case BuiltinType::Char_U:
                    sig << "char";
                    break;
                case BuiltinType::Short:
                    sig << "short";
                    break;
                case BuiltinType::Int:
                    sig << "int";
                    break;
                case BuiltinType::Long:
                    sig << "long";
                    break;
                case BuiltinType::LongLong:
                    sig << "long long";
                    break;
                case BuiltinType::UShort:
                    sig << "unsigned short";
                    break;
                case BuiltinType::UInt:
                    sig << "unsigned int";
                    break;
                case BuiltinType::ULong:
                    sig << "unsigned long";
                    break;
                case BuiltinType::ULongLong:
                    sig << "unsigned long long";
                    break;
                default:
                    sig << "int";
                    break;
            }
        } else {
            sig << "int";
        }
    } else if (T->isFloatingType()) {
        if (T->isSpecificBuiltinType(BuiltinType::Float)) {
            sig << "float";
        } else if (T->isSpecificBuiltinType(BuiltinType::Double)) {
            sig << "double";
        } else {
            sig << "double";
        }
    } else if (T->isPointerType()) {
        QualType pointeeType = T->getPointeeType();
        sig << getTypeSignature(pointeeType) << "*";
    } else if (T->isReferenceType()) {
        QualType refType = T->getPointeeType();
        sig << getTypeSignature(refType) << "&";
    } else if (const RecordType* RT = T->getAs<RecordType>()) {
        RecordDecl* RD = RT->getDecl();
        sig << RD->getQualifiedNameAsString();
    } else {
        // Fallback: use type as string
        sig << Type.getAsString();
    }

    return sig.str();
}
