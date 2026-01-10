/**
 * @file MultipleInheritanceAnalyzer.cpp
 * @brief Implementation of MultipleInheritanceAnalyzer
 *
 * Phase 46, Group 1, Task 1: Base Class Analysis
 */

#include "MultipleInheritanceAnalyzer.h"
#include "clang/AST/RecordLayout.h"
#include <sstream>

using namespace clang;

MultipleInheritanceAnalyzer::MultipleInheritanceAnalyzer(ASTContext& Context)
    : Context(Context) {}

std::vector<MultipleInheritanceAnalyzer::BaseInfo>
MultipleInheritanceAnalyzer::analyzePolymorphicBases(const CXXRecordDecl* Record) {
    std::vector<BaseInfo> result;

    if (!Record || !Record->isCompleteDefinition()) {
        return result;
    }

    unsigned vtblIndex = 0;
    bool foundPrimary = false;

    // Iterate through direct bases in declaration order
    for (const auto& Base : Record->bases()) {
        const CXXRecordDecl* BaseRecord = Base.getType()->getAsCXXRecordDecl();

        // Safety check: skip null base records
        if (!BaseRecord) {
            continue;
        }

        if (!isPolymorphicBase(BaseRecord)) {
            continue;
        }

        BaseInfo info;
        info.BaseDecl = BaseRecord;
        info.IsPrimary = !foundPrimary;  // First polymorphic base is primary
        info.VtblIndex = vtblIndex;
        info.VtblFieldName = getVtblFieldName(vtblIndex);

        // CRITICAL FIX: Primary base always has offset 0
        // Only calculate offset for non-primary bases to avoid ASTRecordLayout issues
        if (info.IsPrimary) {
            info.Offset = 0;
        } else {
            info.Offset = calculateBaseOffset(Record, BaseRecord);
        }

        result.push_back(info);

        foundPrimary = true;
        vtblIndex++;
    }

    return result;
}

const CXXRecordDecl*
MultipleInheritanceAnalyzer::getPrimaryBase(const CXXRecordDecl* Record) {
    if (!Record || !Record->isCompleteDefinition()) {
        return nullptr;
    }

    // Primary base is the first polymorphic base
    for (const auto& Base : Record->bases()) {
        const CXXRecordDecl* BaseRecord = Base.getType()->getAsCXXRecordDecl();

        if (BaseRecord && isPolymorphicBase(BaseRecord)) {
            return BaseRecord;
        }
    }

    return nullptr;
}

std::vector<const CXXRecordDecl*>
MultipleInheritanceAnalyzer::getNonPrimaryBases(const CXXRecordDecl* Record) {
    std::vector<const CXXRecordDecl*> result;

    if (!Record || !Record->isCompleteDefinition()) {
        return result;
    }

    bool foundPrimary = false;

    // Iterate through bases, skipping the first polymorphic one (primary)
    for (const auto& Base : Record->bases()) {
        const CXXRecordDecl* BaseRecord = Base.getType()->getAsCXXRecordDecl();

        if (!BaseRecord || !isPolymorphicBase(BaseRecord)) {
            continue;
        }

        if (!foundPrimary) {
            foundPrimary = true;
            continue;  // Skip primary base
        }

        result.push_back(BaseRecord);
    }

    return result;
}

unsigned MultipleInheritanceAnalyzer::calculateBaseOffset(
    const CXXRecordDecl* Derived,
    const CXXRecordDecl* Base) {

    // Safety checks
    if (!Derived || !Base || !Derived->isCompleteDefinition()) {
        return 0;
    }

    if (!Base->isCompleteDefinition()) {
        return 0;
    }

    // Check if Base is actually a base of Derived
    // CRITICAL: Skip virtual bases - they don't have fixed offsets in BaseOffsets
    bool isBase = false;
    bool isVirtual = false;
    for (const auto& B : Derived->bases()) {
        if (B.getType()->getAsCXXRecordDecl() == Base) {
            isBase = true;
            isVirtual = B.isVirtual();
            break;
        }
    }

    if (!isBase || isVirtual) {
        return 0;  // Virtual bases use VBaseOffsets, not BaseOffsets
    }

    // CRITICAL: Use definition pointers to avoid ASTRecordLayout issues
    const CXXRecordDecl* DerivedDef = Derived->getDefinition();
    if (!DerivedDef) {
        return 0;
    }

    const CXXRecordDecl* BaseDef = Base->getDefinition();
    if (!BaseDef) {
        return 0;
    }

    // Use Clang's ASTRecordLayout to get base class offset
    const ASTRecordLayout& Layout = Context.getASTRecordLayout(DerivedDef);
    CharUnits Offset = Layout.getBaseClassOffset(BaseDef);

    return static_cast<unsigned>(Offset.getQuantity());
}

bool MultipleInheritanceAnalyzer::hasMultiplePolymorphicBases(
    const CXXRecordDecl* Record) {

    if (!Record || !Record->isCompleteDefinition()) {
        return false;
    }

    unsigned count = 0;

    for (const auto& Base : Record->bases()) {
        const CXXRecordDecl* BaseRecord = Base.getType()->getAsCXXRecordDecl();

        if (BaseRecord && isPolymorphicBase(BaseRecord)) {
            count++;
            if (count >= 2) {
                return true;
            }
        }
    }

    return false;
}

std::string MultipleInheritanceAnalyzer::getVtblFieldName(unsigned Index) {
    if (Index == 0) {
        return "lpVtbl";
    }

    std::ostringstream oss;
    oss << "lpVtbl" << (Index + 1);
    return oss.str();
}

bool MultipleInheritanceAnalyzer::isPolymorphicBase(const CXXRecordDecl* Base) {
    if (!Base || !Base->isCompleteDefinition()) {
        return false;
    }

    // A base is polymorphic if it has virtual methods
    return Base->isPolymorphic();
}
