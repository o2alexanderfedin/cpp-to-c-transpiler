/**
 * @file BaseOffsetCalculator.cpp
 * @brief Implementation of BaseOffsetCalculator
 *
 * Phase 46, Group 2, Task 4: Base Offset Calculator
 */

#include "BaseOffsetCalculator.h"
#include "clang/AST/RecordLayout.h"

using namespace clang;

BaseOffsetCalculator::BaseOffsetCalculator(ASTContext& Context)
    : Context(Context) {}

uint64_t BaseOffsetCalculator::getBaseOffset(
    const CXXRecordDecl* Derived,
    const CXXRecordDecl* Base) {

    if (!Derived || !Base || !Derived->isCompleteDefinition()) {
        return 0;
    }

    // Check if Base is actually a direct base of Derived
    bool isDirectBase = false;
    for (const auto& B : Derived->bases()) {
        if (B.getType()->getAsCXXRecordDecl() == Base) {
            isDirectBase = true;
            break;
        }
    }

    if (!isDirectBase) {
        return 0;
    }

    // Use Clang's ASTRecordLayout to get base class offset
    const ASTRecordLayout& Layout = Context.getASTRecordLayout(Derived);

    // Get offset for this base
    CharUnits Offset = Layout.getBaseClassOffset(Base);

    return static_cast<uint64_t>(Offset.getQuantity());
}

uint64_t BaseOffsetCalculator::getLpVtblFieldOffset(
    const CXXRecordDecl* Derived,
    const CXXRecordDecl* Base) {

    // For direct inheritance, the lpVtbl field offset is the same as the base offset
    // This is because the lpVtbl pointer is the first member of each base subobject
    return getBaseOffset(Derived, Base);
}

bool BaseOffsetCalculator::isPrimaryBase(
    const CXXRecordDecl* Derived,
    const CXXRecordDecl* Base) {

    if (!Derived || !Base || !Derived->isCompleteDefinition()) {
        return false;
    }

    // The primary base is the first polymorphic base class
    for (const auto& B : Derived->bases()) {
        const CXXRecordDecl* BaseRecord = B.getType()->getAsCXXRecordDecl();

        if (!BaseRecord || !isPolymorphicBase(BaseRecord)) {
            continue;
        }

        // First polymorphic base found
        return BaseRecord == Base;
    }

    return false;
}

bool BaseOffsetCalculator::isPolymorphicBase(const CXXRecordDecl* Base) {
    if (!Base || !Base->isCompleteDefinition()) {
        return false;
    }

    // A base is polymorphic if it has virtual methods
    return Base->isPolymorphic();
}
