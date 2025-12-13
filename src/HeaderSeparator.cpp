#include "HeaderSeparator.h"
#include "clang/AST/Type.h"

void HeaderSeparator::analyzeTranslationUnit(clang::TranslationUnitDecl *TU) {
    // KISS: Just traverse the AST using RecursiveASTVisitor
    TraverseDecl(TU);
}

bool HeaderSeparator::VisitRecordDecl(clang::RecordDecl *D) {
    // YAGNI: Only handle complete definitions for now
    // Incomplete declarations are forward declarations
    if (D->isCompleteDefinition()) {
        // Analyze fields for forward declaration needs (Story #139)
        analyzeForwardDecls(D);

        headerDecls.push_back(D);
    }
    return true;  // Continue traversal
}

void HeaderSeparator::analyzeForwardDecls(clang::RecordDecl *D) {
    // Iterate through all fields looking for pointers to other structs
    for (auto *Field : D->fields()) {
        clang::QualType fieldType = Field->getType();

        // Check if this is a pointer type
        if (fieldType->isPointerType()) {
            // Get the pointee type (what the pointer points to)
            clang::QualType pointeeType = fieldType->getPointeeType();

            // Check if it's a pointer to a struct/class
            if (const clang::RecordType *RT = pointeeType->getAs<clang::RecordType>()) {
                clang::RecordDecl *PointedToRecord = RT->getDecl();

                // Add to forward declarations set
                // (set automatically handles duplicates)
                forwardDecls.insert(PointedToRecord->getNameAsString());
            }
        }
    }
}

bool HeaderSeparator::VisitFunctionDecl(clang::FunctionDecl *D) {
    if (D->hasBody()) {
        // Function definition: goes to implementation file
        implDecls.push_back(D);

        // Also add to header for declaration
        // (Code generator will print signature only in .h, full body in .c)
        headerDecls.push_back(D);
    } else {
        // Function declaration only: goes to header
        headerDecls.push_back(D);
    }
    return true;  // Continue traversal
}
