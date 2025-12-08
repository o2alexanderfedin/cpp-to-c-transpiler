#include "HeaderSeparator.h"

void HeaderSeparator::analyzeTranslationUnit(clang::TranslationUnitDecl *TU) {
    // KISS: Just traverse the AST using RecursiveASTVisitor
    TraverseDecl(TU);
}

bool HeaderSeparator::VisitRecordDecl(clang::RecordDecl *D) {
    // YAGNI: Only handle complete definitions for now
    // Incomplete declarations (forward decls) handled in Story #139
    if (D->isCompleteDefinition()) {
        headerDecls.push_back(D);
    }
    return true;  // Continue traversal
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
