#include "CppToCVisitor.h"
#include "llvm/Support/raw_ostream.h"

bool CppToCVisitor::VisitCXXRecordDecl(clang::CXXRecordDecl *D) {
  // Only process complete class definitions (not forward declarations)
  if (!D->isCompleteDefinition())
    return true;

  llvm::outs() << "Found class: " << D->getNameAsString() << "\n";
  return true;
}

bool CppToCVisitor::VisitCXXMethodDecl(clang::CXXMethodDecl *MD) {
  llvm::outs() << "Found method: " << MD->getQualifiedNameAsString() << "\n";
  return true;
}

bool CppToCVisitor::VisitVarDecl(clang::VarDecl *VD) {
  llvm::outs() << "Found variable: " << VD->getNameAsString() << "\n";
  return true;
}
