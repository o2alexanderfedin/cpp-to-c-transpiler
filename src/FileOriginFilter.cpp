#include "FileOriginFilter.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/Support/raw_ostream.h"

using namespace clang;
using namespace cpptoc;

FileOriginFilter::FileOriginFilter(FileOriginTracker& tracker, const std::string& currentFile)
    : tracker_(tracker), currentFile_(currentFile) {}

bool FileOriginFilter::shouldProcess(const Decl* D) const {
  if (!D) {
    return false;
  }

  // Use existing tracker for basic check
  if (!tracker_.shouldTranspile(D)) {
    return false;
  }

  // Dispatch to specialized handlers
  if (const CXXMethodDecl* MD = dyn_cast<CXXMethodDecl>(D)) {
    return shouldProcessMethod(MD);
  }

  if (const EnumDecl* ED = dyn_cast<EnumDecl>(D)) {
    return shouldProcessEnum(ED);
  }

  if (const CXXRecordDecl* RD = dyn_cast<CXXRecordDecl>(D)) {
    return shouldProcessClass(RD);
  }

  // Default: use tracker's decision
  return true;
}

bool FileOriginFilter::shouldProcessMethod(const CXXMethodDecl* MD) const {
  if (!MD) {
    return false;
  }

  // KEY FIX for Bug #43: Check where the method BODY is defined, not just the declaration
  // When processing main.cpp, we should NOT process methods defined in StateMachine.cpp
  // even if they're declared in StateMachine.h which is included by main.cpp

  // If method has no body (declaration only), process if declaration is in current file's headers
  if (!MD->hasBody()) {
    return tracker_.shouldTranspile(MD);
  }

  // Method has a body - check where the DEFINITION is located
  std::string defFile = getDefinitionFile(MD);
  if (defFile.empty()) {
    // No definition found, fall back to tracker
    return tracker_.shouldTranspile(MD);
  }

  // Only process if definition is in the current source file we're translating
  // This ensures method bodies end up in the correct .c file
  bool shouldProcess = defFile.find(currentFile_) != std::string::npos;

  if (!shouldProcess) {
    llvm::outs() << "[FileOriginFilter] Skipping method " << MD->getQualifiedNameAsString()
                 << " - defined in " << defFile << ", current file is " << currentFile_ << "\n";
  }

  return shouldProcess;
}

bool FileOriginFilter::shouldProcessEnum(const EnumDecl* ED) const {
  if (!ED) {
    return false;
  }

  // Enums are usually in headers, process if tracker approves
  return tracker_.shouldTranspile(ED);
}

bool FileOriginFilter::shouldProcessClass(const CXXRecordDecl* RD) const {
  if (!RD) {
    return false;
  }

  // Classes are usually in headers, process if tracker approves
  return tracker_.shouldTranspile(RD);
}

std::string FileOriginFilter::getDefinitionFile(const Decl* D) const {
  if (!D) {
    return "";
  }

  // For methods, get the definition (not just declaration)
  if (const FunctionDecl* FD = dyn_cast<FunctionDecl>(D)) {
    const FunctionDecl* Def = FD->getDefinition();
    if (Def) {
      SourceManager& SM = Def->getASTContext().getSourceManager();
      SourceLocation Loc = Def->getLocation();
      if (Loc.isValid()) {
        return SM.getFilename(Loc).str();
      }
    }
  }

  return "";
}
