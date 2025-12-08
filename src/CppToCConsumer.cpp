#include "CppToCConsumer.h"
#include "CppToCVisitor.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>

void CppToCConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
  // Get source manager and main file information
  auto &SM = Context.getSourceManager();
  auto MainFileID = SM.getMainFileID();

  // Print parsed file name for verification
  if (auto FileEntry = SM.getFileEntryRefForID(MainFileID)) {
    llvm::outs() << "Parsed file: " << FileEntry->getName() << "\n";
  }

  // Count top-level declarations in translation unit
  // Using std::distance for more idiomatic C++ (DRY principle)
  auto *TU = Context.getTranslationUnitDecl();
  auto DeclRange = TU->decls();
  auto DeclCount = std::distance(DeclRange.begin(), DeclRange.end());

  llvm::outs() << "Translation unit has " << DeclCount
               << " top-level declarations\n";

  // Create and run visitor to traverse AST
  CppToCVisitor Visitor(Context);
  Visitor.TraverseDecl(TU);
}
