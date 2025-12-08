#include "CppToCConsumer.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/Support/raw_ostream.h"

void CppToCConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
  auto &SM = Context.getSourceManager();
  auto MainFileID = SM.getMainFileID();

  // Get filename and print confirmation
  auto FileEntry = SM.getFileEntryRefForID(MainFileID);
  if (FileEntry) {
    llvm::outs() << "Parsed file: " << FileEntry->getName() << "\n";
  }

  // Count and print top-level declarations
  auto TU = Context.getTranslationUnitDecl();
  unsigned DeclCount = 0;
  for (auto *D : TU->decls()) {
    DeclCount++;
  }

  llvm::outs() << "Translation unit has " << DeclCount
               << " top-level declarations\n";
}
