#include "CppToCConsumer.h"
#include "CNodeBuilder.h"
#include "CppToCVisitor.h"
#include "CodeGenerator.h"
#include "FileOutputManager.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <sstream>
#include <atomic>

// External accessor for output directory (defined in main.cpp)
extern std::string getOutputDir();

// Global counter for successfully generated files
// This allows main() to return success even if there were parse errors
extern std::atomic<int> g_filesGeneratedCount;

void CppToCConsumer::HandleTranslationUnit(clang::ASTContext &Context) {
  // Get source manager and main file information
  auto &SM = Context.getSourceManager();
  auto MainFileID = SM.getMainFileID();

  // Print parsed file name for verification
  if (auto FileEntry = SM.getFileEntryRefForID(MainFileID)) {
    llvm::outs() << "Parsed file: " << FileEntry->getName() << "\n";
  }

  // Phase 34 (v2.5.0): Configure user header paths for multi-file transpilation
  // Auto-detect common project header directories
  fileOriginTracker.addUserHeaderPath(".");
  fileOriginTracker.addUserHeaderPath("include/");
  fileOriginTracker.addUserHeaderPath("src/");
  fileOriginTracker.addUserHeaderPath("tests/");
  llvm::outs() << "FileOriginTracker configured with user header paths\n";

  // Count top-level declarations in translation unit
  // Using std::distance for more idiomatic C++ (DRY principle)
  auto *TU = Context.getTranslationUnitDecl();
  auto DeclRange = TU->decls();
  auto DeclCount = std::distance(DeclRange.begin(), DeclRange.end());

  llvm::outs() << "Translation unit has " << DeclCount
               << " top-level declarations\n";

  // Create CNodeBuilder for C AST construction (Epic #3)
  clang::CNodeBuilder Builder(Context);

  // Create and run visitor to traverse AST
  // Phase 34: Pass FileOriginTracker to visitor for multi-file support
  CppToCVisitor Visitor(Context, Builder, fileOriginTracker);
  Visitor.TraverseDecl(TU);

  // Phase 11 (v2.4.0): Process template instantiations after AST traversal
  // This generates monomorphized C code for all template instantiations
  Visitor.processTemplateInstantiations(TU);

  // Phase 32 (v3.0.0): Get C TranslationUnit for output generation
  // This fixes the bug where C++ AST was being printed instead of C AST
  clang::TranslationUnitDecl* C_TU = Visitor.getCTranslationUnit();

  // Validate that C TranslationUnit has declarations
  auto CTU_DeclCount = std::distance(C_TU->decls().begin(), C_TU->decls().end());
  llvm::outs() << "C TranslationUnit has " << CTU_DeclCount
               << " generated declarations\n";

  if (CTU_DeclCount == 0) {
    llvm::errs() << "Warning: No C AST nodes generated. "
                 << "Input may contain unsupported C++ features.\n";
  }

  // Generate C code using CodeGenerator
  // Use string streams to collect header and implementation output
  std::string headerContent;
  std::string implContent;
  llvm::raw_string_ostream headerOS(headerContent);
  llvm::raw_string_ostream implOS(implContent);

  CodeGenerator headerGen(headerOS, Context);
  CodeGenerator implGen(implOS, Context);

  // Generate header file (.h) - declarations only
  headerOS << "// Generated from: " << InputFilename << "\n";
  headerOS << "// Header file\n\n";

  // Add standard C headers that are commonly needed
  // These replace C++ headers like <cstdio>, <cmath>, etc.
  headerOS << "#include <stdio.h>\n";
  headerOS << "#include <stdlib.h>\n";
  headerOS << "#include <string.h>\n";
  headerOS << "#include <math.h>\n";
  headerOS << "#include <stdint.h>\n";
  headerOS << "#include <stdbool.h>\n\n";

  for (auto *D : C_TU->decls()) {  // Use C_TU instead of TU
    if (!D->isImplicit()) {
      headerGen.printDecl(D, true);  // declarationOnly=true for headers
    }
  }

  // Generate implementation file (.c) - full definitions
  implOS << "// Generated from: " << InputFilename << "\n";
  implOS << "// Implementation file\n\n";

  // Include the corresponding header
  // Extract base name for #include (strip path and extension)
  size_t lastSlash = InputFilename.find_last_of("/\\");
  std::string baseName;
  if (lastSlash != std::string::npos) {
    baseName = InputFilename.substr(lastSlash + 1);
  } else {
    baseName = InputFilename;
  }
  // Strip extension from base name (e.g., "main.cpp" → "main")
  size_t dotPos = baseName.find_last_of('.');
  if (dotPos != std::string::npos) {
    baseName = baseName.substr(0, dotPos);
  }
  implOS << "#include \"" << baseName << ".h\"\n\n";

  for (auto *D : C_TU->decls()) {  // Use C_TU instead of TU
    if (!D->isImplicit()) {
      implGen.printDecl(D, false);  // declarationOnly=false for implementation
    }
  }

  // Flush the streams
  headerOS.flush();
  implOS.flush();

  // Use FileOutputManager to write files
  FileOutputManager outputMgr;
  outputMgr.setInputFilename(InputFilename);

  // Set output directory if specified
  std::string outputDir = getOutputDir();
  if (!outputDir.empty()) {
    outputMgr.setOutputDir(outputDir);
  }

  // Set source directory for structure preservation if specified
  if (!SourceDir.empty()) {
    outputMgr.setSourceDir(SourceDir);
  }

  // Write the files
  if (outputMgr.writeFiles(headerContent, implContent)) {
    llvm::outs() << "Generated files:\n";
    llvm::outs() << "  " << outputMgr.getHeaderFilename() << "\n";
    llvm::outs() << "  " << outputMgr.getImplFilename() << "\n";
    // Increment global counter - this allows main() to return success
    // even if there were parse errors (e.g., missing system headers)
    g_filesGeneratedCount++;
  } else {
    llvm::errs() << "Error: Failed to write output files\n";
  }
}
