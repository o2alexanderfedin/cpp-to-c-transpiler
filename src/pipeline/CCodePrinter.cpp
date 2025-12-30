#include "pipeline/CCodePrinter.h"
#include "CodeGenerator.h"
#include "FileOutputManager.h"
#include "IncludeGuardGenerator.h"
#include "mapping/PathMapper.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>

namespace cpptoc {
namespace pipeline {

// Accessor functions from main.cpp (extern linkage)
extern std::string getOutputDir();
extern std::string getSourceDir();
extern bool shouldUsePragmaOnce();

CCodePrinter::CCodePrinter(const PipelineConfig& config)
  : config_(config) {}

void CCodePrinter::print(TargetContext& targetCtx, const std::string& sourceFilePath) {
  // Get PathMapper
  PathMapper& pathMapper = PathMapper::getInstance(
    config_.sourceDir,
    config_.outputDir
  );

  // Map source to target
  std::string targetPath = pathMapper.mapSourceToTarget(sourceFilePath);

  // Get C_TU for this file
  clang::TranslationUnitDecl* C_TU = pathMapper.getOrCreateTU(targetPath);
  if (!C_TU) {
    return;  // No C TU for this file
  }

  clang::ASTContext& cCtx = targetCtx.getContext();

  // Generate header and implementation
  std::string headerContent;
  std::string implContent;

  {
    llvm::raw_string_ostream headerOS(headerContent);
    llvm::raw_string_ostream implOS(implContent);

    CodeGenerator headerGen(headerOS, cCtx, sourceFilePath);
    CodeGenerator implGen(implOS, cCtx, sourceFilePath);

    // Generate header (declarations only)
    if (config_.usePragmaOnce) {
      headerOS << "#pragma once\n\n";
    } else {
      IncludeGuardGenerator guardGen;
      std::string guard = guardGen.generateGuardName(sourceFilePath);
      headerOS << "#ifndef " << guard << "\n";
      headerOS << "#define " << guard << "\n\n";
    }

    for (auto it = C_TU->decls_begin(); it != C_TU->decls_end(); ++it) {
      headerGen.printDecl(*it, true);  // declarationOnly = true
    }

    if (!config_.usePragmaOnce) {
      IncludeGuardGenerator guardGen;
      std::string guard = guardGen.generateGuardName(sourceFilePath);
      headerOS << "\n#endif // " << guard << "\n";
    }

    headerOS.flush();

    // Generate implementation (full definitions)
    // Add include for header
    std::string headerFilename = sourceFilePath;
    size_t lastSlash = headerFilename.find_last_of("/\\");
    if (lastSlash != std::string::npos) {
      headerFilename = headerFilename.substr(lastSlash + 1);
    }
    size_t lastDot = headerFilename.find_last_of('.');
    if (lastDot != std::string::npos) {
      headerFilename = headerFilename.substr(0, lastDot) + ".h";
    } else {
      headerFilename += ".h";
    }

    implOS << "#include \"" << headerFilename << "\"\n\n";

    for (auto it = C_TU->decls_begin(); it != C_TU->decls_end(); ++it) {
      implGen.printDecl(*it, false);  // declarationOnly = false
    }

    implOS.flush();
  }

  // Write files
  FileOutputManager fileManager;
  fileManager.setInputFilename(sourceFilePath);
  fileManager.setOutputDir(config_.outputDir);
  fileManager.setSourceDir(config_.sourceDir);

  if (!fileManager.writeFiles(headerContent, implContent)) {
    llvm::errs() << "Error: Failed to write output files for " << sourceFilePath << "\n";
  }
}

void CCodePrinter::printAll(TargetContext& targetCtx) {
  // Get PathMapper
  PathMapper& pathMapper = PathMapper::getInstance(
    config_.sourceDir,
    config_.outputDir
  );

  // Iterate over all C TUs and generate files
  // Note: PathMapper doesn't expose iterator, so we can't easily iterate all TUs
  // For Phase 1, we rely on print() being called per source file
  // Phase 2 will add better iteration support
}

}} // namespace cpptoc::pipeline
