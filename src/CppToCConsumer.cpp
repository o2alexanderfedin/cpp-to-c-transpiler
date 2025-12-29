#include "CppToCConsumer.h"
#include "CNodeBuilder.h"
#include "CppToCVisitor.h"
#include "CodeGenerator.h"
#include "FileOutputManager.h"
#include "TargetContext.h"
#include "mapping/PathMapper.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <sstream>
#include <atomic>
#include <filesystem>

namespace fs = std::filesystem;

// External accessors (defined in main.cpp)
extern std::string getOutputDir();
extern std::string getSourceDir();

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

  // Phase 35-02 (Bug #30 FIX): Use shared target context for C AST nodes
  // Get the singleton target context (creates independent ASTContext on first call)
  TargetContext& targetCtx = TargetContext::getInstance();

  // Create CNodeBuilder using the shared target context
  // All C nodes from all files are created in this shared context
  clang::CNodeBuilder Builder(targetCtx.getContext());

  // PathMapper Integration: Get singleton PathMapper instance
  // All files share the same PathMapper to ensure consistent C_TU instances
  std::string sourceDir = getSourceDir();
  std::string outputDir = getOutputDir();
  if (outputDir.empty()) {
    outputDir = ".";  // Default to current directory
  }

  // Get the shared PathMapper instance (initializes on first call)
  cpptoc::PathMapper& pathMapper = cpptoc::PathMapper::getInstance(sourceDir, outputDir);

  // Map source file to target path and get/create C_TU
  std::string targetPath = pathMapper.mapSourceToTarget(InputFilename);
  clang::TranslationUnitDecl* C_TU = pathMapper.getOrCreateTU(targetPath);
  llvm::outs() << "[PathMapper] Mapped " << InputFilename << " -> " << targetPath << "\n";
  llvm::outs() << "[PathMapper] C_TU @ " << (void*)C_TU << " for target: " << targetPath << "\n";

  // Create and run visitor to traverse AST
  // Phase 34: Pass FileOriginTracker to visitor for multi-file support
  // Bug Fix: Pass TargetContext for shared constructor/method/destructor maps
  // PathMapper Integration: Pass PathMapper for declaration routing
  // Refactoring: Removed C_TU parameter - visitor now uses location-based getTargetForNode()
  CppToCVisitor Visitor(Context, Builder, targetCtx, fileOriginTracker, &pathMapper);
  Visitor.TraverseDecl(TU);

  // DEBUG: Check how many declarations are in C_TU IMMEDIATELY after traversal
  llvm::outs() << "[DEBUG AFTER TRAVERSAL] C_TU @ " << (void*)C_TU << " has "
               << std::distance(C_TU->decls().begin(), C_TU->decls().end())
               << " declarations after traversal\n";
  for (auto *D : C_TU->decls()) {
    if (auto* FD = dyn_cast<clang::FunctionDecl>(D)) {
      llvm::outs() << "  [AFTER TRAVERSAL] FunctionDecl: " << FD->getNameAsString() << "\n";
    }
  }

  // Phase 11 (v2.4.0): Process template instantiations after AST traversal
  // This generates monomorphized C code for all template instantiations
  Visitor.processTemplateInstantiations(TU);

  // Phase 35-02 (Bug #30 FIX): C_TU already created above and passed to Visitor
  // The Visitor added all declarations to this file's C_TU during traversal

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

  // Phase 40 (Bug Fix): Pass InputFilename to enable duplicate struct filtering
  CodeGenerator headerGen(headerOS, Context, InputFilename);
  CodeGenerator implGen(implOS, Context, InputFilename);

  // Generate header file (.h) - declarations only
  headerOS << "// Generated from: " << InputFilename << "\n";
  headerOS << "// Header file\n\n";

  // Phase 40 (Bug Fix): Add header guard to prevent multiple inclusion
  headerOS << "#pragma once\n\n";

  // Add standard C headers that are commonly needed
  // These replace C++ headers like <cstdio>, <cmath>, etc.
  headerOS << "#include <stdio.h>\n";
  headerOS << "#include <stdlib.h>\n";
  headerOS << "#include <string.h>\n";
  headerOS << "#include <math.h>\n";
  headerOS << "#include <stdint.h>\n";
  headerOS << "#include <stdbool.h>\n\n";

  // Phase 40 (Bug Fix): Emit #include directives for user headers
  // This fixes the issue where main.c couldn't find constructor declarations
  // from library headers (e.g., Vector3D__ctor_3 from Vector3D.h)
  auto userHeaders = fileOriginTracker.getUserHeaderFiles();
  llvm::outs() << "[DEBUG] getUserHeaderFiles() returned " << userHeaders.size() << " headers\n";
  for (const auto& h : userHeaders) {
    llvm::outs() << "[DEBUG]   - " << h << "\n";
  }
  // Calculate output basename for current file (to detect self-includes)
  std::string currentOutputBasename;
  {
    size_t lastSlash = InputFilename.find_last_of("/\\");
    size_t lastDot = InputFilename.find_last_of('.');
    if (lastSlash != std::string::npos) {
      currentOutputBasename = InputFilename.substr(lastSlash + 1);
    } else {
      currentOutputBasename = InputFilename;
    }
    if (lastDot != std::string::npos && lastDot > lastSlash) {
      currentOutputBasename = currentOutputBasename.substr(0, lastDot - (lastSlash != std::string::npos ? lastSlash + 1 : 0));
    }
  }

  for (const auto& headerPath : userHeaders) {
    // Skip if this is the current file being transpiled
    if (headerPath == InputFilename) {
      continue;
    }

    // PHASE 42 (Bug Fix): Skip template-only headers that don't generate separate files
    // Headers like LinkedList.h containing only templates get monomorphized inline
    // and don't produce separate transpiled files, so we shouldn't include them
    bool hasNonTemplateDecls = false;
    auto headerDecls = fileOriginTracker.getDeclarationsFromFile(headerPath);
    for (const auto* D : headerDecls) {
      // Check if this is a non-template declaration that would generate output
      if (auto* CRD = dyn_cast<clang::CXXRecordDecl>(D)) {
        bool isNestedInTemplate = false;
        // Check if this class is nested within a template class
        if (auto* Parent = dyn_cast_or_null<clang::CXXRecordDecl>(CRD->getParent())) {
          if (Parent->getDescribedClassTemplate()) {
            isNestedInTemplate = true;
          }
        }
        // Skip template declarations, implicit declarations, and nested classes in templates
        if (!CRD->getDescribedClassTemplate() && !CRD->isImplicit() && !isNestedInTemplate) {
          // This is a regular class, not a template - needs separate file
          hasNonTemplateDecls = true;
          break;
        }
      } else if (auto* FD = dyn_cast<clang::FunctionDecl>(D)) {
        // Skip template functions and implicit functions
        if (!FD->getDescribedFunctionTemplate() && !FD->isImplicit() &&
            !isa<clang::CXXMethodDecl>(FD)) {  // Methods belong to their class
          hasNonTemplateDecls = true;
          break;
        }
      } else if (auto* VD = dyn_cast<clang::VarDecl>(D)) {
        // Non-template variables need separate file
        if (!VD->isImplicit()) {
          hasNonTemplateDecls = true;
          break;
        }
      }
    }

    if (!hasNonTemplateDecls) {
      // This header contains only templates/nested classes - skip include directive
      continue;
    }

    // Calculate relative path from sourceDir and generate include path
    std::string includePath;
    if (!SourceDir.empty()) {
      try {
        fs::path hdrPath = fs::weakly_canonical(headerPath);
        fs::path rootPath = fs::weakly_canonical(SourceDir);
        fs::path relPath = hdrPath.lexically_relative(rootPath);

        // Replace extension with .h (transpiled C header)
        relPath.replace_extension(".h");
        std::string relPathStr = relPath.string();

        // Phase 40 (Bug Fix): Map include/ headers to src/ transpiled headers
        // C++ headers in include/ don't generate files - the .cpp files in src/ do
        // So include/Vector3D.h → src/Vector3D.h (from src/Vector3D.cpp)
        if (relPathStr.rfind("include/", 0) == 0) {
          // Replace "include/" with "src/"
          relPathStr = "src/" + relPathStr.substr(8);  // 8 = length of "include/"
        }
        includePath = relPathStr;
      } catch (const fs::filesystem_error& e) {
        // Fallback: use basename only
        size_t lastSlash = headerPath.find_last_of("/\\");
        size_t lastDot = headerPath.find_last_of('.');
        std::string baseName;
        if (lastSlash != std::string::npos) {
          baseName = headerPath.substr(lastSlash + 1);
        } else {
          baseName = headerPath;
        }
        if (lastDot != std::string::npos) {
          baseName = baseName.substr(0, lastDot);
        }
        includePath = baseName + ".h";
      }
    } else {
      // No sourceDir set - use basename only
      size_t lastSlash = headerPath.find_last_of("/\\");
      size_t lastDot = headerPath.find_last_of('.');
      std::string baseName;
      if (lastSlash != std::string::npos) {
        baseName = headerPath.substr(lastSlash + 1);
      } else {
        baseName = headerPath;
      }
      if (lastDot != std::string::npos) {
        baseName = baseName.substr(0, lastDot);
      }
      includePath = baseName + ".h";
    }

    // Phase 40 (Bug Fix): Skip self-includes to prevent circular dependencies
    // Extract basename from includePath to compare with currentOutputBasename
    std::string includeBasename;
    {
      size_t lastSlash = includePath.find_last_of("/\\");
      size_t lastDot = includePath.find_last_of('.');
      if (lastSlash != std::string::npos) {
        includeBasename = includePath.substr(lastSlash + 1);
      } else {
        includeBasename = includePath;
      }
      if (lastDot != std::string::npos && lastDot > lastSlash) {
        includeBasename = includeBasename.substr(0, lastDot - (lastSlash != std::string::npos ? lastSlash + 1 : 0));
      }
    }
    if (includeBasename == currentOutputBasename) {
      llvm::outs() << "[DEBUG] Skipping self-include: " << includePath << " (matches current file: " << currentOutputBasename << ")\n";
      continue;  // Skip self-includes
    }

    headerOS << "#include \"" << includePath << "\"\n";
  }
  if (!userHeaders.empty()) {
    headerOS << "\n";  // Blank line after user includes
  }

  // JSON LOG: Starting iteration
  int declCount = std::distance(C_TU->decls().begin(), C_TU->decls().end());
  llvm::outs() << "{\"event\":\"iterate_HEADER_START\",\"ctu\":\"" << (void*)C_TU << "\""
               << ",\"ctuAsDeclContext\":\"" << (void*)static_cast<clang::DeclContext*>(C_TU) << "\""
               << ",\"declCount\":" << declCount
               << ",\"file\":\"" << InputFilename << "\"}\n";

  // DEBUG: Log all declarations being emitted in header
  llvm::outs() << "[DEBUG] Starting header emission - C_TU @ " << (void*)C_TU << " has "
               << declCount << " total declarations\n";

  for (auto *D : C_TU->decls()) {  // Use C_TU instead of TU
    // JSON LOG: Each declaration found during iteration
    if (auto* FD = dyn_cast<clang::FunctionDecl>(D)) {
      llvm::outs() << "{\"event\":\"iterate_HEADER_FOUND\",\"declType\":\"FunctionDecl\""
                   << ",\"name\":\"" << FD->getNameAsString() << "\""
                   << ",\"declPtr\":\"" << (void*)FD << "\""
                   << ",\"isImplicit\":" << (FD->isImplicit() ? "true" : "false")
                   << ",\"declContext\":\"" << (void*)FD->getDeclContext() << "\"}\n";
      llvm::outs() << "[DEBUG-HEADER] Processing FunctionDecl: " << FD->getNameAsString()
                   << " @ " << (void*)FD << " (implicit=" << FD->isImplicit() << ")\n";
    } else if (auto* VD = dyn_cast<clang::VarDecl>(D)) {
      llvm::outs() << "{\"event\":\"iterate_HEADER_FOUND\",\"declType\":\"VarDecl\""
                   << ",\"name\":\"" << VD->getNameAsString() << "\""
                   << ",\"declPtr\":\"" << (void*)VD << "\""
                   << ",\"isImplicit\":" << (VD->isImplicit() ? "true" : "false") << "}\n";
      llvm::outs() << "[DEBUG-HEADER] Processing VarDecl: " << VD->getNameAsString()
                   << " (implicit=" << VD->isImplicit() << ")\n";
    } else if (auto* ED = dyn_cast<clang::EnumDecl>(D)) {
      llvm::outs() << "{\"event\":\"iterate_HEADER_FOUND\",\"declType\":\"EnumDecl\""
                   << ",\"name\":\"" << ED->getNameAsString() << "\""
                   << ",\"declPtr\":\"" << (void*)ED << "\""
                   << ",\"isImplicit\":" << (ED->isImplicit() ? "true" : "false") << "}\n";
      llvm::outs() << "[DEBUG-HEADER] Processing EnumDecl: " << ED->getNameAsString()
                   << " (implicit=" << ED->isImplicit() << ")\n";
    } else if (auto* RD = dyn_cast<clang::RecordDecl>(D)) {
      llvm::outs() << "{\"event\":\"iterate_HEADER_FOUND\",\"declType\":\"RecordDecl\""
                   << ",\"name\":\"" << RD->getNameAsString() << "\""
                   << ",\"declPtr\":\"" << (void*)RD << "\""
                   << ",\"isImplicit\":" << (RD->isImplicit() ? "true" : "false") << "}\n";
      llvm::outs() << "[DEBUG-HEADER] Processing RecordDecl: " << RD->getNameAsString()
                   << " (implicit=" << RD->isImplicit() << ")\n";
    } else {
      llvm::outs() << "{\"event\":\"iterate_HEADER_FOUND\",\"declType\":\"" << D->getDeclKindName() << "\""
                   << ",\"declPtr\":\"" << (void*)D << "\""
                   << ",\"isImplicit\":" << (D->isImplicit() ? "true" : "false") << "}\n";
      llvm::outs() << "[DEBUG-HEADER] Processing declaration of type: " << D->getDeclKindName()
                   << " (implicit=" << D->isImplicit() << ")\n";
    }

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

  // DEBUG: Log all declarations being emitted in implementation
  llvm::outs() << "[DEBUG] Starting implementation emission - C_TU @ " << (void*)C_TU << " has "
               << std::distance(C_TU->decls().begin(), C_TU->decls().end())
               << " total declarations\n";
  for (auto *D : C_TU->decls()) {  // Use C_TU instead of TU
    // Print declaration details
    if (auto* FD = dyn_cast<clang::FunctionDecl>(D)) {
      llvm::outs() << "[DEBUG-IMPL] Processing FunctionDecl: " << FD->getNameAsString()
                   << " (implicit=" << FD->isImplicit() << ")\n";
    } else if (auto* VD = dyn_cast<clang::VarDecl>(D)) {
      llvm::outs() << "[DEBUG-IMPL] Processing VarDecl: " << VD->getNameAsString()
                   << " (implicit=" << VD->isImplicit() << ")\n";
    } else if (auto* ED = dyn_cast<clang::EnumDecl>(D)) {
      llvm::outs() << "[DEBUG-IMPL] Processing EnumDecl: " << ED->getNameAsString()
                   << " (implicit=" << ED->isImplicit() << ")\n";
    } else if (auto* RD = dyn_cast<clang::RecordDecl>(D)) {
      llvm::outs() << "[DEBUG-IMPL] Processing RecordDecl: " << RD->getNameAsString()
                   << " (implicit=" << RD->isImplicit() << ")\n";
    } else {
      llvm::outs() << "[DEBUG-IMPL] Processing declaration of type: " << D->getDeclKindName()
                   << " (implicit=" << D->isImplicit() << ")\n";
    }

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

  // Set output directory if specified (reuse outputDir from PathMapper creation above)
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
