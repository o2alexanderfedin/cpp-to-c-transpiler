#include "mapping/PathMapper.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <filesystem>
#include <sstream>

namespace fs = std::filesystem;
namespace cpptoc {

// Singleton getInstance method
PathMapper& PathMapper::getInstance(const std::string& sourceDir, const std::string& outputDir) {
  static PathMapper instance(sourceDir, outputDir);
  return instance;
}

// Reset method for test isolation
void PathMapper::reset() {
  // Get instance without arguments (uses empty defaults)
  PathMapper& instance = getInstance();
  instance.fileToTU_.clear();
  instance.declToTarget_.clear();
}

// Private constructor
PathMapper::PathMapper(const std::string& sourceDir, const std::string& outputDir)
    : targetCtx_(TargetContext::getInstance()),
      sourceDir_(sourceDir),
      outputDir_(outputDir) {
  llvm::outs() << "[PathMapper] Initialized:\n";
  llvm::outs() << "  - Source dir: " << sourceDir_ << "\n";
  llvm::outs() << "  - Output dir: " << outputDir_ << "\n";
}

std::string PathMapper::normalizePath(const std::string& path) const {
  try {
    fs::path p(path);
    return fs::weakly_canonical(p).string();
  } catch (const fs::filesystem_error& e) {
    // Fallback: simple string manipulation for invalid paths
    llvm::outs() << "[PathMapper] Warning: Failed to normalize path: " << path
                 << " (" << e.what() << ")\n";
    return path;
  }
}

std::string PathMapper::getTranspiledFilename(const std::string& sourcePath) const {
  // Extract filename from path
  size_t lastSlash = sourcePath.find_last_of("/\\");
  std::string filename;

  if (lastSlash != std::string::npos) {
    filename = sourcePath.substr(lastSlash + 1);
  } else {
    filename = sourcePath;
  }

  // Find extension
  size_t lastDot = filename.find_last_of('.');
  std::string baseName;
  std::string extension;

  if (lastDot != std::string::npos) {
    baseName = filename.substr(0, lastDot);
    extension = filename.substr(lastDot);
  } else {
    baseName = filename;
    extension = "";
  }

  // Determine output extension based on input extension
  std::string outputExtension;
  if (extension == ".cpp" || extension == ".cc" || extension == ".cxx") {
    outputExtension = ".c";
  } else if (extension == ".h" || extension == ".hpp" || extension == ".hxx") {
    outputExtension = ".h";
  } else {
    // Default: assume it's a source file
    outputExtension = ".c";
  }

  return baseName + outputExtension;
}

std::string PathMapper::getRelativeSourcePath(const std::string& absolutePath) const {
  try {
    fs::path absPath = fs::weakly_canonical(absolutePath);
    fs::path srcPath = fs::weakly_canonical(sourceDir_);

    // Check if absolutePath is under sourceDir
    auto relPath = absPath.lexically_relative(srcPath);

    // If path is not relative (i.e., not under sourceDir), return original
    if (relPath.string().find("..") == 0) {
      return absolutePath;
    }

    return relPath.string();
  } catch (const fs::filesystem_error& e) {
    llvm::outs() << "[PathMapper] Warning: Failed to get relative path for "
                 << absolutePath << " (" << e.what() << ")\n";
    return absolutePath;
  }
}

std::string PathMapper::mapSourceToTarget(const std::string& sourcePath) {
  // Get relative path within source directory
  std::string relPath = getRelativeSourcePath(sourcePath);

  // Extract directory and filename
  std::string directory;
  size_t lastSlash = relPath.find_last_of("/\\");

  if (lastSlash != std::string::npos) {
    directory = relPath.substr(0, lastSlash);
  } else {
    directory = "";
  }

  // Get transpiled filename (with _transpiled suffix)
  std::string transpiledFilename = getTranspiledFilename(sourcePath);

  // Build target path
  std::string targetPath;
  if (!directory.empty()) {
    targetPath = outputDir_ + "/" + directory + "/" + transpiledFilename;
  } else {
    targetPath = outputDir_ + "/" + transpiledFilename;
  }

  // Normalize the target path
  targetPath = normalizePath(targetPath);

  llvm::outs() << "[PathMapper::mapSourceToTarget]\n";
  llvm::outs() << "  Input:  " << sourcePath << "\n";
  llvm::outs() << "  Rel:    " << relPath << "\n";
  llvm::outs() << "  Output: " << targetPath << "\n";

  return targetPath;
}

clang::TranslationUnitDecl* PathMapper::getOrCreateTU(const std::string& targetPath) {
  // Check if we already have a C_TU for this target file
  auto it = fileToTU_.find(targetPath);
  if (it != fileToTU_.end()) {
    llvm::outs() << "[PathMapper::getOrCreateTU] Returning existing C_TU for: "
                 << targetPath << "\n";
    return it->second;
  }

  // Create new C_TU in shared target context
  clang::TranslationUnitDecl* cTU = targetCtx_.createTranslationUnit();

  // Cache it
  fileToTU_[targetPath] = cTU;

  // JSON LOG: C_TU creation
  llvm::outs() << "{\"event\":\"create_CTU\",\"ctu\":\"" << (void*)cTU << "\""
               << ",\"ctuAsDeclContext\":\"" << (void*)static_cast<clang::DeclContext*>(cTU) << "\""
               << ",\"targetFile\":\"" << targetPath << "\"}\n";

  llvm::outs() << "[PathMapper::getOrCreateTU] Created new C_TU @ " << (void*)cTU
               << " for: " << targetPath << "\n";

  return cTU;
}

void PathMapper::registerDeclaration(const clang::Decl* decl,
                                     const std::string& targetPath) {
  if (!decl) {
    llvm::outs() << "[PathMapper::registerDeclaration] Warning: null decl\n";
    return;
  }

  declToTarget_[decl] = targetPath;

  // Also ensure this target file has a C_TU
  if (fileToTU_.find(targetPath) == fileToTU_.end()) {
    getOrCreateTU(targetPath);
  }

  llvm::outs() << "[PathMapper::registerDeclaration] Registered decl "
               << (const void*)decl << " -> " << targetPath << "\n";
}

std::string PathMapper::getTargetPathForDecl(const clang::Decl* decl) const {
  if (!decl) {
    return "";
  }

  auto it = declToTarget_.find(decl);
  if (it != declToTarget_.end()) {
    return it->second;
  }

  llvm::outs() << "[PathMapper::getTargetPathForDecl] Warning: decl "
               << (const void*)decl << " not registered\n";
  return "";
}

std::vector<std::string> PathMapper::getAllTargetFiles() const {
  std::vector<std::string> result;

  // Collect all target files from fileToTU map
  for (const auto& pair : fileToTU_) {
    result.push_back(pair.first);
  }

  // Also check declToTarget for any additional files not in fileToTU yet
  for (const auto& pair : declToTarget_) {
    const auto& targetPath = pair.second;
    if (std::find(result.begin(), result.end(), targetPath) == result.end()) {
      result.push_back(targetPath);
    }
  }

  llvm::outs() << "[PathMapper::getAllTargetFiles] Found " << result.size()
               << " target files:\n";
  for (const auto& file : result) {
    llvm::outs() << "  - " << file << "\n";
  }

  return result;
}

// Phase 1.2: Node location tracking methods

void PathMapper::setNodeLocation(const clang::Decl* node, const std::string& location) {
  if (!node) return;
  targetCtx_.recordNode(node, location);
}

std::string PathMapper::getNodeLocation(const clang::Decl* node) const {
  if (!node) return "";
  return targetCtx_.getLocation(node);
}

std::vector<const clang::Decl*> PathMapper::getAllNodesForFile(const std::string& file) const {
  std::vector<const clang::Decl*> result;

  // Iterate through all registered declarations and filter by target file
  for (const auto& pair : declToTarget_) {
    if (pair.second == file) {
      result.push_back(pair.first);
    }
  }

  llvm::outs() << "[PathMapper::getAllNodesForFile] Found " << result.size()
               << " nodes for file: " << file << "\n";

  return result;
}

} // namespace cpptoc
