// FileOriginTracker Implementation - Phase 34-02
// Purpose: Track declaration-to-file mappings for multi-file transpilation
// Replaces: 12 isInMainFile() checks with intelligent file origin filtering

#include "FileOriginTracker.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceLocation.h"
#include "llvm/Support/Path.h"
#include <algorithm>

namespace cpptoc {

// ============================================================================
// Constructor
// ============================================================================

FileOriginTracker::FileOriginTracker(clang::SourceManager &SM) : SM(SM) {}

// ============================================================================
// Core Recording API
// ============================================================================

void FileOriginTracker::recordDeclaration(const clang::Decl *D) {
  // Null safety (SOLID: defensive programming)
  if (!D) {
    return;
  }

  // Get file path for this declaration
  std::string filepath = getFilePath(D);
  if (filepath.empty()) {
    return; // Skip declarations without valid source location
  }

  // Store in declToFile map (O(1) operation)
  declToFile[D] = filepath;

  // Classify file if not already cached (O(1) with caching)
  if (fileCategories.find(filepath) == fileCategories.end()) {
    fileCategories[filepath] = classifyFile(filepath);
  }

  // Add to fileToDecls map (O(1) map lookup, O(log n) set insertion)
  fileToDecls[filepath].insert(D);
}

// ============================================================================
// Query APIs
// ============================================================================

bool FileOriginTracker::isFromMainFile(const clang::Decl *D) const {
  // DRY: Reuse getFileCategory() instead of duplicating lookup logic
  return getFileCategory(D) == FileCategory::MainFile;
}

bool FileOriginTracker::isFromUserHeader(const clang::Decl *D) const {
  // DRY: Reuse getFileCategory() instead of duplicating lookup logic
  return getFileCategory(D) == FileCategory::UserHeader;
}

bool FileOriginTracker::isFromSystemHeader(const clang::Decl *D) const {
  // DRY: Reuse getFileCategory() instead of duplicating lookup logic
  return getFileCategory(D) == FileCategory::SystemHeader;
}

bool FileOriginTracker::shouldTranspile(const clang::Decl *D) const {
  // DRY: Reuse getFileCategory() instead of duplicating lookup logic
  // Transpilation policy (KISS: simple logic)
  // 1. Main file → always transpile
  // 2. User headers → always transpile
  // 3. Third-party headers → configurable
  // 4. System headers → never transpile

  FileCategory category = getFileCategory(D);

  switch (category) {
  case FileCategory::MainFile:
    return true;
  case FileCategory::UserHeader:
    return true;
  case FileCategory::ThirdPartyHeader:
    return transpileThirdParty; // Configurable
  case FileCategory::SystemHeader:
    return false;
  default:
    return false;
  }
}

std::string FileOriginTracker::getOriginFile(const clang::Decl *D) const {
  if (!D) {
    return "";
  }

  auto it = declToFile.find(D);
  if (it != declToFile.end()) {
    return it->second;
  }

  return "";
}

FileOriginTracker::FileCategory
FileOriginTracker::getFileCategory(const clang::Decl *D) const {
  if (!D) {
    return FileCategory::SystemHeader; // Safe default: skip
  }

  auto it = declToFile.find(D);
  if (it == declToFile.end()) {
    return FileCategory::SystemHeader; // Safe default: skip
  }

  auto catIt = fileCategories.find(it->second);
  if (catIt != fileCategories.end()) {
    return catIt->second;
  }

  return FileCategory::SystemHeader; // Safe default: skip
}

std::set<std::string> FileOriginTracker::getUserHeaderFiles() const {
  std::set<std::string> userHeaders;

  for (const auto &pair : fileCategories) {
    if (pair.second == FileCategory::UserHeader) {
      userHeaders.insert(pair.first);
    }
  }

  return userHeaders;
}

std::set<const clang::Decl *>
FileOriginTracker::getDeclarationsFromFile(const std::string &filepath) const {
  auto it = fileToDecls.find(filepath);
  if (it != fileToDecls.end()) {
    return it->second;
  }

  return {}; // Empty set
}

// ============================================================================
// Configuration APIs
// ============================================================================

void FileOriginTracker::addUserHeaderPath(const std::string &dir) {
  userHeaderPaths.insert(dir);
}

void FileOriginTracker::addThirdPartyPath(const std::string &dir) {
  thirdPartyPaths.insert(dir);
}

void FileOriginTracker::setTranspileThirdParty(bool transpile) {
  transpileThirdParty = transpile;
}

// ============================================================================
// Statistics API
// ============================================================================

FileOriginTracker::Statistics FileOriginTracker::getStatistics() const {
  Statistics stats = {};
  stats.totalDeclarations = declToFile.size();
  stats.uniqueFiles = fileCategories.size();

  // Count by category
  for (const auto &pair : declToFile) {
    const clang::Decl *D = pair.first;
    auto catIt = fileCategories.find(pair.second);
    if (catIt != fileCategories.end()) {
      switch (catIt->second) {
      case FileCategory::MainFile:
        stats.mainFileDeclarations++;
        break;
      case FileCategory::UserHeader:
        stats.userHeaderDeclarations++;
        break;
      case FileCategory::SystemHeader:
        stats.systemHeaderDeclarations++;
        break;
      case FileCategory::ThirdPartyHeader:
        stats.thirdPartyHeaderDeclarations++;
        break;
      }
    }
  }

  return stats;
}

// ============================================================================
// Private Helper Methods
// ============================================================================

std::string FileOriginTracker::getFilePath(const clang::Decl *D) const {
  if (!D) {
    return "";
  }

  // Get source location
  clang::SourceLocation loc = D->getLocation();
  if (!loc.isValid()) {
    return "";
  }

  // Handle macro expansions: use spelling location (where code is written)
  // not expansion location (where macro is expanded)
  loc = SM.getSpellingLoc(loc);
  if (!loc.isValid()) {
    return "";
  }

  // Get file entry
  clang::FileID fileID = SM.getFileID(loc);
  if (fileID.isInvalid()) {
    return "";
  }

  auto fileEntry = SM.getFileEntryRefForID(fileID);
  if (!fileEntry) {
    return "";
  }

  // Return absolute path
  return std::string(fileEntry->getName());
}

FileOriginTracker::FileCategory
FileOriginTracker::classifyFile(const std::string &filepath) const {
  // Check cache first (O(1))
  auto it = fileCategories.find(filepath);
  if (it != fileCategories.end()) {
    return it->second;
  }

  // Classification algorithm (in priority order)

  // 1. Check if main file
  clang::FileID mainFileID = SM.getMainFileID();
  auto mainFileEntry = SM.getFileEntryRefForID(mainFileID);
  if (mainFileEntry) {
    std::string mainFilePath(mainFileEntry->getName());
    if (filepath == mainFilePath) {
      return FileCategory::MainFile;
    }
  }

  // 2. Check if system header (highest priority after main file)
  if (isSystemPath(filepath)) {
    return FileCategory::SystemHeader;
  }

  // 3. Check if user header (explicit configuration)
  if (isUserPath(filepath)) {
    return FileCategory::UserHeader;
  }

  // 4. Check if third-party header (explicit configuration)
  if (isThirdPartyPath(filepath)) {
    return FileCategory::ThirdPartyHeader;
  }

  // 5. Heuristic: If in current working directory or subdirectories → user header
  // Otherwise → system header (safe default: skip unknown files)
  std::string mainDir;
  if (mainFileEntry) {
    llvm::StringRef mainPath(mainFileEntry->getName());
    mainDir = std::string(llvm::sys::path::parent_path(mainPath));
  }

  if (!mainDir.empty() && filepath.find(mainDir) == 0) {
    return FileCategory::UserHeader; // In project directory
  }

  // Default: system header (safe - don't transpile unknown files)
  return FileCategory::SystemHeader;
}

bool FileOriginTracker::isSystemPath(const std::string &filepath) const {
  // macOS system paths
  static const std::vector<std::string> systemPrefixes = {
      "/usr/include/",
      "/Library/Developer/",
      "/System/Library/",
      "/Applications/Xcode.app/Contents/Developer/",
      "/usr/local/include/" // Homebrew packages
  };

  for (const auto &prefix : systemPrefixes) {
    if (filepath.find(prefix) == 0) {
      return true;
    }
  }

  // Also check Clang's built-in system header detection
  // (more robust - handles toolchain-specific paths)
  clang::FileID fileID = SM.translateFile(
      SM.getFileManager().getFileRef(filepath).get());
  if (!fileID.isInvalid()) {
    clang::SourceLocation loc = SM.getLocForStartOfFile(fileID);
    if (loc.isValid() && SM.isInSystemHeader(loc)) {
      return true;
    }
  }

  return false;
}

// Helper: Check if filepath matches a path prefix (absolute or relative)
// SOLID: Single Responsibility - only path prefix matching
static bool matchesPathPrefix(const std::string &filepath, const std::string &prefix) {
  // Check if filepath starts with prefix (absolute path match)
  if (filepath.find(prefix) == 0) {
    return true;
  }

  // Also check if prefix is a relative path and filepath contains it
  // (More flexible matching for relative paths like "include/")
  if (!prefix.empty() && prefix[0] != '/' &&
      filepath.find("/" + prefix) != std::string::npos) {
    return true;
  }

  return false;
}

bool FileOriginTracker::isUserPath(const std::string &filepath) const {
  // DRY: Extract common path matching logic
  for (const auto &userPath : userHeaderPaths) {
    if (matchesPathPrefix(filepath, userPath)) {
      return true;
    }
  }
  return false;
}

bool FileOriginTracker::isThirdPartyPath(const std::string &filepath) const {
  // DRY: Extract common path matching logic
  for (const auto &thirdPartyPath : thirdPartyPaths) {
    if (matchesPathPrefix(filepath, thirdPartyPath)) {
      return true;
    }
  }
  return false;
}

} // namespace cpptoc
