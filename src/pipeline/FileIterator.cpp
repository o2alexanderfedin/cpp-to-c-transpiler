#include "pipeline/FileIterator.h"
#include <unordered_set>

namespace cpptoc {
namespace pipeline {

FileIterator::FileIterator(const PipelineConfig& config)
  : config_(config),
    currentIndex_(0),
    usingExplicitFiles_(!config.inputFiles.empty()),
    exhausted_(false) {

  if (!usingExplicitFiles_) {
    initializeDirectoryIterator();
  }
}

void FileIterator::initializeDirectoryIterator() {
  fs::path sourcePath(config_.sourceDir);

  // Validate source directory exists
  if (!fs::exists(sourcePath) || !fs::is_directory(sourcePath)) {
    exhausted_ = true;
    return;
  }

  // Create recursive directory iterator
  dirIterator_ = std::make_unique<fs::recursive_directory_iterator>(
    sourcePath,
    fs::directory_options::skip_permission_denied
  );
}

bool FileIterator::isCppSourceFile(const fs::path& path) {
  static const std::unordered_set<std::string> validExtensions = {
    ".cpp", ".cxx", ".cc"
  };
  return validExtensions.count(path.extension().string()) > 0;
}

bool FileIterator::shouldExcludeDirectory(const std::string& dirName) {
  // Exact match exclusions
  static const std::unordered_set<std::string> excludedDirs = {
    ".git", ".svn", ".hg",
    "node_modules", "vendor"
  };

  if (excludedDirs.count(dirName) > 0) {
    return true;
  }

  // Prefix pattern exclusions
  if (dirName.find("build") == 0) return true;  // build, build-debug, etc.
  if (dirName.find("cmake-build-") == 0) return true;  // CLion build dirs
  if (dirName.size() > 0 && dirName[0] == '.' && dirName != "..") return true;  // Hidden dirs

  return false;
}

std::optional<std::string> FileIterator::next() {
  if (exhausted_) {
    return std::nullopt;
  }

  if (usingExplicitFiles_) {
    // Explicit file list mode
    while (currentIndex_ < config_.inputFiles.size()) {
      const std::string& path = config_.inputFiles[currentIndex_++];

      // Validate file exists and is regular
      if (fs::exists(path) && fs::is_regular_file(path)) {
        return fs::absolute(path).string();
      }
    }

    exhausted_ = true;
    return std::nullopt;
  } else {
    // Directory scanning mode
    return advanceToNextFile();
  }
}

std::optional<std::string> FileIterator::advanceToNextFile() {
  if (!dirIterator_ || *dirIterator_ == fs::recursive_directory_iterator()) {
    exhausted_ = true;
    return std::nullopt;
  }

  while (*dirIterator_ != fs::recursive_directory_iterator()) {
    auto& entry = **dirIterator_;

    // Skip excluded directories
    if (entry.is_directory()) {
      std::string dirName = entry.path().filename().string();
      if (shouldExcludeDirectory(dirName)) {
        dirIterator_->disable_recursion_pending();  // Don't descend
        ++(*dirIterator_);
        continue;
      }
    }

    // Check for C++ source file
    if (entry.is_regular_file() && isCppSourceFile(entry.path())) {
      std::string result = fs::absolute(entry.path()).string();
      ++(*dirIterator_);  // Advance for next call
      return result;
    }

    ++(*dirIterator_);
  }

  exhausted_ = true;
  return std::nullopt;
}

void FileIterator::reset() {
  currentIndex_ = 0;
  exhausted_ = false;

  if (!usingExplicitFiles_) {
    dirIterator_.reset();
    initializeDirectoryIterator();
  }
}

}} // namespace cpptoc::pipeline
