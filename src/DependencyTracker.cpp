#include "DependencyTracker.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>

namespace cpptoc {

void DependencyTracker::addDependency(const std::string& file, const std::string& dependency) {
  if (file.empty() || dependency.empty()) {
    llvm::outs() << "[DependencyTracker::addDependency] Warning: empty file or dependency\n";
    return;
  }

  // Don't add self-dependencies
  if (file == dependency) {
    return;
  }

  // Add to set (automatically deduplicates)
  fileDependencies_[file].insert(dependency);

  llvm::outs() << "[DependencyTracker::addDependency] " << file << " -> " << dependency << "\n";
}

std::vector<std::string> DependencyTracker::getDependenciesForFile(const std::string& file) const {
  std::vector<std::string> result;

  auto it = fileDependencies_.find(file);
  if (it != fileDependencies_.end()) {
    // Convert set to vector
    result.assign(it->second.begin(), it->second.end());

    // Sort for deterministic output
    std::sort(result.begin(), result.end());
  }

  llvm::outs() << "[DependencyTracker::getDependenciesForFile] File: " << file
               << " has " << result.size() << " dependencies\n";

  return result;
}

void DependencyTracker::clearDependenciesForFile(const std::string& file) {
  fileDependencies_.erase(file);
  llvm::outs() << "[DependencyTracker::clearDependenciesForFile] Cleared dependencies for: "
               << file << "\n";
}

void DependencyTracker::clearAll() {
  fileDependencies_.clear();
  llvm::outs() << "[DependencyTracker::clearAll] Cleared all dependencies\n";
}

} // namespace cpptoc
