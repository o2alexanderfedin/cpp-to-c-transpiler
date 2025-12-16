// RuntimeFeatureFlags.cpp - Modular runtime feature flags implementation
// Story #118: Implement Modular Runtime Feature Flags
//
// TDD GREEN Phase: Implement minimal functionality to pass all tests
//
// This implementation parses command-line --runtime flags and manages
// which runtime features are enabled, allowing fine-grained control over
// code size and compilation speed.

#include "RuntimeFeatureFlags.h"
#include <algorithm>
#include <sstream>
#include <cctype>

// Constructor - parse runtime flags from command line
RuntimeFeatureFlags::RuntimeFeatureFlags(int argc, const char** argv) {
  bool foundFlag = false;

  // Search for --runtime flag
  for (int i = 1; i < argc; ++i) {
    std::string arg(argv[i]);

    if (arg.find("--runtime=") == 0) {
      // Extract value after '='
      std::string value = arg.substr(10);  // Length of "--runtime="
      parseRuntimeFlag(value);
      foundFlag = true;
      break;
    }
  }

  // Default: enable all features (backward compatibility)
  if (!foundFlag) {
    enabledFeatures_.insert(RuntimeFeature::Exceptions);
    enabledFeatures_.insert(RuntimeFeature::RTTI);
    enabledFeatures_.insert(RuntimeFeature::Memory);
    enabledFeatures_.insert(RuntimeFeature::VInherit);
  }
}

// Check if a specific runtime feature is enabled
bool RuntimeFeatureFlags::isEnabled(RuntimeFeature feature) const {
  return enabledFeatures_.count(feature) > 0;
}

// Get list of all enabled features
std::vector<RuntimeFeature> RuntimeFeatureFlags::getEnabledFeatures() const {
  return std::vector<RuntimeFeature>(enabledFeatures_.begin(), enabledFeatures_.end());
}

// Get estimated size of a runtime module in bytes
size_t RuntimeFeatureFlags::getModuleSize(RuntimeFeature feature) const {
  switch (feature) {
    case RuntimeFeature::Exceptions:
      return EXCEPTION_SIZE;
    case RuntimeFeature::RTTI:
      return RTTI_SIZE;
    case RuntimeFeature::Memory:
      return MEMORY_SIZE;
    case RuntimeFeature::VInherit:
      return VINHERIT_SIZE;
    default:
      return 0;
  }
}

// Get total size of all enabled modules
size_t RuntimeFeatureFlags::getTotalEnabledSize() const {
  size_t total = 0;
  for (auto feature : enabledFeatures_) {
    total += getModuleSize(feature);
  }
  return total;
}

// Generate preprocessor defines for enabled features
std::string RuntimeFeatureFlags::generatePreprocessorDefines() const {
  std::stringstream ss;

  for (auto feature : enabledFeatures_) {
    ss << "#define CPPTOC_RUNTIME_";

    switch (feature) {
      case RuntimeFeature::Exceptions:
        ss << "EXCEPTIONS";
        break;
      case RuntimeFeature::RTTI:
        ss << "RTTI";
        break;
      case RuntimeFeature::Memory:
        ss << "COROUTINES";  // Memory is for coroutines
        break;
      case RuntimeFeature::VInherit:
        ss << "VINHERIT";
        break;
    }

    ss << "\n";
  }

  return ss.str();
}

// Generate size impact documentation
std::string RuntimeFeatureFlags::generateSizeDocumentation() const {
  std::stringstream ss;

  ss << "| Feature          | Size (bytes) | Enabled |\n";
  ss << "|------------------|--------------|--       |------|\n";

  // Exceptions
  ss << "| Exceptions       | 800-1200     | ";
  ss << (isEnabled(RuntimeFeature::Exceptions) ? "Yes" : "No") << " |\n";

  // RTTI
  ss << "| RTTI             | 600-1000     | ";
  ss << (isEnabled(RuntimeFeature::RTTI) ? "Yes" : "No") << " |\n";

  // Coroutines (Memory)
  ss << "| Coroutines       | 400-800      | ";
  ss << (isEnabled(RuntimeFeature::Memory) ? "Yes" : "No") << " |\n";

  // Virtual Inheritance
  ss << "| Virtual Inherit  | 500-900      | ";
  ss << (isEnabled(RuntimeFeature::VInherit) ? "Yes" : "No") << " |\n";

  // Total
  ss << "|------------------|--------------|------|\n";
  ss << "| **Total**        | **" << getTotalEnabledSize() << "**      | - |\n";

  return ss.str();
}

// Parse --runtime flag value
void RuntimeFeatureFlags::parseRuntimeFlag(const std::string& value) {
  // Clear any defaults
  enabledFeatures_.clear();

  std::string lowerValue = toLower(value);

  // Handle special cases
  if (lowerValue == "all") {
    enabledFeatures_.insert(RuntimeFeature::Exceptions);
    enabledFeatures_.insert(RuntimeFeature::RTTI);
    enabledFeatures_.insert(RuntimeFeature::Memory);
    enabledFeatures_.insert(RuntimeFeature::VInherit);
    return;
  }

  if (lowerValue == "none") {
    // Leave enabledFeatures_ empty
    return;
  }

  // Parse comma-separated list
  std::stringstream ss(value);
  std::string featureName;

  while (std::getline(ss, featureName, ',')) {
    // Trim whitespace
    featureName.erase(0, featureName.find_first_not_of(" \t"));
    featureName.erase(featureName.find_last_not_of(" \t") + 1);

    if (!featureName.empty()) {
      RuntimeFeature feature = parseFeatureName(featureName);
      enabledFeatures_.insert(feature);
    }
  }
}

// Parse single feature name
RuntimeFeature RuntimeFeatureFlags::parseFeatureName(const std::string& name) const {
  std::string lowerName = toLower(name);

  if (lowerName == "exceptions") {
    return RuntimeFeature::Exceptions;
  } else if (lowerName == "rtti") {
    return RuntimeFeature::RTTI;
  } else if (lowerName == "coroutines" || lowerName == "memory") {
    return RuntimeFeature::Memory;
  } else if (lowerName == "vinherit" || lowerName == "virtual-inheritance") {
    return RuntimeFeature::VInherit;
  } else {
    throw std::invalid_argument("Unknown runtime feature: " + name);
  }
}

// Convert RuntimeFeature to string name
std::string RuntimeFeatureFlags::featureToString(RuntimeFeature feature) const {
  switch (feature) {
    case RuntimeFeature::Exceptions:
      return "exceptions";
    case RuntimeFeature::RTTI:
      return "rtti";
    case RuntimeFeature::Memory:
      return "coroutines";
    case RuntimeFeature::VInherit:
      return "vinherit";
    default:
      return "unknown";
  }
}

// Convert string to lowercase
std::string RuntimeFeatureFlags::toLower(const std::string& str) const {
  std::string result = str;
  std::transform(result.begin(), result.end(), result.begin(),
                 [](unsigned char c) { return std::tolower(c); });
  return result;
}
