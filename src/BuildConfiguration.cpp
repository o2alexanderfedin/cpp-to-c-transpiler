/**
 * BuildConfiguration.cpp
 *
 * Story #119: Implement Size Optimization with LTO/PGO Support
 * Epic #16: Runtime Optimization & Configuration
 *
 * Implementation of BuildConfiguration class for managing
 * compiler optimization flags and build settings.
 */

#include "BuildConfiguration.h"
#include <sys/stat.h>
#include <sstream>

/**
 * Default constructor
 * Initializes with no optimizations (baseline configuration)
 */
BuildConfiguration::BuildConfiguration()
    : optimizationLevel(OptLevel::None)
    , ltoEnabled(false)
    , pgoMode(PGOMode::Disabled)
    , deadCodeEliminationEnabled(false) {
}

/**
 * Set optimization level
 */
void BuildConfiguration::setOptimizationLevel(OptLevel level) {
    optimizationLevel = level;
}

/**
 * Get current optimization level
 */
BuildConfiguration::OptLevel BuildConfiguration::getOptimizationLevel() const {
    return optimizationLevel;
}

/**
 * Enable Link Time Optimization
 */
void BuildConfiguration::enableLTO() {
    ltoEnabled = true;
}

/**
 * Disable Link Time Optimization
 */
void BuildConfiguration::disableLTO() {
    ltoEnabled = false;
}

/**
 * Check if LTO is enabled
 */
bool BuildConfiguration::isLTOEnabled() const {
    return ltoEnabled;
}

/**
 * Enable Profile-Guided Optimization
 */
void BuildConfiguration::enablePGO(PGOMode mode) {
    pgoMode = mode;
}

/**
 * Disable Profile-Guided Optimization
 */
void BuildConfiguration::disablePGO() {
    pgoMode = PGOMode::Disabled;
}

/**
 * Get current PGO mode
 */
BuildConfiguration::PGOMode BuildConfiguration::getPGOMode() const {
    return pgoMode;
}

/**
 * Enable dead code elimination
 */
void BuildConfiguration::enableDeadCodeElimination() {
    deadCodeEliminationEnabled = true;
}

/**
 * Disable dead code elimination
 */
void BuildConfiguration::disableDeadCodeElimination() {
    deadCodeEliminationEnabled = false;
}

/**
 * Check if dead code elimination is enabled
 */
bool BuildConfiguration::isDeadCodeEliminationEnabled() const {
    return deadCodeEliminationEnabled;
}

/**
 * Get compiler flags for this configuration
 */
std::vector<std::string> BuildConfiguration::getCompilerFlags() const {
    std::vector<std::string> flags;

    // Add optimization level flag
    std::string optFlag = optimizationLevelToFlag(optimizationLevel);
    if (!optFlag.empty()) {
        flags.push_back(optFlag);
    }

    // Add LTO flag
    if (ltoEnabled) {
        flags.push_back("-flto");
    }

    // Add PGO flag
    std::string pgoFlag = pgoModeToFlag(pgoMode);
    if (!pgoFlag.empty()) {
        flags.push_back(pgoFlag);
    }

    // Add dead code elimination flags (compiler side)
    if (deadCodeEliminationEnabled) {
        flags.push_back("-ffunction-sections");
        flags.push_back("-fdata-sections");
    }

    return flags;
}

/**
 * Get linker flags for this configuration
 */
std::vector<std::string> BuildConfiguration::getLinkerFlags() const {
    std::vector<std::string> flags;

    // Add LTO flag for linker
    if (ltoEnabled) {
        flags.push_back("-flto");
    }

    // Add dead code elimination flags (linker side)
    if (deadCodeEliminationEnabled) {
        flags.push_back("-Wl,--gc-sections");
    }

    return flags;
}

/**
 * Measure binary size of a compiled program
 */
size_t BuildConfiguration::measureBinarySize(const std::string& binaryPath) const {
    struct stat st;
    if (stat(binaryPath.c_str(), &st) == 0) {
        return static_cast<size_t>(st.st_size);
    }
    return 0;
}

/**
 * Generate CMake configuration for this build configuration
 */
std::string BuildConfiguration::generateCMakeConfig() const {
    std::ostringstream oss;

    oss << "# Build Configuration\n";
    oss << "# Story #119: Size Optimization with LTO/PGO Support\n\n";

    // Optimization level
    oss << "# Optimization Level: ";
    switch (optimizationLevel) {
        case OptLevel::None:
            oss << "None (-O0)\n";
            oss << "set(CMAKE_C_FLAGS \"${CMAKE_C_FLAGS} -O0\")\n";
            oss << "set(CMAKE_CXX_FLAGS \"${CMAKE_CXX_FLAGS} -O0\")\n";
            break;
        case OptLevel::Size:
            oss << "Size (-Os)\n";
            oss << "set(CMAKE_C_FLAGS \"${CMAKE_C_FLAGS} -Os\")\n";
            oss << "set(CMAKE_CXX_FLAGS \"${CMAKE_CXX_FLAGS} -Os\")\n";
            break;
        case OptLevel::Speed:
            oss << "Speed (-O2)\n";
            oss << "set(CMAKE_C_FLAGS \"${CMAKE_C_FLAGS} -O2\")\n";
            oss << "set(CMAKE_CXX_FLAGS \"${CMAKE_CXX_FLAGS} -O2\")\n";
            break;
        case OptLevel::MaxSpeed:
            oss << "MaxSpeed (-O3)\n";
            oss << "set(CMAKE_C_FLAGS \"${CMAKE_C_FLAGS} -O3\")\n";
            oss << "set(CMAKE_CXX_FLAGS \"${CMAKE_CXX_FLAGS} -O3\")\n";
            break;
    }
    oss << "\n";

    // LTO
    if (ltoEnabled) {
        oss << "# Link Time Optimization (LTO)\n";
        oss << "set(CMAKE_INTERPROCEDURAL_OPTIMIZATION TRUE)\n";
        oss << "set(CMAKE_C_FLAGS \"${CMAKE_C_FLAGS} -flto\")\n";
        oss << "set(CMAKE_CXX_FLAGS \"${CMAKE_CXX_FLAGS} -flto\")\n\n";
    }

    // PGO
    if (pgoMode != PGOMode::Disabled) {
        oss << "# Profile-Guided Optimization (PGO)\n";
        if (pgoMode == PGOMode::Generate) {
            oss << "set(CMAKE_C_FLAGS \"${CMAKE_C_FLAGS} -fprofile-generate\")\n";
            oss << "set(CMAKE_CXX_FLAGS \"${CMAKE_CXX_FLAGS} -fprofile-generate\")\n";
        } else {
            oss << "set(CMAKE_C_FLAGS \"${CMAKE_C_FLAGS} -fprofile-use\")\n";
            oss << "set(CMAKE_CXX_FLAGS \"${CMAKE_CXX_FLAGS} -fprofile-use\")\n";
        }
        oss << "\n";
    }

    // Dead code elimination
    if (deadCodeEliminationEnabled) {
        oss << "# Dead Code Elimination\n";
        oss << "set(CMAKE_C_FLAGS \"${CMAKE_C_FLAGS} -ffunction-sections -fdata-sections\")\n";
        oss << "set(CMAKE_CXX_FLAGS \"${CMAKE_CXX_FLAGS} -ffunction-sections -fdata-sections\")\n";
        oss << "set(CMAKE_EXE_LINKER_FLAGS \"${CMAKE_EXE_LINKER_FLAGS} -Wl,--gc-sections\")\n\n";
    }

    return oss.str();
}

/**
 * Generate compiler command line for this configuration
 */
std::string BuildConfiguration::generateCompileCommand(const std::string& sourcePath,
                                                       const std::string& outputPath) const {
    std::ostringstream oss;

    oss << "gcc";

    // Add compiler flags
    std::vector<std::string> compilerFlags = getCompilerFlags();
    for (const auto& flag : compilerFlags) {
        oss << " " << flag;
    }

    // Add linker flags
    std::vector<std::string> linkerFlags = getLinkerFlags();
    for (const auto& flag : linkerFlags) {
        oss << " " << flag;
    }

    // Add source and output
    oss << " " << sourcePath << " -o " << outputPath;

    return oss.str();
}

/**
 * Convert optimization level to compiler flag
 */
std::string BuildConfiguration::optimizationLevelToFlag(OptLevel level) const {
    switch (level) {
        case OptLevel::None:
            return "-O0";
        case OptLevel::Size:
            return "-Os";
        case OptLevel::Speed:
            return "-O2";
        case OptLevel::MaxSpeed:
            return "-O3";
        default:
            return "";
    }
}

/**
 * Convert PGO mode to compiler flag
 */
std::string BuildConfiguration::pgoModeToFlag(PGOMode mode) const {
    switch (mode) {
        case PGOMode::Generate:
            return "-fprofile-generate";
        case PGOMode::Use:
            return "-fprofile-use";
        case PGOMode::Disabled:
        default:
            return "";
    }
}
