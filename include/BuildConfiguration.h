/**
 * BuildConfiguration.h
 *
 * Story #119: Implement Size Optimization with LTO/PGO Support
 * Epic #16: Runtime Optimization & Configuration
 *
 * Build configuration management for size optimization including:
 * - Optimization levels (-Os, -O2, -O3)
 * - LTO (Link Time Optimization)
 * - PGO (Profile-Guided Optimization)
 * - Dead code elimination flags
 * - Function/data section separation
 * - Binary size measurement
 *
 * SOLID Principles:
 * - Single Responsibility: Manages build configuration only
 * - Open/Closed: Extensible for new optimization techniques
 * - Liskov Substitution: Can be substituted with derived configs
 * - Interface Segregation: Minimal, focused interface
 * - Dependency Inversion: Depends on abstractions (enums)
 *
 * Design Patterns:
 * - Builder pattern for configuration construction
 * - Strategy pattern for different optimization strategies
 */

#ifndef BUILD_CONFIGURATION_H
#define BUILD_CONFIGURATION_H

#include <string>
#include <vector>
#include <cstddef>

/**
 * Build configuration for size optimization
 *
 * Provides interface for:
 * - Setting optimization levels
 * - Enabling LTO and PGO
 * - Configuring dead code elimination
 * - Measuring binary sizes
 */
class BuildConfiguration {
public:
    /**
     * Optimization level enumeration
     */
    enum class OptLevel {
        None,       // No optimization (-O0)
        Size,       // Optimize for size (-Os)
        Speed,      // Optimize for speed (-O2)
        MaxSpeed    // Maximum speed (-O3)
    };

    /**
     * PGO mode enumeration
     */
    enum class PGOMode {
        Disabled,   // No PGO
        Generate,   // Generate profile data (-fprofile-generate)
        Use         // Use profile data (-fprofile-use)
    };

    /**
     * Default constructor
     * Initializes with no optimizations
     */
    BuildConfiguration();

    /**
     * Set optimization level
     *
     * @param level Optimization level to use
     */
    void setOptimizationLevel(OptLevel level);

    /**
     * Get current optimization level
     *
     * @return Current optimization level
     */
    OptLevel getOptimizationLevel() const;

    /**
     * Enable Link Time Optimization
     *
     * Adds -flto flag for whole-program optimization
     */
    void enableLTO();

    /**
     * Disable Link Time Optimization
     */
    void disableLTO();

    /**
     * Check if LTO is enabled
     *
     * @return true if LTO is enabled
     */
    bool isLTOEnabled() const;

    /**
     * Enable Profile-Guided Optimization
     *
     * @param mode PGO mode (Generate or Use)
     */
    void enablePGO(PGOMode mode);

    /**
     * Disable Profile-Guided Optimization
     */
    void disablePGO();

    /**
     * Get current PGO mode
     *
     * @return Current PGO mode
     */
    PGOMode getPGOMode() const;

    /**
     * Enable dead code elimination
     *
     * Adds -ffunction-sections, -fdata-sections, and -Wl,--gc-sections
     */
    void enableDeadCodeElimination();

    /**
     * Disable dead code elimination
     */
    void disableDeadCodeElimination();

    /**
     * Check if dead code elimination is enabled
     *
     * @return true if dead code elimination is enabled
     */
    bool isDeadCodeEliminationEnabled() const;

    /**
     * Get compiler flags for this configuration
     *
     * @return Vector of compiler flags
     */
    std::vector<std::string> getCompilerFlags() const;

    /**
     * Get linker flags for this configuration
     *
     * @return Vector of linker flags
     */
    std::vector<std::string> getLinkerFlags() const;

    /**
     * Measure binary size of a compiled program
     *
     * @param binaryPath Path to the binary file
     * @return Size in bytes, or 0 if file doesn't exist
     */
    size_t measureBinarySize(const std::string& binaryPath) const;

    /**
     * Generate CMake configuration for this build configuration
     *
     * @return CMake configuration string
     */
    std::string generateCMakeConfig() const;

    /**
     * Generate compiler command line for this configuration
     *
     * @param sourcePath Path to source file
     * @param outputPath Path to output file
     * @return Full compiler command
     */
    std::string generateCompileCommand(const std::string& sourcePath,
                                       const std::string& outputPath) const;

private:
    OptLevel optimizationLevel;
    bool ltoEnabled;
    PGOMode pgoMode;
    bool deadCodeEliminationEnabled;

    /**
     * Convert optimization level to compiler flag
     *
     * @param level Optimization level
     * @return Compiler flag string (e.g., "-Os")
     */
    std::string optimizationLevelToFlag(OptLevel level) const;

    /**
     * Convert PGO mode to compiler flag
     *
     * @param mode PGO mode
     * @return Compiler flag string or empty if disabled
     */
    std::string pgoModeToFlag(PGOMode mode) const;
};

#endif // BUILD_CONFIGURATION_H
