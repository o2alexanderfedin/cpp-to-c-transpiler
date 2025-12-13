#ifndef FILE_OUTPUT_MANAGER_H
#define FILE_OUTPUT_MANAGER_H

#include <string>

/// @brief Manages file output for generated .h and .c files
///
/// SOLID: Single Responsibility - only handles file I/O.
/// This class determines output filenames and writes generated code to files.
///
/// Default behavior: input.cpp → input.h + input.c
/// Custom behavior: --output-header and --output-impl override defaults
class FileOutputManager {
public:
    /// @brief Set input filename (used to derive default output names)
    /// @param filename Input C++ source filename (e.g., "Point.cpp")
    void setInputFilename(const std::string& filename);

    /// @brief Set custom output header filename
    /// @param filename Custom header filename (e.g., "custom.h")
    void setOutputHeader(const std::string& filename);

    /// @brief Set custom output implementation filename
    /// @param filename Custom implementation filename (e.g., "custom.c")
    void setOutputImpl(const std::string& filename);

    /// @brief Get header filename (custom or default)
    /// @return Header filename
    std::string getHeaderFilename() const;

    /// @brief Get implementation filename (custom or default)
    /// @return Implementation filename
    std::string getImplFilename() const;

    /// @brief Write header and implementation files
    /// @param headerContent Content for .h file
    /// @param implContent Content for .c file
    /// @return true if successful, false on error
    bool writeFiles(const std::string& headerContent,
                    const std::string& implContent);

private:
    std::string inputFilename;    ///< Input C++ filename
    std::string outputHeader;     ///< Custom header filename (if set)
    std::string outputImpl;       ///< Custom impl filename (if set)

    /// @brief Derive base name from input filename
    /// @return Base name without extension (e.g., "Point" from "Point.cpp")
    std::string getBaseName() const;

    /// @brief Write content to file with error handling
    /// @param filename Output filename
    /// @param content Content to write
    /// @return true if successful, false on error
    bool writeFile(const std::string& filename, const std::string& content);
};

#endif // FILE_OUTPUT_MANAGER_H
