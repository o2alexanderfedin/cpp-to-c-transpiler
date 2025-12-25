#include "FileOutputManager.h"
#include <fstream>
#include <iostream>
#include <filesystem>

namespace fs = std::filesystem;

void FileOutputManager::setInputFilename(const std::string& filename) {
    inputFilename = filename;
}

void FileOutputManager::setOutputDir(const std::string& dir) {
    outputDir = dir;
}

void FileOutputManager::setOutputHeader(const std::string& filename) {
    outputHeader = filename;
}

void FileOutputManager::setOutputImpl(const std::string& filename) {
    outputImpl = filename;
}

void FileOutputManager::setSourceDir(const std::string& root) {
    sourceDir = root;
}

std::string FileOutputManager::getSourceDir() const {
    return sourceDir;
}

std::string FileOutputManager::getBaseName() const {
    // Extract base name: "Point.cpp" → "Point"
    // KISS: Simple string manipulation
    size_t lastSlash = inputFilename.find_last_of("/\\");
    size_t lastDot = inputFilename.find_last_of('.');

    // Get filename without path
    std::string filename;
    if (lastSlash != std::string::npos) {
        filename = inputFilename.substr(lastSlash + 1);
    } else {
        filename = inputFilename;
    }

    // Remove extension
    if (lastDot != std::string::npos) {
        size_t dotPosition = filename.find_last_of('.');
        if (dotPosition != std::string::npos) {
            filename = filename.substr(0, dotPosition);
        }
    }

    return filename;
}

std::string FileOutputManager::getFullPath(const std::string& filename) const {
    // If output directory is set, prepend it to the filename
    if (!outputDir.empty()) {
        // Ensure proper path separator
        if (outputDir.back() == '/' || outputDir.back() == '\\') {
            return outputDir + filename;
        } else {
            return outputDir + "/" + filename;
        }
    }
    return filename;
}

std::string FileOutputManager::calculateOutputPath(const std::string& extension) const {
    // Legacy mode: strip path (current behavior when sourceDir not set)
    if (sourceDir.empty()) {
        return getFullPath(getBaseName() + extension);
    }

    // Structure preservation mode
    try {
        // Resolve symlinks and normalize paths
        fs::path inputPath = fs::weakly_canonical(inputFilename);
        fs::path rootPath = fs::weakly_canonical(sourceDir);

        // Calculate relative path
        fs::path relPath = inputPath.lexically_relative(rootPath);

        // Handle files outside source root
        std::string relPathStr = relPath.string();
        if (relPathStr.find("..") == 0) {
            std::cerr << "Warning: File " << inputFilename
                      << " is outside source root " << sourceDir
                      << ". Using basename only." << std::endl;
            return getFullPath(getBaseName() + extension);
        }

        // Replace extension
        relPath.replace_extension(extension);

        return getFullPath(relPath.string());

    } catch (const fs::filesystem_error& e) {
        std::cerr << "Error calculating output path for " << inputFilename
                  << ": " << e.what() << std::endl;
        // Fallback to legacy behavior
        return getFullPath(getBaseName() + extension);
    }
}

std::string FileOutputManager::getHeaderFilename() const {
    // If custom header name specified, use it
    if (!outputHeader.empty()) {
        return getFullPath(outputHeader);
    }

    // Use new path calculation logic
    return calculateOutputPath(".h");
}

std::string FileOutputManager::getImplFilename() const {
    // If custom source name specified, use it
    if (!outputImpl.empty()) {
        return getFullPath(outputImpl);
    }

    // Use new path calculation logic
    return calculateOutputPath(".c");
}

bool FileOutputManager::writeFile(const std::string& filename,
                                   const std::string& content) {
    // Create parent directories if they don't exist
    fs::path filePath(filename);
    fs::path parentDir = filePath.parent_path();

    if (!parentDir.empty() && !fs::exists(parentDir)) {
        std::error_code ec;
        fs::create_directories(parentDir, ec);
        if (ec) {
            std::cerr << "Error: Could not create directory: " << parentDir
                      << " - " << ec.message() << std::endl;
            return false;
        }
    }

    std::ofstream outFile(filename);

    if (!outFile.is_open()) {
        std::cerr << "Error: Could not open file for writing: " << filename << std::endl;
        return false;
    }

    outFile << content;

    if (outFile.fail()) {
        std::cerr << "Error: Failed to write to file: " << filename << std::endl;
        return false;
    }

    outFile.close();
    return true;
}

bool FileOutputManager::writeFiles(const std::string& headerContent,
                                    const std::string& implContent) {
    // Write header file
    if (!writeFile(getHeaderFilename(), headerContent)) {
        return false;
    }

    // Write implementation file
    if (!writeFile(getImplFilename(), implContent)) {
        return false;
    }

    return true;
}
