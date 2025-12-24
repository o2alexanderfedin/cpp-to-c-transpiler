#include "FileOutputManager.h"
#include <fstream>
#include <iostream>

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

std::string FileOutputManager::getHeaderFilename() const {
    // Return custom header if set, otherwise default
    std::string baseFilename;
    if (!outputHeader.empty()) {
        baseFilename = outputHeader;
    } else {
        baseFilename = getBaseName() + ".h";
    }

    return getFullPath(baseFilename);
}

std::string FileOutputManager::getImplFilename() const {
    // Return custom impl if set, otherwise default
    std::string baseFilename;
    if (!outputImpl.empty()) {
        baseFilename = outputImpl;
    } else {
        baseFilename = getBaseName() + ".c";
    }

    return getFullPath(baseFilename);
}

bool FileOutputManager::writeFile(const std::string& filename,
                                   const std::string& content) {
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
