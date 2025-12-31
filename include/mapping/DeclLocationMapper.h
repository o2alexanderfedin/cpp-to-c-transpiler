/**
 * @file DeclLocationMapper.h
 * @brief Utility for extracting source file paths from AST node locations
 *
 * Bridges Clang AST (high-level) with PathMapper (low-level string utility).
 * Encapsulates the boilerplate of getting source file path from a declaration's location.
 *
 * Design Principles:
 * - Single Responsibility: Extract source paths from AST nodes
 * - Dependency Inversion: High-level utility that depends on both Clang AST and PathMapper
 * - Encapsulation: Hides SourceManager complexity from handlers
 */

#pragma once

#include "mapping/PathMapper.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include <string>

namespace cpptoc {

/**
 * @class DeclLocationMapper
 * @brief Maps AST declarations to their target output file paths
 *
 * This utility class extracts the source file path from a declaration's location
 * and maps it to the target output path using PathMapper.
 *
 * **Separation of Concerns**:
 * - Clang AST layer: DeclLocationMapper (this class)
 * - String path mapping: PathMapper (low-level utility)
 *
 * **Usage**:
 * @code
 * DeclLocationMapper locMapper(pathMapper);
 * std::string targetPath = locMapper.getTargetPath(cppCtx, classDecl);
 * @endcode
 */
class DeclLocationMapper {
public:
    /**
     * @brief Construct with required PathMapper reference
     * @param mapper PathMapper for source→target path mapping
     */
    explicit DeclLocationMapper(PathMapper& mapper) : pathMapper_(mapper) {}

    /**
     * @brief Get target output path for a declaration's source file location
     * @param cppASTContext C++ ASTContext containing SourceManager
     * @param D Declaration to extract source file location from (must not be null)
     * @return Output path (e.g., "/output/Point_transpiled.c")
     *
     * **Algorithm**:
     * 1. Extract source file path from D->getLocation() using SourceManager
     * 2. Map source path to target path via PathMapper
     * 3. Return target path
     *
     * **Fallback**: For in-memory sources (e.g., tests), uses "<stdin>" as source path
     *
     * @pre D != nullptr (asserted)
     */
    std::string getTargetPath(const clang::ASTContext& cppASTContext, const clang::Decl* D) const;

private:
    PathMapper& pathMapper_; ///< PathMapper for string-level path mapping
};

} // namespace cpptoc
