#ifndef SOURCELOCATIONMAPPER_H
#define SOURCELOCATIONMAPPER_H

#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceLocation.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/ADT/StringMap.h"
#include "llvm/ADT/StringRef.h"
#include "llvm/Support/MemoryBuffer.h"
#include <memory>

/// SourceLocationMapper creates valid clang::SourceLocation objects for
/// synthetic C AST nodes.
///
/// Purpose:
/// - Enable C AST nodes to have valid source locations
/// - Support CodeGenerator emitting #line directives for debugging
/// - Map generated C code back to original C++ source (optional)
///
/// Design:
/// - Manages a SourceManager dedicated to C output files
/// - Registers target C files with synthetic MemoryBuffers
/// - Creates SourceLocations at file start or specific line/column positions
/// - Caches FileIDs to avoid re-registration
///
/// Usage:
///   SourceLocationMapper mapper(fileMgr, diag);
///   SourceLocation loc = mapper.getStartOfFile("output/game.c");
///   // Use loc when creating C AST nodes
///
/// Thread Safety: Not thread-safe. Use from single thread.
///
class SourceLocationMapper {
public:
  /// Create a SourceLocationMapper with its own SourceManager.
  ///
  /// \param FM FileManager (typically shared across transpiler)
  /// \param Diag DiagnosticsEngine (typically shared across transpiler)
  SourceLocationMapper(clang::FileManager &FM, clang::DiagnosticsEngine &Diag);

  /// Destructor
  ~SourceLocationMapper();

  /// Register a target C file and return its FileID.
  ///
  /// Files are registered lazily - first call creates the FileID,
  /// subsequent calls return cached FileID.
  ///
  /// \param filePath Path to target C file (e.g., "output/game.c")
  /// \return FileID for the registered file
  clang::FileID registerFile(llvm::StringRef filePath);

  /// Get SourceLocation for the start of a file (line 1, column 1).
  ///
  /// Registers the file if not already registered.
  ///
  /// \param filePath Path to target C file
  /// \return Valid SourceLocation pointing to start of file
  clang::SourceLocation getStartOfFile(llvm::StringRef filePath);

  /// Get SourceLocation at a specific line and column in a file.
  ///
  /// Registers the file if not already registered.
  /// Line and column numbers are 1-based.
  ///
  /// \param filePath Path to target C file
  /// \param line Line number (1-based)
  /// \param column Column number (1-based)
  /// \return SourceLocation at the specified position, or start of file if
  /// line/column are out of range (never returns invalid location)
  clang::SourceLocation getLocation(llvm::StringRef filePath, unsigned line,
                                    unsigned column);

  /// Map a C++ source location to a C target location (for debugging).
  ///
  /// This creates a C location at the same line/column as the C++ location.
  /// Useful for maintaining line correspondence between C++ input and C output.
  ///
  /// \param targetFilePath Path to target C file
  /// \param cppLoc SourceLocation from C++ source (from C++ SourceManager)
  /// \param cppSM SourceManager from C++ AST (to query line/column)
  /// \return SourceLocation in C file at same line/column, or start of file if
  /// cppLoc is invalid
  clang::SourceLocation mapFromCppLocation(llvm::StringRef targetFilePath,
                                           clang::SourceLocation cppLoc,
                                           clang::SourceManager &cppSM);

  /// Get the underlying SourceManager (for advanced use cases).
  ///
  /// \return Reference to the SourceManager managing C file locations
  clang::SourceManager &getSourceManager() { return *SM; }

private:
  /// SourceManager for C file locations (owned by this mapper)
  std::unique_ptr<clang::SourceManager> SM;

  /// Cache: file path → FileID
  llvm::StringMap<clang::FileID> FileCache;

  /// Maximum number of lines to support in synthetic buffers
  /// This determines the size of the newline-only buffer created for each file
  static constexpr unsigned MAX_LINES = 10000;

  /// Ensure file is registered, return its FileID.
  ///
  /// If file is already in cache, returns cached FileID.
  /// Otherwise, creates a synthetic buffer and registers it.
  ///
  /// \param filePath Path to target C file
  /// \return FileID for the file
  clang::FileID ensureFileRegistered(llvm::StringRef filePath);

  /// Create a synthetic MemoryBuffer for a file.
  ///
  /// Creates a buffer containing MAX_LINES newlines to support
  /// line/column queries up to MAX_LINES.
  ///
  /// \param filePath Path to use as buffer identifier
  /// \return MemoryBuffer with newline-only content
  std::unique_ptr<llvm::MemoryBuffer>
  createBufferForFile(llvm::StringRef filePath);
};

#endif // SOURCELOCATIONMAPPER_H
