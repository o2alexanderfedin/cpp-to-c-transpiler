#include "SourceLocationMapper.h"
#include "clang/Basic/Diagnostic.h"
#include <string>

using namespace clang;
using namespace llvm;

SourceLocationMapper::SourceLocationMapper(FileManager &FM,
                                           DiagnosticsEngine &Diag)
    : SM(std::make_unique<SourceManager>(Diag, FM)) {}

SourceLocationMapper::~SourceLocationMapper() = default;

FileID SourceLocationMapper::registerFile(StringRef filePath) {
  return ensureFileRegistered(filePath);
}

SourceLocation SourceLocationMapper::getStartOfFile(StringRef filePath) {
  FileID FID = ensureFileRegistered(filePath);
  return SM->getLocForStartOfFile(FID);
}

SourceLocation SourceLocationMapper::getLocation(StringRef filePath,
                                                 unsigned line,
                                                 unsigned column) {
  // Validate line/column (1-based, must be positive)
  if (line == 0 || column == 0) {
    // Fall back to start of file instead of returning invalid location
    return getStartOfFile(filePath);
  }

  // Check if line is within supported range
  if (line > MAX_LINES) {
    // Fall back to start of file if line exceeds buffer capacity
    return getStartOfFile(filePath);
  }

  FileID FID = ensureFileRegistered(filePath);
  return SM->translateLineCol(FID, line, column);
}

SourceLocation
SourceLocationMapper::mapFromCppLocation(StringRef targetFilePath,
                                         SourceLocation cppLoc,
                                         SourceManager &cppSM) {
  // If C++ location is invalid, return start of target file
  if (cppLoc.isInvalid()) {
    return getStartOfFile(targetFilePath);
  }

  // Get line and column from C++ location
  unsigned line = cppSM.getSpellingLineNumber(cppLoc);
  unsigned column = cppSM.getSpellingColumnNumber(cppLoc);

  // Create corresponding location in C file
  return getLocation(targetFilePath, line, column);
}

FileID SourceLocationMapper::ensureFileRegistered(StringRef filePath) {
  // Check cache first
  auto it = FileCache.find(filePath);
  if (it != FileCache.end()) {
    return it->second;
  }

  // Create synthetic buffer for this file
  auto Buffer = createBufferForFile(filePath);

  // Register with SourceManager
  FileID FID = SM->createFileID(std::move(Buffer), SrcMgr::C_User);

  // Cache the FileID
  FileCache[filePath] = FID;

  return FID;
}

std::unique_ptr<MemoryBuffer>
SourceLocationMapper::createBufferForFile(StringRef filePath) {
  // Create a buffer with MAX_LINES lines
  // Each line has enough content to support column queries (80 characters)
  // This allows translateLineCol() to work up to line MAX_LINES, column 80

  // Allocate string with placeholder content on each line
  std::string content;
  content.reserve(MAX_LINES * 81); // 80 chars + newline per line

  // Create lines with spaces to support column positions
  // Using spaces instead of actual content keeps it minimal
  for (unsigned i = 0; i < MAX_LINES; ++i) {
    // Add 80 spaces to support column positions up to 80
    content.append(80, ' ');
    content += '\n';
  }

  // Create MemoryBuffer with the content
  // The buffer is identified by filePath for debugging/display purposes
  return MemoryBuffer::getMemBufferCopy(content, filePath);
}
