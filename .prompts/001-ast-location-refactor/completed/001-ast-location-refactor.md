# Refactor: AST Node Location-Based File Organization

## Objective

Refactor the C++ to C transpiler to use AST node locations instead of instance variables (`m_currentSourceFile`, `m_currentTargetPath`) to determine file organization. This architectural change eliminates redundancy and fixes the critical bug where function declarations disappear between `addDecl()` and iteration.

**Why This Matters**: The current architecture tracks file locations in instance variables that can become stale or incorrect. AST nodes inherently know their source file location, which should be the single source of truth.

## Context

**Current Architecture Problem**:
- CppToCVisitor has instance variables: `m_currentSourceFile` and `m_currentTargetPath`
- These are set once during visitor initialization
- Used throughout the visitor to determine where to place C AST nodes
- **BUG**: 13 FunctionDecls added via `addDecl()` but 0 found during iteration
- **ROOT CAUSE**: File organization logic is inconsistent due to stale instance variables

**Technical Specification to Follow**:

```cpp
// Step 1: Every C++ node knows its source file
SourceLocation loc = cppNode->getLocation();
SourceManager &SM = Context.getSourceManager();
FileID fid = SM.getFileID(loc);
StringRef sourceFile = SM.getFileEntryForID(fid)->getName();

// Step 2: Map source file → target file
std::string targetFile = pathMapper->mapSourceToTarget(sourceFile);

// Step 3: Get the C_TranslationUnit for that target file
clang::TranslationUnitDecl *C_TU = pathMapper->getOrCreateTU(targetFile);

// Step 4: Create C node and add to C_TU
clang::RecordDecl *cRecordDecl = Builder.recordDecl(...);
C_TU->addDecl(cRecordDecl);
```

**Key Principles**:
1. Source location is in the AST node (via `getLocation()`)
2. PathMapper is a singleton (already implemented)
3. One C_TU per output file (already implemented)
4. Declarations find their home based on node location (to be implemented)

**Files to Modify**:
- @/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/CppToCVisitor.h (remove instance variables)
- @/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCVisitor.cpp (refactor all usages)

**Instance Variable Usages Found** (17 occurrences in CppToCVisitor.cpp):
- Lines 38-39: Constructor initialization
- Line 243: `recordNode(C_EnumDecl, m_currentTargetPath)`
- Line 324: `recordNode(C_Typedef, m_currentTargetPath)`
- Line 458: `getBaseName(m_currentSourceFile)`
- Lines 463-464: Debug logging
- Line 499: `setNodeLocation(existingStruct, m_currentTargetPath)`
- Line 556: `recordNode(CStruct, m_currentTargetPath)`
- Line 873: `setNodeLocation(CFunc, m_currentTargetPath)`
- Lines 912-913: JSON logging with source and target paths
- Lines 1206-1207: JSON logging with source and target paths

## Requirements

### 1. Create Helper Method for Location Extraction

Add to CppToCVisitor class:

```cpp
// Get source file path from C++ AST node location
std::string getSourceFileFromNode(const clang::Decl* node) const {
  if (!node) return "";

  clang::SourceLocation loc = node->getLocation();
  if (loc.isInvalid()) return "";

  clang::SourceManager &SM = Context.getSourceManager();
  clang::FileID fid = SM.getFileID(loc);
  const clang::FileEntry *entry = SM.getFileEntryForID(fid);

  return entry ? entry->getName().str() : "";
}

// Get target file path and C_TU for a C++ AST node
std::pair<std::string, clang::TranslationUnitDecl*>
getTargetForNode(const clang::Decl* cppNode) {
  std::string sourceFile = getSourceFileFromNode(cppNode);
  if (sourceFile.empty()) {
    llvm::outs() << "[ERROR] Cannot determine source file for node\n";
    return {"", nullptr};
  }

  std::string targetPath = pathMapper->mapSourceToTarget(sourceFile);
  clang::TranslationUnitDecl* C_TU = pathMapper->getOrCreateTU(targetPath);

  return {targetPath, C_TU};
}
```

### 2. Refactor All Instance Variable Usages

Replace each occurrence of `m_currentSourceFile` or `m_currentTargetPath` with calls to the helper methods:

**Before**:
```cpp
targetCtx.recordNode(C_EnumDecl, m_currentTargetPath);
```

**After**:
```cpp
auto [targetPath, C_TU] = getTargetForNode(EnumDecl);
targetCtx.recordNode(C_EnumDecl, targetPath);
```

**Before**:
```cpp
std::string currentBaseName = getBaseName(m_currentSourceFile);
llvm::outs() << "  -> Current file: " << m_currentSourceFile
             << " (base: " << currentBaseName << ") -> " << m_currentTargetPath << "\n";
```

**After**:
```cpp
auto [targetPath, C_TU] = getTargetForNode(RD);
std::string sourceFile = getSourceFileFromNode(RD);
std::string currentBaseName = getBaseName(sourceFile);
llvm::outs() << "  -> Current file: " << sourceFile
             << " (base: " << currentBaseName << ") -> " << targetPath << "\n";
```

### 3. Update Constructor Signature

Remove the `currentFile` parameter from CppToCVisitor constructor:

**Before**:
```cpp
CppToCVisitor(clang::ASTContext &Context,
              clang::CNodeBuilder &Builder,
              TargetContext &targetCtx,
              cpptoc::FileOriginTracker &tracker,
              cpptoc::PathMapper* pathMapper_param,
              const std::string& currentFile)
    : Context(Context), Builder(Builder), targetCtx(targetCtx),
      Mangler(), fileOriginTracker(tracker),
      pathMapper(pathMapper_param),
      m_currentSourceFile(currentFile),
      m_currentTargetPath(pathMapper_param ? pathMapper_param->mapSourceToTarget(currentFile) : ""),
      ...
```

**After**:
```cpp
CppToCVisitor(clang::ASTContext &Context,
              clang::CNodeBuilder &Builder,
              TargetContext &targetCtx,
              cpptoc::FileOriginTracker &tracker,
              cpptoc::PathMapper* pathMapper_param)
    : Context(Context), Builder(Builder), targetCtx(targetCtx),
      Mangler(), fileOriginTracker(tracker),
      pathMapper(pathMapper_param),
      ...
```

### 4. Remove Instance Variable Declarations

From CppToCVisitor.h, delete:

```cpp
// Phase 1.2: Current source and target file paths for node location tracking
std::string m_currentSourceFile;
std::string m_currentTargetPath;
```

### 5. Update All Call Sites

Find and update all places where CppToCVisitor is constructed (likely in CppToCConsumer.cpp) to remove the `currentFile` parameter.

### 6. Critical: Update addDecl() Calls

**Most Important**: Wherever we call `C_TranslationUnit->addDecl()`, ensure we're using the C_TU obtained from `getTargetForNode()`, not a cached instance variable.

**Before**:
```cpp
// Using instance variable (WRONG)
clang::FunctionDecl *CFunc = Builder.funcDecl(...);
C_TranslationUnit->addDecl(CFunc);  // C_TranslationUnit might be wrong!
```

**After**:
```cpp
// Using node location (CORRECT)
auto [targetPath, C_TU] = getTargetForNode(MethodDecl);
clang::FunctionDecl *CFunc = Builder.funcDecl(...);
C_TU->addDecl(CFunc);  // Guaranteed correct C_TU for this specific node
```

## Output Specification

Save all changes to:
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/CppToCVisitor.h`
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCVisitor.cpp`
- Any other files that construct CppToCVisitor

Create a summary file: `.prompts/001-ast-location-refactor/ast-location-refactor.md`

## Metadata Requirements

Include in output file (`ast-location-refactor.md`):

```xml
<confidence>High|Medium|Low</confidence>
<dependencies>
  - PathMapper singleton must be working
  - SourceManager available in ASTContext
  - All C++ nodes have valid SourceLocation
</dependencies>
<open_questions>
  - Are there any C++ nodes created synthetically without valid SourceLocation?
  - Do we need fallback logic for invalid locations?
</open_questions>
<assumptions>
  - Every C++ AST node we visit has a valid getLocation()
  - SourceManager can reliably map SourceLocation to file paths
  - PathMapper.mapSourceToTarget() never returns empty string for valid source files
</assumptions>
```

## SUMMARY.md Requirement

Create `.prompts/001-ast-location-refactor/SUMMARY.md` with:

**One-liner**: Refactored file organization to use AST node intrinsic locations instead of stale instance variables

**Version**: v1

**Key Findings**:
- [Number] instance variable usages replaced with location queries
- Helper methods `getSourceFileFromNode()` and `getTargetForNode()` added
- Constructor signature simplified (removed `currentFile` parameter)
- All `addDecl()` calls now use dynamically-determined C_TU

**Files Modified**:
- CppToCVisitor.h (removed instance variables, added helper methods)
- CppToCVisitor.cpp (refactored all usages)
- [Any other files that construct CppToCVisitor]

**Decisions Needed**:
- Fallback strategy if SourceLocation is invalid
- Error handling for nodes without file information

**Blockers**:
- None (can proceed with refactor)

**Next Step**:
- Rebuild transpiler and run validation suite to verify declarations now persist

## Success Criteria

- ✅ Helper methods `getSourceFileFromNode()` and `getTargetForNode()` implemented
- ✅ All 17 instance variable usages replaced with location queries
- ✅ Instance variables `m_currentSourceFile` and `m_currentTargetPath` removed from header
- ✅ Constructor signature updated and all call sites fixed
- ✅ Code compiles without errors
- ✅ Each `addDecl()` call uses C_TU obtained from `getTargetForNode()`
- ✅ Metadata section included in output file
- ✅ SUMMARY.md created with all required sections
- ✅ One-liner is substantive and describes the actual change made

## Quality Controls

Before submitting:

1. **Verification Checklist**:
   - [ ] Searched entire codebase for remaining `m_currentSourceFile` usages
   - [ ] Searched entire codebase for remaining `m_currentTargetPath` usages
   - [ ] Verified all `addDecl()` calls use location-based C_TU
   - [ ] Compiled code successfully
   - [ ] Checked that no hardcoded file paths remain

2. **Testing**:
   - [ ] Run transpiler on test case: `01-math-library`
   - [ ] Verify JSON logs show same C_TU for addDecl and iteration
   - [ ] Check that function count after addDecl matches count during iteration

3. **Documentation**:
   - [ ] Updated any comments referencing the removed instance variables
   - [ ] Added comments explaining the new location-based approach
