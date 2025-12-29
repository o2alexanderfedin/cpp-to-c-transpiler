# C AST Node Location Tracking Implementation

## Executive Summary

**Objective**: Implement node location tracking architecture to eliminate duplicate enum/struct declarations and ensure method declarations appear in correct header files.

**Current Status**: Phase 1 Complete (3/3 tasks) - Infrastructure added and building successfully

**Test Results**:
- Current: 1/5 tests passing (20%)
- Target: 5/5 tests passing (100%)

## Architecture Overview

### Core Principle
Each C AST node has exactly ONE output file location, preventing duplicate declarations across multiple .h/.c files.

### Three-Stage Pipeline

The transpiler operates as a 3-stage pipeline:

1. **Stage 1: C++ AST Generation** (Clang Frontend)
   - Input: C++ source files
   - Output: C++ AST
   - Responsibility: Parsing and semantic analysis

2. **Stage 2: C++ AST → C AST Translation** (CppToCVisitor)
   - Input: C++ AST from Stage 1
   - Output: C AST representing equivalent C code
   - Responsibility: Transformation decisions, deduplication
   - **THIS IS WHERE NODE LOCATION TRACKING HAPPENS**

3. **Stage 3: C Code Emission** (CodeGenerator)
   - Input: C AST from Stage 2
   - Output: C source files (.h and .c)
   - Responsibility: Text generation only (NO translation decisions)

## Phase 1: Infrastructure (COMPLETE ✅)

### Task 1.1: TargetContext Extension ✅

**Added to `include/TargetContext.h`:**
```cpp
// Node location tracking
std::map<const clang::Decl*, std::string> nodeToLocation;

// Global deduplication maps
std::map<std::string, clang::EnumDecl*> globalEnums;
std::map<std::string, clang::RecordDecl*> globalStructs;

// Public methods
clang::EnumDecl* findEnum(const std::string& name);
clang::RecordDecl* findStruct(const std::string& name);
void recordNode(const clang::Decl* node, const std::string& location);
std::string getLocation(const clang::Decl* node) const;
```

**Implementation in `src/TargetContext.cpp`:**
- `findEnum()`: Lookup existing enum by name
- `findStruct()`: Lookup existing struct by name
- `recordNode()`: Store node location and register in type-specific maps
- `getLocation()`: Retrieve node's output file location

**Purpose**: Centralized tracking of all C AST nodes and their output locations

### Task 1.2: PathMapper Extension ✅

**Added to `include/PathMapper.h`:**
```cpp
void setNodeLocation(const clang::Decl* node, const std::string& location);
std::string getNodeLocation(const clang::Decl* node) const;
std::vector<const clang::Decl*> getAllNodesForFile(const std::string& file) const;
```

**Implementation in `src/PathMapper.cpp`:**
- `setNodeLocation()`: Delegates to TargetContext::recordNode()
- `getNodeLocation()`: Delegates to TargetContext::getLocation()
- `getAllNodesForFile()`: Returns all declarations for specific output file

**Purpose**: File-oriented view of node locations, supporting file-based emission

### Task 1.3: DependencyTracker Creation ✅

**New files created:**
- `include/DependencyTracker.h`
- `src/DependencyTracker.cpp`

**Public interface:**
```cpp
void addDependency(const std::string& file, const std::string& dependency);
std::vector<std::string> getDependenciesForFile(const std::string& file) const;
void clearDependenciesForFile(const std::string& file);
void clearAll();
```

**Implementation:**
- Uses `std::map<std::string, std::set<std::string>>` for automatic deduplication
- Prevents self-dependencies
- Returns sorted results for deterministic output

**Purpose**: Track which output files depend on which headers for #include generation

**Build Integration**: Added `src/DependencyTracker.cpp` to CMakeLists.txt

### Build Verification ✅

```bash
cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/build_working_new
make cpptoc -j8
# Result: [100%] Built target cpptoc
```

All Phase 1 code compiles successfully with no errors.

## Phase 2: Visitor Logic Updates (IN PROGRESS)

### Current Visitor Architecture

**CppToCVisitor** delegates to specialized handlers:
- `EnumTranslator` (m_enumTranslator) - handles enum translation
- `TypedefGenerator` (m_typedefGenerator) - handles typedef generation
- Methods still handled directly in VisitCXXMethodDecl

### Task 2.1: Update VisitEnumDecl (PENDING)

**Current behavior** (`src/CppToCVisitor.cpp:171-247`):
```cpp
bool CppToCVisitor::VisitEnumDecl(EnumDecl *ED) {
  // ... filtering logic ...

  // Delegate to EnumTranslator
  clang::Decl* C_Enum = m_enumTranslator->handleDecl(ED, ctx);

  // PROBLEM: Always adds enum to C_TranslationUnit
  C_TranslationUnit->addDecl(C_Enum);  // Line 226

  return true;
}
```

**Required changes**:
```cpp
// After line 199 (after EnumTranslator creates C_Enum):

// Deduplication check
std::string enumName = llvm::dyn_cast<clang::EnumDecl>(C_Enum)->getNameAsString();
clang::EnumDecl* existingEnum = targetCtx.findEnum(enumName);

if (existingEnum) {
  // Enum already exists globally - reuse it, don't add to C_TU
  llvm::outs() << "  -> Reusing existing enum: " << enumName << "\n";

  // Update enum constant mappings to point to existing enum
  if (ED->isScoped()) {
    // Update enumConstantMap to use existing enum's constants
    // ... (existing logic at lines 231-242 but with existingEnum)
  }
} else {
  // New enum - record location and add to C_TU
  std::string targetFile = pathMapper->mapSourceToTarget(sourceFile);
  targetCtx.recordNode(C_Enum, targetFile);
  C_TranslationUnit->addDecl(C_Enum);

  llvm::outs() << "  -> New enum " << enumName << " added to C_TU for " << targetFile << "\n";

  // Update enumConstantMap (existing logic at lines 231-242)
}
```

### Task 2.2: Update VisitCXXRecordDecl (PENDING)

**Current behavior** (`src/CppToCVisitor.cpp:316-onwards`):
```cpp
bool CppToCVisitor::VisitCXXRecordDecl(CXXRecordDecl *D) {
  // ... filtering logic ...
  // ... edge case handling ...

  // Check local deduplication only
  if (cppToCMap.find(D) != cppToCMap.end())
    return true;  // Line 361-362

  // Build struct
  RecordDecl *CStruct = Builder.structDecl(D->getName(), fields);  // Line 390
  cppToCMap[D] = CStruct;  // Line 393

  // Add to C_TU (somewhere after line 396)
  C_TranslationUnit->addDecl(CStruct);

  return true;
}
```

**Required changes**:
```cpp
// After line 390 (after struct creation):

// Global deduplication check
std::string structName = CStruct->getNameAsString();
clang::RecordDecl* existingStruct = targetCtx.findStruct(structName);

if (existingStruct) {
  // Struct already exists globally - reuse it
  llvm::outs() << "  -> Reusing existing struct: " << structName << "\n";
  cppToCMap[D] = existingStruct;
  // Don't add to C_TU
} else {
  // New struct - record location and add to C_TU
  std::string targetFile = pathMapper->mapSourceToTarget(sourceFile);
  targetCtx.recordNode(CStruct, targetFile);
  cppToCMap[D] = CStruct;

  // Only add to C_TU if should be in this file
  // (existing smart filtering logic continues...)
  C_TranslationUnit->addDecl(CStruct);

  llvm::outs() << "  -> New struct " << structName << " added to C_TU for " << targetFile << "\n";
}
```

### Task 2.3: Update VisitCXXMethodDecl (PENDING)

**Purpose**: Record output location for each method's C function

**Required changes** (in `src/CppToCVisitor.cpp` in VisitCXXMethodDecl):
```cpp
// After creating C function declaration (C_FuncDecl):

// Record method location
if (C_FuncDecl && pathMapper) {
  std::string targetFile = pathMapper->mapSourceToTarget(sourceFile);
  pathMapper->setNodeLocation(C_FuncDecl, targetFile);

  llvm::outs() << "  -> Recorded method location: "
               << C_FuncDecl->getNameAsString()
               << " -> " << targetFile << "\n";
}
```

**Note**: Methods are NOT deduplicated (each class has unique methods)

### Task 2.4: Update VisitTypeAliasDecl (PENDING)

**Current behavior** (`src/CppToCVisitor.cpp:250-285`):
```cpp
bool CppToCVisitor::VisitTypeAliasDecl(TypeAliasDecl *TAD) {
  // ... filtering logic ...

  // Generate C typedef
  clang::TypedefDecl* C_Typedef = m_typedefGenerator->generateTypedef(info);

  // PROBLEM: No deduplication, no recording

  return true;
}
```

**Required changes**:
```cpp
// After line 274 (after typedef generation):

if (C_Typedef) {
  std::string typedefName = C_Typedef->getNameAsString();

  // Deduplication check (typedefs use same global map as structs)
  // TODO: Add globalTypedefs map to TargetContext if needed

  // Record location
  std::string targetFile = pathMapper->mapSourceToTarget(sourceFile);
  targetCtx.recordNode(C_Typedef, targetFile);

  llvm::outs() << "  -> C typedef " << typedefName
               << " recorded for " << targetFile << "\n";
}
```

## Phase 3: Code Generation Updates (PENDING)

### Current CodeGenerator Architecture

**Problem**: CodeGenerator currently emits all declarations from C_TranslationUnit without file-based filtering

### Task 3.1: Modify Header Emission (PENDING)

**Required changes** in `src/CodeGenerator.cpp`:

```cpp
// Current approach (WRONG):
void emitHeader(const std::string& headerPath, TranslationUnitDecl* TU) {
  // Emit ALL declarations from TU to header
  for (Decl* D : TU->decls()) {
    emitDeclaration(D);
  }
}

// New approach (CORRECT):
void emitHeader(const std::string& headerPath, TranslationUnitDecl* TU) {
  // Get all nodes for this specific header file
  std::vector<const Decl*> nodesForThisFile =
    pathMapper->getAllNodesForFile(headerPath);

  // Only emit declarations (not function bodies)
  for (const Decl* D : nodesForThisFile) {
    emitDeclarationOnly(D);  // New method: declaration without body
  }
}
```

### Task 3.2: Modify Implementation Emission (PENDING)

```cpp
void emitImplementation(const std::string& implPath, TranslationUnitDecl* TU) {
  // Get corresponding header path
  std::string headerPath = implPath;  // Convert .c to .h

  // Emit #include for own header
  emit("#include \"" + getFilename(headerPath) + "\"\n\n");

  // Get all nodes for this implementation file
  std::vector<const Decl*> nodesForThisFile =
    pathMapper->getAllNodesForFile(implPath);

  // Only emit function bodies (not declarations)
  for (const Decl* D : nodesForThisFile) {
    if (auto* FD = dyn_cast<FunctionDecl>(D)) {
      emitFunctionBody(FD);  // Body only
    }
  }
}
```

### Task 3.3: Update Include Generation (PENDING)

```cpp
void emitIncludes(const std::string& filePath) {
  // Get dependencies for this file
  std::vector<std::string> deps = dependencyTracker->getDependenciesForFile(filePath);

  // Emit #include for each dependency
  for (const std::string& depPath : deps) {
    std::string depFilename = getFilename(depPath);
    emit("#include \"" + depFilename + "\"\n");
  }
  emit("\n");
}
```

## Phase 4: Testing & Validation (PENDING)

### Current Test Results

```
Total:  5 projects
Passed: 1 (Math Library)
Failed: 4
Pass Rate: 1/5 (20%)
```

### Test Breakdown

1. **01-game-logic** (Math Library) - ✅ PASS
   - This is the baseline that works

2. **02-custom-container** - ❌ FAIL (C build failed)
   - Likely: Duplicate struct declarations
   - Likely: Missing method declarations in headers

3. **03-state-machine** - ❌ FAIL (C build failed)
   - Likely: Duplicate enum declarations (GameState)
   - Likely: Missing state transition function declarations

4. **04-simple-parser** - ❌ FAIL (Transpilation failed)
   - Most severe: Transpiler crashes or errors
   - Needs investigation of crash logs

5. **05-game-logic** - ❌ FAIL (C build failed)
   - Likely: Entity struct duplication
   - Likely: CollisionDetector method declarations missing

### Expected Results After Implementation

All tests should pass (100%) with:
- Zero duplicate enum declarations
- Zero duplicate struct declarations
- All method declarations in correct header files
- Proper #include directives for dependencies

## Phase 5: Cleanup & Documentation (PENDING)

### Task 5.1: Remove Obsolete Code
- Remove any old deduplication attempts
- Clean up debug logging
- Remove commented-out code

### Task 5.2: Git Commit
```bash
git add -A
git commit -m "feat(transpiler): implement C AST node location tracking

- Add node location tracking to TargetContext
- Extend PathMapper with location methods
- Create DependencyTracker for include management
- Update visitor logic for enum/struct deduplication
- Modify code generation for file-based emission
- Achieve 100% validation pass rate (5/5 tests)

Fixes duplicate enum/struct declarations
Ensures method declarations in correct headers

Phase 1: Infrastructure ✅
Phase 2: Visitor Logic ✅
Phase 3: Code Generation ✅
Phase 4: Testing & Validation ✅
Phase 5: Cleanup & Documentation ✅

🤖 Generated with Claude Code

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>"
```

### Task 5.3: Create implementation-notes.md ✅
This document.

### Task 5.4: Create SUMMARY.md
See SUMMARY.md file.

## Deduplication Algorithm

### For Enums

```
When encountering enum (e.g., GameState):
1. EnumTranslator creates C EnumDecl
2. Check if globalEnums["GameState"] exists
   - If YES:
     * Reuse existing node
     * Don't add to C_TU
     * Update enum constant mappings
   - If NO:
     * Record in globalEnums
     * Record location in nodeToLocation
     * Add to C_TU
```

### For Structs

```
When encountering class (e.g., Point):
1. CNodeBuilder creates C RecordDecl
2. Check if globalStructs["Point"] exists
   - If YES:
     * Reuse existing node
     * Update cppToCMap
     * Don't add to C_TU
   - If NO:
     * Record in globalStructs
     * Record location in nodeToLocation
     * Update cppToCMap
     * Add to C_TU (if smart filtering allows)
```

### For Methods

```
When encountering method (e.g., Entity::getX):
1. Create C function (e.g., Entity_getX)
2. Record location in nodeToLocation
3. Add to C_TU

Note: Methods are NOT deduplicated (each class has unique methods)
```

## Emission Rules

### For Header Files (.h)

```
For each C node with location "path/to/file.c":
1. Map to header: "path/to/file.h"
2. Emit DECLARATION ONLY:
   - enum GameState { ... };
   - struct Entity { ... };
   - extern float Entity_getX(struct Entity* this);
3. Do NOT emit function bodies
```

### For Implementation Files (.c)

```
For each C node with location "path/to/file.c":
1. Emit #include "file.h"
2. Emit #includes for dependencies (from DependencyTracker)
3. Emit FUNCTION BODIES ONLY:
   - float Entity_getX(struct Entity* this) { return this->x; }
4. Do NOT emit enum/struct declarations (already in .h)
```

## File Structure

```
src/
  TargetContext.cpp       [Modified] - Node tracking methods
  PathMapper.cpp          [Modified] - Location delegation methods
  DependencyTracker.cpp   [New] - Dependency management
  CppToCVisitor.cpp       [To Modify] - Deduplication logic
  CodeGenerator.cpp       [To Modify] - File-based emission

include/
  TargetContext.h         [Modified] - Node tracking maps
  PathMapper.h            [Modified] - Location tracking API
  DependencyTracker.h     [New] - Dependency tracking API
  CppToCVisitor.h         [No changes needed]
  CodeGenerator.h         [To Modify] - Emission method signatures

CMakeLists.txt            [Modified] - Added DependencyTracker.cpp
```

## Testing Strategy

### Unit Tests (Future)
- Test TargetContext::findEnum() with existing/non-existing enums
- Test PathMapper::getAllNodesForFile() filtering
- Test DependencyTracker deduplication

### Integration Tests (Current)
- Run validate-all.sh
- Verify 5/5 tests pass
- Check transpiled .h files for duplicates
- Check transpiled .c files for missing declarations

## Known Issues & Solutions

### Issue 1: Enum Constants Not Found
**Symptom**: Undefined reference to `GameState__Menu`
**Cause**: Enum defined in one file, used in another, not included
**Solution**: DependencyTracker adds dependency, includes GameState.h

### Issue 2: Duplicate Struct Definitions
**Symptom**: "error: redefinition of struct Entity"
**Cause**: Entity struct emitted in both main.h and Entity.h
**Solution**: globalStructs map ensures only one definition

### Issue 3: Missing Method Declarations
**Symptom**: "error: implicit declaration of function 'Entity_getX'"
**Cause**: Method defined in Entity.c but not declared in Entity.h
**Solution**: Phase 3 ensures declarations in .h, bodies in .c

## Success Criteria

✅ **Phase 1 Complete**: All infrastructure compiles without errors
⏳ **Phase 2**: Visitor logic updated with deduplication
⏳ **Phase 3**: Code generator emits file-based output
⏳ **Phase 4**: validate-all.sh shows 5/5 (100%) pass rate
⏳ **Phase 5**: Code committed with documentation

**Final Goal**: Zero duplicate declarations, all tests passing, clean architecture.
