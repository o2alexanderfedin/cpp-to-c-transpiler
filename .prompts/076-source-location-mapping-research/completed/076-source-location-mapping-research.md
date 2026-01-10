# Research: SourceLocation Mapping for C AST Nodes

## Objective

Research and develop a comprehensive solution for creating correct `clang::SourceLocation` objects for C AST nodes in the transpiler. Currently, all handlers use `clang::SourceLocation()` (default/invalid locations), which prevents accurate source mapping in generated C code and limits debugging capabilities.

**Why This Matters**:
- Proper SourceLocations enable accurate line/column reporting in generated C code
- CodeGenerator can emit correct `#line` directives for debugging
- Error messages in generated C code can map back to original C++ source
- Essential for production-quality transpiler output

**Success Definition**: A tested, documented system that:
1. Creates valid SourceLocations for C AST nodes pointing to target C files
2. Optionally preserves line/column mapping from C++ source to C output
3. Works seamlessly with existing PathMapper and TargetContext infrastructure
4. Includes working POC demonstrating the approach in real handlers

## Context

**Building on Previous Work**:
- @.prompts/001-ast-location-refactor/completed/001-ast-location-refactor.md - Established location-based file organization using `getTargetForNode()`
- Current state: File organization works, but C AST nodes have invalid SourceLocations

**Current Problem**:

All handlers create C AST nodes with default SourceLocations:

```cpp
// Example from CppToCVisitor (and all other handlers)
clang::CStyleCastExpr* cCast = clang::CStyleCastExpr::Create(
    cASTContext,
    targetType,
    cppCast->getValueKind(),
    castKind,
    cSubExpr,
    nullptr,  // path
    clang::FPOptionsOverride(),
    cASTContext.getTrivialTypeSourceInfo(targetType),
    clang::SourceLocation(),  // LParenLoc - INVALID!
    clang::SourceLocation()   // RParenLoc - INVALID!
);
```

**Desired Approach** (pseudo-code):

```cpp
// Step 1: Get C++ source location
clang::SourceLocation cppLoc = cppCast->getLParenLoc();

// Step 2: Map to target C file location
clang::SourceLocation targetLoc = sourceLocationMapper->mapToTarget(
    cppLoc,           // Original C++ location
    targetFilePath    // Target C file path from PathMapper
);

// Step 3: Use in C AST node creation
clang::CStyleCastExpr* cCast = clang::CStyleCastExpr::Create(
    cASTContext,
    targetType,
    cppCast->getValueKind(),
    castKind,
    cSubExpr,
    nullptr,
    clang::FPOptionsOverride(),
    cASTContext.getTrivialTypeSourceInfo(targetType),
    targetLoc,  // Proper location!
    targetLoc   // Proper location!
);
```

**Key Components to Research**:
1. `clang::SourceManager` - Manages source file buffers and locations
2. `clang::FileManager` - Handles file system interactions
3. `clang::FileID` - Represents a file in SourceManager
4. `clang::SourceLocation` - Opaque location type (how to create?)
5. `SourceManager::createFileID()` - Registers new files
6. `SourceManager::getLocForStartOfFile()` - Creates locations in files
7. Line/column offset calculations

**Architecture Constraints**:
- Must work with existing C ASTContext (created in TargetContext)
- PathMapper already maps source→target paths
- Each target file has its own TranslationUnitDecl
- SourceManager is per-ASTContext (C++ has one, C has another)

## Requirements

### 1. Deep Research Phase

Conduct comprehensive investigation into Clang's source location system:

#### A. Official Documentation Research

Search and study:
- LLVM/Clang official documentation on SourceManager
- Clang API reference for SourceLocation creation
- FileManager integration with SourceManager
- Best practices for creating synthetic source locations
- How Clang tools (clang-tidy, clang-format) handle source locations

**Key Questions**:
- How do you register a new file with SourceManager?
- How do you create SourceLocations for files not actually parsed?
- Can you create a SourceLocation without an actual file buffer?
- What's the relationship between FileID and SourceLocation?
- How do you get a SourceLocation for a specific line/column in a file?

**Sources to Consult**:
- https://clang.llvm.org/doxygen/classclang_1_1SourceManager.html
- https://clang.llvm.org/doxygen/classclang_1_1SourceLocation.html
- https://clang.llvm.org/doxygen/classclang_1_1FileManager.html
- LLVM documentation on source locations
- Clang mailing list archives for synthetic location creation

#### B. Clang Source Code Analysis

Examine Clang's own codebase for examples:

```bash
# Search for patterns in LLVM source (adapt path as needed)
grep -r "createFileID" /opt/homebrew/opt/llvm/include/clang/
grep -r "getLocForStartOfFile" /opt/homebrew/opt/llvm/include/clang/
grep -r "SourceLocation::getFromRawEncoding" /opt/homebrew/opt/llvm/include/clang/
```

**Find Examples**:
- How does ASTImporter create locations for imported nodes?
- How does Rewriter create locations for rewritten code?
- How do AST matchers handle synthetic locations?
- How does CodeGen create locations for generated code?

#### C. Experimentation Plan

Design experiments to test understanding:

1. **Experiment 1: Register a File**
   - Create a SourceManager
   - Register a target C file path (that doesn't exist yet)
   - Verify FileID creation

2. **Experiment 2: Create Basic Location**
   - Get SourceLocation for start of registered file
   - Verify it's valid (not `isInvalid()`)
   - Print raw encoding to understand structure

3. **Experiment 3: Line/Column Offsets**
   - Create SourceLocation for line 10, column 5
   - Verify SourceManager can decode it back
   - Test boundaries (what if line doesn't exist in buffer?)

4. **Experiment 4: Multiple Files**
   - Register multiple target files (.h and .c)
   - Create locations in each
   - Verify they're distinct and correct

### 2. Design Phase

Based on research, design the solution architecture:

#### A. Component Design

Design a `SourceLocationMapper` class (or similar):

```cpp
// Proposed interface (refine based on research)
class SourceLocationMapper {
public:
    SourceLocationMapper(clang::SourceManager& cSourceManager,
                         clang::FileManager& cFileManager,
                         cpptoc::PathMapper* pathMapper);

    // Map C++ location to corresponding C location
    clang::SourceLocation mapToTarget(
        clang::SourceLocation cppLoc,
        const std::string& targetFilePath
    );

    // Create location at specific line/column in target file
    clang::SourceLocation createLocation(
        const std::string& targetFilePath,
        unsigned line,
        unsigned column
    );

    // Register a target file with SourceManager
    clang::FileID registerTargetFile(const std::string& targetFilePath);

private:
    clang::SourceManager& m_cSourceManager;
    clang::FileManager& m_cFileManager;
    cpptoc::PathMapper* m_pathMapper;

    // Cache FileIDs for registered target files
    std::map<std::string, clang::FileID> m_registeredFiles;
};
```

#### B. Integration Points

Identify where to inject SourceLocationMapper:

1. **Creation**: In TargetContext alongside C ASTContext
2. **Access**: Passed to all handlers (via handler context or global)
3. **Usage**: Every handler uses it when creating C AST nodes

#### C. Migration Strategy

Plan how to refactor all handlers:

```cpp
// Current (17 handlers do this):
Builder.funcDecl(..., clang::SourceLocation(), ...)

// After refactoring:
auto targetLoc = locMapper->mapToTarget(cppDecl->getLocation(), targetPath);
Builder.funcDecl(..., targetLoc, ...)
```

**Handlers to Update** (non-exhaustive):
- VariableHandler
- FunctionHandler
- RecordHandler
- ConstructorHandler
- MethodHandler
- VirtualMethodHandler
- InstanceMethodHandler
- ExceptionHandler
- (All 17+ handlers)

### 3. Proof-of-Concept Phase

Implement and test the solution:

#### A. Create Test File

Create `tests/SourceLocationMapperTest.cpp`:

```cpp
#include "SourceLocationMapper.h"
#include "gtest/gtest.h"
#include "clang/AST/ASTContext.h"
#include "clang/Basic/FileManager.h"
#include "clang/Basic/SourceManager.h"

TEST(SourceLocationMapperTest, RegisterTargetFile) {
    // Test: Can register a target C file path
    // Verify: FileID is valid
}

TEST(SourceLocationMapperTest, CreateLocationInFile) {
    // Test: Create location at line 10, column 5
    // Verify: Location is valid and decodable
}

TEST(SourceLocationMapperTest, MapCppLocationToTarget) {
    // Test: Map C++ source location to C target location
    // Verify: Preserves line/column or maps appropriately
}

TEST(SourceLocationMapperTest, MultipleTargetFiles) {
    // Test: Register both .h and .c target files
    // Verify: Locations in each are distinct
}
```

#### B. Implement SourceLocationMapper

Create files:
- `include/SourceLocationMapper.h`
- `src/SourceLocationMapper.cpp`

Based on research findings, implement:
1. File registration with SourceManager
2. Location creation at specific lines/columns
3. Optional: Mapping from C++ locations to C locations (preserve line numbers)

#### C. Test in Real Handler

Pick one simple handler (e.g., VariableHandler) and apply:

```cpp
// In VariableHandler.cpp (example)
void VariableHandler::handleVariable(const clang::VarDecl* VD) {
    auto [targetPath, C_TU] = getTargetForNode(VD);

    // NEW: Get proper source location
    clang::SourceLocation targetLoc = locMapper->mapToTarget(
        VD->getLocation(),
        targetPath
    );

    // Use in C AST node creation
    clang::VarDecl* cVar = Builder.varDecl(
        /*...*/,
        targetLoc,  // Instead of clang::SourceLocation()
        /*...*/
    );

    C_TU->addDecl(cVar);
}
```

Verify:
- Code compiles
- Location is valid (`!cVar->getLocation().isInvalid()`)
- SourceManager can decode the location back to file/line/column

#### D. Verify in CodeGenerator

Check that CodeGenerator (Stage 3) correctly uses the locations:

```cpp
// In CodeGenerator.cpp
void CodeGenerator::visitFunctionDecl(const clang::FunctionDecl* FD) {
    clang::SourceLocation loc = FD->getLocation();

    if (!loc.isInvalid()) {
        clang::SourceManager& SM = /*...*/;
        unsigned line = SM.getSpellingLineNumber(loc);
        unsigned col = SM.getSpellingColumnNumber(loc);

        // Emit #line directive
        outputFile << "#line " << line << " \""
                   << SM.getFilename(loc) << "\"\n";
    }

    // Emit function code...
}
```

Verify:
- CodeGenerator can extract line/column from C AST node locations
- #line directives point to correct target C files (not C++ source)

### 4. Documentation Phase

Create comprehensive documentation:

#### A. API Documentation

Document SourceLocationMapper:
- Purpose and motivation
- Public interface
- Usage examples
- Integration with TargetContext

#### B. Migration Guide

Create step-by-step guide for refactoring handlers:

```markdown
# How to Add SourceLocation Support to a Handler

1. Get SourceLocationMapper reference (via handler context)
2. For each C AST node creation:
   a. Get C++ source location from original node
   b. Get target path via getTargetForNode()
   c. Call locMapper->mapToTarget(cppLoc, targetPath)
   d. Pass result to Builder methods
3. Update tests to verify locations are valid
```

#### C. Architecture Decision Record

Document key decisions:
- Why we chose this approach over alternatives
- Trade-offs (e.g., preserving line numbers vs. fresh numbering)
- Future extensibility (e.g., column-level precision)

### 5. Verification Checklist

Before considering research complete:

- [ ] **Official Documentation Consulted**
  - [ ] Read SourceManager documentation
  - [ ] Read FileManager documentation
  - [ ] Read SourceLocation documentation
  - [ ] Found examples in official Clang tools

- [ ] **Clang Source Code Examined**
  - [ ] Analyzed ASTImporter or Rewriter examples
  - [ ] Found how Clang creates synthetic locations
  - [ ] Understand FileID registration process

- [ ] **Experiments Completed**
  - [ ] Successfully registered a file with SourceManager
  - [ ] Created valid SourceLocation for registered file
  - [ ] Tested line/column offset calculations
  - [ ] Verified multiple file registration

- [ ] **POC Implementation**
  - [ ] SourceLocationMapper class created
  - [ ] Unit tests written and passing
  - [ ] Applied to at least one real handler
  - [ ] Verified in CodeGenerator

- [ ] **Documentation Created**
  - [ ] API documentation for SourceLocationMapper
  - [ ] Migration guide for refactoring handlers
  - [ ] Architecture decision record

## Output Specification

Save research output to: `.prompts/076-source-location-mapping-research/source-location-mapping-research.md`

**Structure your output as**:

```markdown
# SourceLocation Mapping Research Results

## Executive Summary
[1-2 paragraphs: what was learned, recommended approach]

## Research Findings

### SourceManager API
[Details on how SourceManager works]

### FileManager Integration
[How to register files]

### Creating SourceLocations
[Step-by-step process for creating valid locations]

### Line/Column Mapping
[How to preserve or map line numbers]

## Experiments Conducted

### Experiment 1: File Registration
[What was tested, results]

### Experiment 2: Location Creation
[What was tested, results]

[Continue for all experiments...]

## Recommended Solution

### Architecture
[Proposed SourceLocationMapper design]

### Implementation Plan
[Step-by-step refactoring approach]

### Integration Points
[Where to inject into existing code]

## Proof-of-Concept Results

### Test Results
[Output from SourceLocationMapperTest]

### Handler Integration Example
[Code showing refactored handler]

### CodeGenerator Verification
[Evidence that CodeGenerator uses locations correctly]

## Migration Guide

### Step-by-Step Handler Refactoring
[Detailed guide for updating handlers]

### Testing Strategy
[How to verify each handler]

## Open Questions and Future Work

[Any unresolved issues or potential improvements]

## Appendix

### Code Listings
[Full source of SourceLocationMapper if created]

### References
[All documentation and sources consulted]
```

**Quality Requirements**:
- Use streaming writes (write sections as you complete them, don't accumulate in memory)
- Include actual code examples from experiments
- Cite all sources with URLs
- Mark assumptions vs. verified facts
- Include error cases and limitations discovered

## Metadata Requirements

Include at end of output file:

```xml
<confidence>High|Medium|Low</confidence>
<dependencies>
  - C ASTContext with SourceManager available in TargetContext
  - PathMapper working and accessible to handlers
  - FileManager available in TargetContext
  - [Any others discovered during research]
</dependencies>
<open_questions>
  - Can we create SourceLocations without actual file buffers?
  - Should we preserve C++ line numbers or use fresh numbering?
  - How to handle macro expansions and included files?
  - [Any others that arise during research]
</open_questions>
<assumptions>
  - SourceManager in C ASTContext is independent of C++ SourceManager
  - Target C files don't need to exist on disk to register with SourceManager
  - CodeGenerator has access to SourceManager to decode locations
  - [Any others made during research]
</assumptions>
```

## SUMMARY.md Requirement

Create `.prompts/076-source-location-mapping-research/SUMMARY.md`:

**One-liner**: [Substantive description of the SourceLocation mapping solution discovered]

**Version**: v1

**Key Findings**:
- [Specific API calls needed to create SourceLocations]
- [Whether line number preservation is feasible/recommended]
- [How to integrate SourceLocationMapper with existing architecture]
- [Results from POC testing]

**Files Created**:
- `include/SourceLocationMapper.h`
- `src/SourceLocationMapper.cpp`
- `tests/SourceLocationMapperTest.cpp`
- [Any others]

**Decisions Needed**:
- [Specific architectural choices that require user input]
- [Trade-offs between approaches discovered]

**Blockers**:
- [Any technical blockers discovered]
- [Missing capabilities in Clang API]

**Next Step**:
- Create plan for refactoring all 17+ handlers to use SourceLocationMapper
- OR: Begin implementation in TargetContext if research conclusive

## Success Criteria

Research is complete when:

- ✅ All official documentation consulted and cited
- ✅ Clang source code examples found and analyzed
- ✅ All experiments successfully conducted
- ✅ SourceLocationMapper implemented and tested (if feasible)
- ✅ At least one handler refactored as POC
- ✅ CodeGenerator verified to use locations correctly
- ✅ Migration guide written for refactoring remaining handlers
- ✅ Metadata section complete with honest confidence level
- ✅ SUMMARY.md created with substantive one-liner
- ✅ Open questions and blockers clearly identified
- ✅ All code examples compile and tests pass

## Quality Controls

### Pre-Submission Verification

1. **Research Depth**:
   - [ ] Official docs read (not just skimmed)
   - [ ] At least 3 Clang source code examples examined
   - [ ] At least 2 external sources consulted (blogs, Stack Overflow, etc.)

2. **Experimentation**:
   - [ ] All 4 experiments conducted and documented
   - [ ] Code examples compile without errors
   - [ ] Test output captured and included

3. **POC Quality**:
   - [ ] SourceLocationMapper compiles and links
   - [ ] Unit tests written (minimum 4 tests)
   - [ ] All tests pass
   - [ ] Handler refactoring example compiles

4. **Documentation Quality**:
   - [ ] Migration guide is step-by-step and actionable
   - [ ] Code examples are complete (not pseudocode)
   - [ ] All sources cited with URLs
   - [ ] Distinction made between verified facts and assumptions

5. **Critical Thinking**:
   - [ ] Alternative approaches considered and compared
   - [ ] Limitations and edge cases documented
   - [ ] Performance implications discussed (if relevant)
   - [ ] Future extensibility considered

### Quality Report

At end of research output, include:

```markdown
## Research Quality Assurance

### Sources Consulted
1. [Source 1 with URL and what was learned]
2. [Source 2 with URL and what was learned]
[List all sources]

### Verification Status
- **Official Documentation**: [% read and understood]
- **Code Examples Found**: [number and quality]
- **Experiments Conducted**: [number passed/total]
- **POC Implementation**: [Complete | Partial | Not feasible because...]

### Confidence Assessment
**Overall Confidence**: [High | Medium | Low]

**High Confidence In**:
- [Specific findings you're certain about]

**Medium Confidence In**:
- [Findings that need more validation]

**Low Confidence In / Need More Research**:
- [Areas that remain unclear]

### Critical Assumptions Requiring Validation
1. [Assumption that needs testing in real transpiler]
2. [Another assumption]
```

## Additional Context

**Handler Files to Eventually Refactor** (for reference):

```
src/dispatch/VariableHandler.cpp
src/dispatch/FunctionHandler.cpp
src/dispatch/RecordHandler.cpp
src/dispatch/ConstructorHandler.cpp
src/dispatch/MethodHandler.cpp
src/dispatch/InstanceMethodHandler.cpp
src/dispatch/VirtualMethodHandler.cpp
src/dispatch/ExceptionHandler.cpp
src/dispatch/TypeInfoHandler.cpp
src/dispatch/DynamicCastHandler.cpp
[... approximately 17+ handlers total]
```

**Existing Infrastructure to Leverage**:

From @001-ast-location-refactor:
```cpp
// Already implemented - use this to get target path
auto [targetPath, C_TU] = getTargetForNode(cppNode);
```

From TargetContext:
```cpp
// C ASTContext already available
clang::ASTContext& getCContext();

// Access to SourceManager (likely)
getCContext().getSourceManager();
```

**Related Architecture**:
- PathMapper: Maps source file paths to target file paths
- FileOriginTracker: Tracks which declarations belong to which files
- TargetContext: Manages C AST context and translation units

---

**Remember**: This is a research prompt, not an implementation prompt. The goal is to understand how to do this correctly, experiment with the approach, and provide a validated migration path. The actual refactoring of all handlers will be a separate "Do" or "Plan" prompt.
