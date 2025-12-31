# Include Directive Handling Analysis

## Overview

The transpiler has a comprehensive system for handling `#include` directives when generating C output files. The system distinguishes between standard C headers, user-defined headers, and system headers to generate correct includes in the transpiled C code.

---

## Pipeline Architecture

### Stage 1: Include Path Tracking (FileOriginTracker)
- **Location**: `include/FileOriginTracker.h`, `src/FileOriginTracker.cpp`
- **Responsibility**: Track which declarations come from which source files
- **Key Methods**:
  - `recordDeclaration(const clang::Decl *D)` - Records a declaration's origin file
  - `getUserHeaderFiles()` - Returns all user header files encountered
  - `shouldTranspile(const clang::Decl *D)` - Determines if a declaration should generate output
  - `getDeclarationsFromFile(const std::string& filepath)` - Gets declarations from a specific file

### Stage 2: Include Directive Generation (CppToCConsumer)
- **Location**: `src/CppToCConsumer.cpp`
- **Responsibility**: Generate #include directives in output .h files
- **Key Section**: Lines 100-261 in HandleTranslationUnit()

### Stage 3: File Output (FileOutputManager)
- **Location**: `include/FileOutputManager.h`, `src/FileOutputManager.cpp`
- **Responsibility**: Write .h and .c files with proper includes

---

## Current Include Generation Process

### Step 1: Standard C Headers (Lines 106-113)

The transpiler **always** includes these standard C headers:

```cpp
headerOS << "#include <stdio.h>\n";
headerOS << "#include <stdlib.h>\n";
headerOS << "#include <string.h>\n";
headerOS << "#include <math.h>\n";
headerOS << "#include <stdint.h>\n";
headerOS << "#include <stdbool.h>\n\n";
```

**Purpose**: These replace C++ standard library headers:
- `<cstdio>` → `<stdio.h>`
- `<cmath>` → `<math.h>`
- `<cstdint>` → `<stdint.h>`
- etc.

### Step 2: User Header Includes (Lines 115-261)

For each user header encountered during parsing:

1. **Retrieve all user headers** (Line 118):
   ```cpp
   auto userHeaders = fileOriginTracker.getUserHeaderFiles();
   ```

2. **Determine output basename** to detect self-includes (Lines 123-136):
   - Example: `main.cpp` → `main`
   - Used to prevent circular dependencies

3. **For each user header, decide whether to include it**:

   a. **Skip self-includes** (Lines 139-141):
      ```cpp
      if (headerPath == InputFilename) {
          continue;  // Skip if this is the current file
      }
      ```

   b. **Skip template-only headers** (Lines 144-184):
      - Headers containing only template definitions don't generate separate transpiled files
      - These are monomorphized inline instead
      - Example: `LinkedList.h` with only template classes

   c. **Calculate include path** (Lines 186-235):
      - **If `SourceDir` is set**: Use relative path from root
        ```cpp
        fs::path hdrPath = fs::weakly_canonical(headerPath);
        fs::path rootPath = fs::weakly_canonical(SourceDir);
        fs::path relPath = hdrPath.lexically_relative(rootPath);
        relPath.replace_extension(".h");  // .cpp/.h → .h
        ```

      - **Special mapping**: `include/` → `src/`
        ```cpp
        if (relPathStr.rfind("include/", 0) == 0) {
            relPathStr = "src/" + relPathStr.substr(8);
        }
        ```
        This is critical because C++ headers in `include/` don't generate files;
        the `.cpp` files in `src/` do.

      - **If no `SourceDir`**: Use basename only
        ```cpp
        std::string includePath = baseName + ".h";
        ```

   d. **Skip self-includes by basename** (Lines 237-255):
      - Compare basename of include path with current file's basename
      - Prevents including `Vector3D.h` from `Vector3D.cpp`

4. **Emit the #include directive** (Line 257):
   ```cpp
   headerOS << "#include \"" << includePath << "\"\n";
   ```

### Step 3: Implementation File Includes (Lines 269-287)

The `.c` implementation file includes its own header:

```cpp
size_t lastSlash = InputFilename.find_last_of("/\\");
std::string baseName;
if (lastSlash != std::string::npos) {
    baseName = InputFilename.substr(lastSlash + 1);
} else {
    baseName = InputFilename;
}
size_t dotPos = baseName.find_last_of('.');
if (dotPos != std::string::npos) {
    baseName = baseName.substr(0, dotPos);
}
implOS << "#include \"" << baseName << ".h\"\n\n";
```

---

## Example: Math Library Project

### Project Structure
```
01-math-library/
├── main.cpp
├── include/
│   ├── Vector3D.h
│   └── Matrix3x3.h
└── src/
    ├── Vector3D.cpp
    └── Matrix3x3.cpp
```

### Generated main.h
```c
// Generated from: main.cpp
#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

#include "src/Vector3D.h"
#include "src/Matrix3x3.h"

// Function declarations...
```

### Key Mapping
- **C++ headers**: `include/Vector3D.h`, `include/Matrix3x3.h`
- **Generated transpiled headers**: `src/Vector3D.h`, `src/Matrix3x3.h`
- **Include directive**: Maps `include/` → `src/` to reference transpiled headers

### Generated Vector3D.h
```c
// Generated from: src/Vector3D.cpp
#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

// Struct definition for Vector3D...
```

---

## Include Path Transformation Rules

### Rule 1: Extension Replacement
```
Vector3D.cpp → Vector3D.h (C transpiled header)
Vector3D.h → Vector3D.h (header already .h)
```

### Rule 2: Directory Mapping
```
include/Vector3D.h → src/Vector3D.h
```

**Rationale**: C++ build projects typically have:
- `include/` - Public headers (declarations only)
- `src/` - Implementation files

When transpiling:
- The `include/Vector3D.h` file doesn't generate output
- The `src/Vector3D.cpp` file generates both `src/Vector3D.h` and `src/Vector3D.c`
- So includes should reference `src/Vector3D.h`

### Rule 3: Relative vs Absolute Paths
```
If SourceDir set: Use relative path from root
If SourceDir empty: Use basename only
```

**Example with SourceDir**:
- SourceDir: `/path/to/project`
- Header: `/path/to/project/include/Vector3D.h`
- Include: `src/Vector3D.h` (relative from SourceDir after include/ → src/ mapping)

**Example without SourceDir**:
- Header: `/path/to/project/include/Vector3D.h`
- Include: `Vector3D.h` (basename only)

### Rule 4: Self-Include Prevention
```
main.cpp includes main.h? NO - skip to prevent circular dependency
Vector3D.cpp includes Vector3D.h? NO - the .c file already includes it
```

**How it works**:
1. Calculate current output file's basename: `main` (from `main.cpp`)
2. For each user header: Calculate its output basename
3. If basenames match, skip the include

---

## Deduplication Logic

### Template-Only Headers (Lines 144-184)

**Problem**: Headers like `LinkedList.h` contain only template classes/functions that don't generate separate files.

**Solution**: Check if header has non-template declarations:
```cpp
bool hasNonTemplateDecls = false;

for (const auto* D : headerDecls) {
    if (auto* CRD = dyn_cast<clang::CXXRecordDecl>(D)) {
        if (!CRD->getDescribedClassTemplate() &&
            !CRD->isImplicit() &&
            !isNestedInTemplate) {
            hasNonTemplateDecls = true;
            break;
        }
    }
    // ... similar checks for functions, variables
}

if (!hasNonTemplateDecls) {
    continue;  // Skip include - header has no files to include
}
```

**Result**: `#include "LinkedList.h"` is NOT emitted because LinkedList.h generates no separate output file.

### File Origin Filtering

The `FileOriginTracker` filters declarations by category:

```cpp
enum class FileCategory {
    MainFile,           // Always transpile
    UserHeader,         // Always transpile
    SystemHeader,       // Never transpile
    ThirdPartyHeader    // Configurable (default: skip)
};
```

**Application**: Only declarations from MainFile and UserHeader categories generate includes.

---

## How to Inject Proper Include Path Mapping

### Current Architecture Entry Points

1. **For custom include path transformations**:
   - Modify `CppToCConsumer::HandleTranslationUnit()` lines 186-235
   - Add custom logic in the include path calculation section

2. **For filtering decisions**:
   - Modify `FileOriginTracker::getUserHeaderFiles()` to filter headers
   - Modify template detection logic (lines 144-184)

3. **For include format**:
   - Modify line 257 to change `"` to `<>` for system headers
   - Add conditional logic: `#include <std_header.h>` vs `#include "user_header.h"`

### Example: Add Custom Include Mapping

To map includes through a specific directory:

```cpp
// In CppToCConsumer.cpp, around line 195:
std::string includePath = relPathStr;

// NEW: Custom mapping for includes
// Example: Map all includes to "transpiled/" subdirectory
includePath = "transpiled/" + includePath;

// Or map based on file type:
if (includePath.find("src/") == 0) {
    // Already in src/ - good
} else if (includePath.find("include/") == 0) {
    // Already mapped to src/ above
}
```

### Example: Add Include Guard Handling

The codebase has `IncludeGuardGenerator` available (see `include/IncludeGuardGenerator.h`):

```cpp
// Currently using:
headerOS << "#pragma once\n\n";

// Could use traditional guards instead:
IncludeGuardGenerator guardGen(false);  // false = traditional guards
std::string guardName = guardGen.generateGuardName("Vector3D.h");
headerOS << guardGen.emitGuardBegin(guardName) << "\n";
// ... content ...
headerOS << guardGen.emitGuardEnd(guardName) << "\n";
```

---

## Key Classes and Methods

### FileOriginTracker
- **Location**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/FileOriginTracker.h`
- **Purpose**: Track file origins and determine transpilation policy
- **Key Methods**:
  ```cpp
  void recordDeclaration(const clang::Decl *D);
  std::set<std::string> getUserHeaderFiles() const;
  std::vector<const clang::Decl*> getDeclarationsFromFile(const std::string& filepath);
  bool shouldTranspile(const clang::Decl *D) const;
  ```

### CppToCConsumer
- **Location**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCConsumer.cpp`
- **Purpose**: Generate C code and coordinate output
- **Key Section**: `HandleTranslationUnit()` method (lines 23-325)
- **Include Generation**: Lines 100-261

### CodeGenerator
- **Location**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/CodeGenerator.h`
- **Responsibility**: Emit C code (doesn't handle includes - that's CppToCConsumer's job)

### IncludeGuardGenerator
- **Location**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/IncludeGuardGenerator.h`
- **Purpose**: Generate header guards (currently unused - transpiler uses `#pragma once`)
- **Supports**: Traditional `#ifndef` guards and modern `#pragma once`

---

## Current Behavior Summary

| Aspect | Current Behavior |
|--------|------------------|
| **Standard Headers** | Always included: `<stdio.h>`, `<stdlib.h>`, `<string.h>`, `<math.h>`, `<stdint.h>`, `<stdbool.h>` |
| **User Headers** | Automatically detected and included (with path transformation) |
| **Include Format** | `#include "path/to/header.h"` (quoted, relative paths) |
| **Header Guard** | `#pragma once` (modern style) |
| **Path Transformation** | `include/` → `src/` directory mapping |
| **Relative Paths** | Based on SourceDir if set; basename only if not |
| **Self-Include Prevention** | Detected by basename comparison |
| **Template Headers** | Skipped (monomorphized inline instead) |
| **Deduplication** | Via file origin tracking and template detection |

---

## Testing Validation Cases

### Test Case 1: Single File Projects
- **File**: `tests/real-world/simple-validation/01-math-library/`
- **Expected**: main.h includes transpiled library headers (src/Vector3D.h, src/Matrix3x3.h)
- **Status**: PASSING

### Test Case 2: State Machine (Single File)
- **File**: `tests/real-world/simple-validation/03-state-machine/`
- **Expected**: main.h includes src/StateMachine.h
- **Status**: PASSING

### Test Case 3: Parser (Multiple Classes)
- **File**: `tests/real-world/simple-validation/04-simple-parser/`
- **Expected**: main.h includes src/Tokenizer.h, src/ExpressionEvaluator.h
- **Status**: PASSING

### Test Case 4: Game Logic (Multiple Files)
- **File**: `tests/real-world/simple-validation/05-game-logic/`
- **Expected**: Complex dependency graph with cross-file includes
- **Status**: PASSING

---

## Potential Issues and Improvements

### 1. Hardcoded Standard Headers
**Current**: Always includes 6 standard headers regardless of actual use
**Improvement**: Analyze actual C code generation to determine which headers are actually needed

### 2. No Include Deduplication Across Files
**Current**: Each .h file emits its own #include directives
**Improvement**: Could track already-included files to avoid redundant includes

### 3. No Conditional Compilation for Platform-Specific Headers
**Current**: Same headers for all platforms
**Improvement**: Could emit conditional includes based on target platform

### 4. Manual Path Mapping
**Current**: Hardcoded `include/` → `src/` mapping
**Improvement**: Could make this configurable via command-line arguments

### 5. No System Header Handling
**Current**: All includes are quoted (relative)
**Improvement**: Could distinguish between system includes (`<>`) and local includes (`""`)

---

## Architecture Diagram

```
C++ Source Files
       ↓
[Clang Frontend Parser]
       ↓
C++ AST
       ↓
[FileOriginTracker]  ← Tracks which declarations come from which files
       ↓
[CppToCVisitor]      ← Traverses C++ AST, visits declarations
       ↓
C AST (C_TranslationUnit)
       ↓
[CppToCConsumer]
       ├─→ Generates #include directives (user headers)
       ├─→ Generates standard C headers
       └─→ Passes content to CodeGenerator
       ↓
[CodeGenerator]      ← Emits C code (doesn't handle includes)
       ↓
String Content (headerContent, implContent)
       ↓
[FileOutputManager]
       └─→ Writes .h and .c files
```

---

## Summary

The transpiler has a sophisticated include generation system that:

1. **Automatically tracks** which declarations come from which files
2. **Generates correct relative paths** based on project structure
3. **Handles special cases** like `include/` → `src/` directory mapping
4. **Prevents self-includes** to avoid circular dependencies
5. **Skips template-only headers** that don't generate separate files
6. **Deduplicates includes** via file origin tracking

The main entry point for customization is `CppToCConsumer::HandleTranslationUnit()` lines 100-261, where include directives are generated before code emission.
