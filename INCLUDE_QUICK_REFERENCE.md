# Include Directive Generation - Quick Reference

## Where Includes Are Generated

**File**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCConsumer.cpp`
**Method**: `void CppToCConsumer::HandleTranslationUnit(clang::ASTContext &Context)`
**Lines**: 100-261

## Generation Flow

### 1. Standard C Headers (Lines 106-113)
```cpp
headerOS << "#include <stdio.h>\n";
headerOS << "#include <stdlib.h>\n";
headerOS << "#include <string.h>\n";
headerOS << "#include <math.h>\n";
headerOS << "#include <stdint.h>\n";
headerOS << "#include <stdbool.h>\n\n";
```

### 2. User Header Includes (Lines 115-261)
```cpp
// Get all user headers encountered during parsing
auto userHeaders = fileOriginTracker.getUserHeaderFiles();

// For each user header:
for (const auto& headerPath : userHeaders) {
    // Skip self-includes
    if (headerPath == InputFilename) continue;

    // Skip template-only headers (no separate file generated)
    if (!hasNonTemplateDecls) continue;

    // Calculate include path (with include/ → src/ mapping)
    std::string includePath = calculateIncludePath(headerPath);

    // Skip self-includes by basename
    if (includeBasename == currentOutputBasename) continue;

    // Emit the include
    headerOS << "#include \"" << includePath << "\"\n";
}
```

### 3. Implementation File Header Include (Lines 273-287)
```cpp
implOS << "#include \"" << baseName << ".h\"\n\n";
```

## Key Classes

| Class | Location | Purpose |
|-------|----------|---------|
| `FileOriginTracker` | `include/FileOriginTracker.h` | Tracks which declarations come from which files |
| `CppToCConsumer` | `include/CppToCConsumer.h` | Orchestrates include generation and code emission |
| `CodeGenerator` | `include/CodeGenerator.h` | Emits C code (doesn't handle includes) |
| `FileOutputManager` | `include/FileOutputManager.h` | Writes output .h and .c files |

## Include Path Transformation

### Directory Mapping
```
include/Vector3D.h → src/Vector3D.h
include/Matrix.h   → src/Matrix.h
```

**Why**: C++ headers in `include/` don't generate output; implementation files in `src/` do.

### Path Calculation
```
If SourceDir set:
  1. Make path relative to SourceDir
  2. Replace extension with .h
  3. Replace include/ with src/

If SourceDir not set:
  Use basename only
```

## Self-Include Prevention

### Method 1: File Comparison (Line 140)
```cpp
if (headerPath == InputFilename) continue;
```

### Method 2: Basename Comparison (Lines 237-255)
```cpp
std::string currentOutputBasename = extractBasename("main.cpp");  // "main"
std::string includeBasename = extractBasename("src/main.h");      // "main"

if (includeBasename == currentOutputBasename) continue;  // Skip
```

## Template-Only Header Skipping

**Lines 144-184**: Check if header contains non-template declarations

```cpp
bool hasNonTemplateDecls = false;

// Check each declaration in the header
for (const auto* D : headerDecls) {
    if (auto* CRD = dyn_cast<clang::CXXRecordDecl>(D)) {
        // Skip if it's a template, implicit, or nested in template
        if (!CRD->getDescribedClassTemplate() &&
            !CRD->isImplicit() &&
            !isNestedInTemplate) {
            hasNonTemplateDecls = true;
            break;
        }
    }
    // ... similar for functions, variables
}

if (!hasNonTemplateDecls) continue;  // Skip include
```

## Output Example

### Input: main.cpp
```cpp
#include <stdio.h>
#include "include/Vector3D.h"
#include "include/Matrix3x3.h"

int main() { ... }
```

### Generated: main.h
```c
#pragma once

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

#include "src/Vector3D.h"
#include "src/Matrix3x3.h"

int main();
```

### Generated: main.c
```c
#include "main.h"

int main() { ... }
```

## Include Path Options

### With SourceDir
```
SourceDir: /project
Header: /project/include/Vector3D.h
Output: src/Vector3D.h  (relative from SourceDir)
```

### Without SourceDir
```
Header: /project/include/Vector3D.h
Output: Vector3D.h  (basename only)
```

## How to Customize

### Add Custom Path Mapping

**Location**: `CppToCConsumer.cpp` line 205

```cpp
includePath = relPathStr;  // Current

// Add custom mapping:
if (includePath.find("vendor/") == 0) {
    includePath = "external/" + includePath;
}
```

### Change Include Format

**Location**: `CppToCConsumer.cpp` line 257

```cpp
// Current: quoted includes
headerOS << "#include \"" << includePath << "\"\n";

// Change to angle brackets for system headers:
if (isSystemHeader) {
    headerOS << "#include <" << includePath << ">\n";
} else {
    headerOS << "#include \"" << includePath << "\"\n";
}
```

### Use Traditional Include Guards

**Location**: `CppToCConsumer.cpp` line 104

```cpp
// Current:
headerOS << "#pragma once\n\n";

// Change to:
#include "IncludeGuardGenerator.h"
IncludeGuardGenerator guardGen(false);  // false = traditional guards
std::string guardName = guardGen.generateGuardName(baseName + ".h");
headerOS << guardGen.emitGuardBegin(guardName) << "\n\n";
// ... at end:
headerOS << guardGen.emitGuardEnd(guardName) << "\n";
```

## Testing

### See Generated Includes

Location: `tests/real-world/simple-validation/`

Test cases:
- `01-math-library/transpiled/main.h` - Multiple library includes
- `03-state-machine/transpiled/main.h` - Single library include
- `04-simple-parser/transpiled/main.h` - Multiple class includes
- `05-game-logic/transpiled/main.h` - Complex dependencies

## Pipeline Overview

```
C++ Source
    ↓
[Parse with Clang]
    ↓
C++ AST + FileOriginTracker
    ↓
[CppToCConsumer] ← HERE: Generates includes
    ├─→ Standard headers: <stdio.h>, etc.
    ├─→ User headers: src/Vector3D.h, etc.
    └─→ Header guard: #pragma once
    ↓
[CodeGenerator] ← Emits declarations/definitions
    ↓
Output Files (.h + .c)
```

## Current Behavior

| Feature | Status |
|---------|--------|
| **Standard Headers** | ✓ Always included |
| **User Headers** | ✓ Auto-detected and included |
| **Path Transform** | ✓ include/ → src/ mapping |
| **Self-Include Prevention** | ✓ Basename comparison |
| **Template Skipping** | ✓ Detects template-only headers |
| **Relative Paths** | ✓ Based on SourceDir |
| **Include Guard** | ✓ #pragma once (modern) |
| **Deduplication** | ✓ Via file tracking |

## Debugging Tips

### Print Include Decisions
```cpp
// Add debugging in CppToCConsumer.cpp line 257:
llvm::outs() << "[INCLUDE] Adding: " << includePath << "\n";
```

### Verify User Headers
```cpp
// Add debugging line 118:
auto userHeaders = fileOriginTracker.getUserHeaderFiles();
for (const auto& h : userHeaders) {
    llvm::outs() << "[DEBUG] User header: " << h << "\n";
}
```

### Trace Include Path Calculation
```cpp
// Add debugging in path calculation section (lines 186-235):
llvm::outs() << "[PATH] Header: " << headerPath << "\n";
llvm::outs() << "[PATH] Relative: " << relPath << "\n";
llvm::outs() << "[PATH] Final: " << includePath << "\n";
```
