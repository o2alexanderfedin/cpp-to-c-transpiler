# Include Directive Handling - Code Snippets & Examples

## Code Snippet 1: Standard C Headers Generation

**File**: `src/CppToCConsumer.cpp` (Lines 106-113)

```cpp
// Phase 40 (Bug Fix): Add standard C headers
headerOS << "#include <stdio.h>\n";
headerOS << "#include <stdlib.h>\n";
headerOS << "#include <string.h>\n";
headerOS << "#include <math.h>\n";
headerOS << "#include <stdint.h>\n";
headerOS << "#include <stdbool.h>\n\n";
```

**Purpose**: Replace C++ standard library headers with C equivalents

**Mapping**:
| C++ Header | C Header | Used For |
|------------|----------|----------|
| `<cstdio>` | `<stdio.h>` | Input/output operations |
| `<cstdlib>` | `<stdlib.h>` | Memory allocation, exit |
| `<cstring>` | `<string.h>` | String operations |
| `<cmath>` | `<math.h>` | Math functions |
| `<cstdint>` | `<stdint.h>` | Fixed-width integer types |
| `<ccstdbool>` | `<stdbool.h>` | Boolean type support |

---

## Code Snippet 2: User Header Collection

**File**: `src/CppToCConsumer.cpp` (Lines 118-122)

```cpp
// Phase 40 (Bug Fix): Emit #include directives for user headers
auto userHeaders = fileOriginTracker.getUserHeaderFiles();
llvm::outs() << "[DEBUG] getUserHeaderFiles() returned " << userHeaders.size() << " headers\n";
for (const auto& h : userHeaders) {
    llvm::outs() << "[DEBUG]   - " << h << "\n";
}
```

**What it does**:
1. Gets all user-defined header files encountered during parsing
2. Prints debug info showing which headers will be included

**FileOriginTracker::getUserHeaderFiles()** returns:
- All files from main source
- All files from included user headers
- Excludes system headers (`/usr/include`, `/Library`, `/System`)

**Example Output**:
```
[DEBUG] getUserHeaderFiles() returned 3 headers
[DEBUG]   - /Users/alex/project/include/Vector3D.h
[DEBUG]   - /Users/alex/project/include/Matrix3x3.h
[DEBUG]   - /Users/alex/project/main.cpp
```

---

## Code Snippet 3: Self-Include Prevention

**File**: `src/CppToCConsumer.cpp` (Lines 123-136)

Calculate current file's output basename to detect self-includes:

```cpp
// Calculate output basename for current file (to detect self-includes)
std::string currentOutputBasename;
{
    size_t lastSlash = InputFilename.find_last_of("/\\");
    size_t lastDot = InputFilename.find_last_of('.');
    if (lastSlash != std::string::npos) {
        currentOutputBasename = InputFilename.substr(lastSlash + 1);
    } else {
        currentOutputBasename = InputFilename;
    }
    if (lastDot != std::string::npos && lastDot > lastSlash) {
        currentOutputBasename = currentOutputBasename.substr(0,
            lastDot - (lastSlash != std::string::npos ? lastSlash + 1 : 0));
    }
}
```

**Logic**:
1. Find last path separator (`/` or `\`)
2. Find last dot (`.`)
3. Extract basename between separator and dot
4. Remove extension

**Examples**:
```
Input: /project/src/Vector3D.cpp
  → lastSlash: 17
  → lastDot: 26
  → substr(18): Vector3D.cpp
  → Remove ext: Vector3D

Input: main.cpp
  → lastSlash: npos
  → lastDot: 4
  → substr(0, 4): main

Input: /path/to/my-class.cpp
  → lastSlash: 9
  → lastDot: 21
  → substr(10): my-class.cpp
  → Remove ext: my-class
```

---

## Code Snippet 4: Template-Only Header Detection

**File**: `src/CppToCConsumer.cpp` (Lines 147-179)

```cpp
bool hasNonTemplateDecls = false;
auto headerDecls = fileOriginTracker.getDeclarationsFromFile(headerPath);

for (const auto* D : headerDecls) {
    // Check if this is a non-template class declaration
    if (auto* CRD = dyn_cast<clang::CXXRecordDecl>(D)) {
        bool isNestedInTemplate = false;
        // Check if this class is nested within a template class
        if (auto* Parent = dyn_cast_or_null<clang::CXXRecordDecl>(CRD->getParent())) {
            if (Parent->getDescribedClassTemplate()) {
                isNestedInTemplate = true;
            }
        }
        // Skip template declarations, implicit declarations, and nested classes in templates
        if (!CRD->getDescribedClassTemplate() && !CRD->isImplicit() && !isNestedInTemplate) {
            hasNonTemplateDecls = true;
            break;
        }
    } else if (auto* FD = dyn_cast<clang::FunctionDecl>(D)) {
        // Skip template functions and implicit functions
        if (!FD->getDescribedFunctionTemplate() && !FD->isImplicit() &&
            !isa<clang::CXXMethodDecl>(FD)) {
            hasNonTemplateDecls = true;
            break;
        }
    } else if (auto* VD = dyn_cast<clang::VarDecl>(D)) {
        // Non-template variables need separate file
        if (!VD->isImplicit()) {
            hasNonTemplateDecls = true;
            break;
        }
    }
}

if (!hasNonTemplateDecls) {
    continue;  // Skip include - header has no files to include
}
```

**Decision Logic**:

For **Class/Struct** declarations:
- Skip if: `ClassTemplate::ListNode<T>`
- Skip if: nested in template class
- Skip if: compiler-generated (implicit)
- **Include if**: regular concrete class

For **Function** declarations:
- Skip if: `template<typename T> void func()`
- Skip if: member function (belongs to class)
- Skip if: compiler-generated
- **Include if**: regular function

For **Variable** declarations:
- Skip if: compiler-generated
- **Include if**: global variable

**Real-World Example**:

Template-only header that generates NO include:
```cpp
// LinkedList.h - NO #include generated
template<typename T>
class LinkedList {
    template<typename U>
    struct Node {
        U data;
        Node<U>* next;
    };
    // ...
};
```

Regular header that DOES generate include:
```cpp
// Vector3D.h - #include "src/Vector3D.h" IS generated
class Vector3D {
    float x, y, z;
public:
    Vector3D();
    float magnitude() const;
};
```

---

## Code Snippet 5: Include Path Calculation

**File**: `src/CppToCConsumer.cpp` (Lines 186-220)

```cpp
std::string includePath;
if (!SourceDir.empty()) {
    try {
        fs::path hdrPath = fs::weakly_canonical(headerPath);
        fs::path rootPath = fs::weakly_canonical(SourceDir);
        fs::path relPath = hdrPath.lexically_relative(rootPath);

        // Replace extension with .h (transpiled C header)
        relPath.replace_extension(".h");
        std::string relPathStr = relPath.string();

        // Phase 40 (Bug Fix): Map include/ headers to src/ transpiled headers
        // C++ headers in include/ don't generate files - the .cpp files in src/ do
        // So include/Vector3D.h → src/Vector3D.h (from src/Vector3D.cpp)
        if (relPathStr.rfind("include/", 0) == 0) {
            relPathStr = "src/" + relPathStr.substr(8);  // 8 = length of "include/"
        }
        includePath = relPathStr;
    } catch (const fs::filesystem_error& e) {
        // Fallback: use basename only
        size_t lastSlash = headerPath.find_last_of("/\\");
        size_t lastDot = headerPath.find_last_of('.');
        std::string baseName;
        if (lastSlash != std::string::npos) {
            baseName = headerPath.substr(lastSlash + 1);
        } else {
            baseName = headerPath;
        }
        if (lastDot != std::string::npos) {
            baseName = baseName.substr(0, lastDot);
        }
        includePath = baseName + ".h";
    }
} else {
    // No sourceDir set - use basename only
    // [similar basename extraction code]
}
```

**Processing Steps**:

1. **Canonicalize paths** (normalize .. and .):
   ```
   /project/./include/../include/Vector3D.h
   → /project/include/Vector3D.h
   ```

2. **Make relative to SourceDir**:
   ```
   SourceDir: /project
   Path: /project/include/Vector3D.h
   Relative: include/Vector3D.h
   ```

3. **Replace extension**:
   ```
   include/Vector3D.h  (already .h, no change)
   include/Point.cpp   → include/Point.h
   ```

4. **Map include/ → src/** (Critical!):
   ```
   include/Vector3D.h → src/Vector3D.h
   include/Matrix.h   → src/Matrix.h
   ```

**Why the mapping matters**:
```
C++ Project Structure:
  include/Vector3D.h      ← Header only (declarations)
  src/Vector3D.cpp        ← Implementation

Transpilation:
  Vector3D.h does NOT generate output (it's just declarations)
  Vector3D.cpp GENERATES:
    - src/Vector3D.h (declarations)
    - src/Vector3D.c (implementation)

So when main.cpp includes "include/Vector3D.h",
the transpiler must map this to "src/Vector3D.h"
```

---

## Code Snippet 6: Self-Include Prevention by Basename

**File**: `src/CppToCConsumer.cpp` (Lines 237-255)

```cpp
// Phase 40 (Bug Fix): Skip self-includes to prevent circular dependencies
// Extract basename from includePath to compare with currentOutputBasename
std::string includeBasename;
{
    size_t lastSlash = includePath.find_last_of("/\\");
    size_t lastDot = includePath.find_last_of('.');
    if (lastSlash != std::string::npos) {
        includeBasename = includePath.substr(lastSlash + 1);
    } else {
        includeBasename = includePath;
    }
    if (lastDot != std::string::npos && lastDot > lastSlash) {
        includeBasename = includeBasename.substr(0,
            lastDot - (lastSlash != std::string::npos ? lastSlash + 1 : 0));
    }
}

if (includeBasename == currentOutputBasename) {
    llvm::outs() << "[DEBUG] Skipping self-include: " << includePath
                 << " (matches current file: " << currentOutputBasename << ")\n";
    continue;  // Skip self-includes
}
```

**Examples of Self-Include Prevention**:

```
Case 1: main.cpp
  currentOutputBasename = "main"
  includePath = "src/main.h"
  includeBasename = "main"
  Match? YES → Skip

Case 2: Vector3D.cpp
  currentOutputBasename = "Vector3D"
  includePath = "src/Vector3D.h"
  includeBasename = "Vector3D"
  Match? YES → Skip

Case 3: Vector3D.cpp includes Matrix.h
  currentOutputBasename = "Vector3D"
  includePath = "src/Matrix.h"
  includeBasename = "Matrix"
  Match? NO → Include
```

---

## Code Snippet 7: Include Directive Emission

**File**: `src/CppToCConsumer.cpp` (Line 257)

```cpp
headerOS << "#include \"" << includePath << "\"\n";
```

**Format**:
- **Quoted includes**: `#include "path/to/header.h"`
- Used for: User headers, project-local files
- Alternative: `#include <system_header.h>` (not currently used)

**Output Examples**:
```c
#include "src/Vector3D.h"
#include "src/Matrix3x3.h"
#include "src/StateMachine.h"
#include "include/LinkedList.h"  // Only if not template-only
```

---

## Code Snippet 8: Implementation File Include

**File**: `src/CppToCConsumer.cpp` (Lines 273-287)

```cpp
// Generate implementation file (.c) - full definitions
implOS << "// Generated from: " << InputFilename << "\n";
implOS << "// Implementation file\n\n";

// Include the corresponding header
// Extract base name for #include (strip path and extension)
size_t lastSlash = InputFilename.find_last_of("/\\");
std::string baseName;
if (lastSlash != std::string::npos) {
    baseName = InputFilename.substr(lastSlash + 1);
} else {
    baseName = InputFilename;
}

// Strip extension from base name (e.g., "main.cpp" → "main")
size_t dotPos = baseName.find_last_of('.');
if (dotPos != std::string::npos) {
    baseName = baseName.substr(0, dotPos);
}

implOS << "#include \"" << baseName << ".h\"\n\n";
```

**Pattern**: Each .c file includes its corresponding .h file

**Examples**:
```
Vector3D.cpp → #include "Vector3D.h"
main.cpp → #include "main.h"
Parser.cpp → #include "Parser.h"
```

---

## Code Snippet 9: Header Guard (Using #pragma once)

**File**: `src/CppToCConsumer.cpp` (Line 104)

```cpp
// Phase 40 (Bug Fix): Add header guard to prevent multiple inclusion
headerOS << "#pragma once\n\n";
```

**Alternative: Traditional Guards**

Using the `IncludeGuardGenerator` class:

```cpp
#include "IncludeGuardGenerator.h"

// Option 1: #pragma once (current)
headerOS << "#pragma once\n\n";

// Option 2: Traditional guards (alternative)
IncludeGuardGenerator guardGen(false);  // false = use traditional guards
std::string guardName = guardGen.generateGuardName(baseName + ".h");
headerOS << guardGen.emitGuardBegin(guardName) << "\n";
// ... header content ...
headerOS << guardGen.emitGuardEnd(guardName) << "\n";

// Option 3: Conditional (always #pragma once in 2024)
#ifdef USE_PRAGMA_ONCE
    headerOS << "#pragma once\n\n";
#else
    // Use traditional guards...
#endif
```

**Guard Name Generation**:
```
Vector3D.h → VECTOR3D_H
my-class.h → MY_CLASS_H
Parser.h → PARSER_H
```

---

## Flowchart: Include Decision Making

```
┌─────────────────────────────────────────────────┐
│ For each user header from FileOriginTracker     │
└────────────────┬────────────────────────────────┘
                 │
                 ▼
        ┌────────────────────┐
        │ Same as InputFile? │
        │ (line 140)         │
        └────┬───────────┬───┘
             │ YES       │ NO
             │           │
         Skip ◄──────────┘
             │           │
             │           ▼
             │    ┌──────────────────┐
             │    │ Has non-template │
             │    │ declarations?    │
             │    │ (lines 144-179)  │
             │    └────┬─────────┬───┘
             │         │ NO      │ YES
             │         │         │
             │     Skip ◄────────┘
             │         │         │
             │         │         ▼
             │         │    ┌────────────────┐
             │         │    │ Calculate      │
             │         │    │ include path   │
             │         │    │ (lines 186-235)│
             │         │    └────┬───────────┘
             │         │         │
             │         │         ▼
             │         │    ┌────────────────┐
             │         │    │ Basename match │
             │         │    │ current file?  │
             │         │    │ (lines 237-255)│
             │         │    └────┬─────┬──────┘
             │         │         │ YES │ NO
             │         │         │     │
             │         │     Skip ◄────┘
             │         │         │     │
             │         │         │     ▼
             │         │         │  ┌──────────────┐
             │         │         │  │ Emit include │
             │         │         │  │ line 257     │
             │         │         │  └──────────────┘
             │         │         │
             └─────────┴─────────┘
```

---

## Example: Full Include Generation for main.cpp

**Input File**: `/project/main.cpp`
```cpp
#include <iostream>
#include "include/Vector3D.h"
#include "include/Matrix3x3.h"

int main() { ... }
```

**Configuration**:
```
InputFilename: main.cpp
SourceDir: /project
UserHeaders from tracker: {
    /project/main.cpp,
    /project/include/Vector3D.h,
    /project/include/Matrix3x3.h
}
```

**Generation Process**:

1. **Emit standard headers** (lines 106-113):
   ```c
   #include <stdio.h>
   #include <stdlib.h>
   #include <string.h>
   #include <math.h>
   #include <stdint.h>
   #include <stdbool.h>
   ```

2. **Calculate currentOutputBasename** (lines 123-136):
   ```
   InputFilename = "main.cpp"
   currentOutputBasename = "main"
   ```

3. **Process /project/main.cpp** (line 140):
   ```
   headerPath == InputFilename? YES
   Skip (self-include prevention)
   ```

4. **Process /project/include/Vector3D.h** (lines 144-255):
   ```
   hasNonTemplateDecls? YES (Vector3D class is not a template)
   includePath calculation:
     hdrPath: /project/include/Vector3D.h
     rootPath: /project
     relPath: include/Vector3D.h
     replace extension: include/Vector3D.h (already .h)
     map include/ → src/: src/Vector3D.h
     includePath: "src/Vector3D.h"

   basename match? "Vector3D" == "main"? NO
   Emit: #include "src/Vector3D.h"
   ```

5. **Process /project/include/Matrix3x3.h** (similar to above):
   ```
   Emit: #include "src/Matrix3x3.h"
   ```

**Final Generated main.h**:
```c
// Generated from: /project/main.cpp
// Header file

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

---

## Debugging: Print All Decisions

**Add to CppToCConsumer.cpp for comprehensive debugging**:

```cpp
// After line 118 - print all user headers
auto userHeaders = fileOriginTracker.getUserHeaderFiles();
llvm::outs() << "[INCLUDES] Processing " << userHeaders.size() << " user headers\n";

for (const auto& headerPath : userHeaders) {
    llvm::outs() << "\n[INCLUDES] Processing: " << headerPath << "\n";

    // Check 1
    if (headerPath == InputFilename) {
        llvm::outs() << "  → SKIP: Self-file (same as InputFilename)\n";
        continue;
    }
    llvm::outs() << "  → PASS: Not self-file\n";

    // Check 2
    bool hasNonTemplateDecls = /* ... calculation ... */;
    if (!hasNonTemplateDecls) {
        llvm::outs() << "  → SKIP: Template-only header (no separate file)\n";
        continue;
    }
    llvm::outs() << "  → PASS: Has non-template declarations\n";

    // Check 3
    std::string includePath = /* ... calculation ... */;
    llvm::outs() << "  → Include path calculated: " << includePath << "\n";

    // Check 4
    std::string includeBasename = /* ... extraction ... */;
    if (includeBasename == currentOutputBasename) {
        llvm::outs() << "  → SKIP: Basename match (\"" << includeBasename
                     << "\" == \"" << currentOutputBasename << "\")\n";
        continue;
    }
    llvm::outs() << "  → PASS: Basename doesn't match\n";

    llvm::outs() << "  ✓ EMIT: #include \"" << includePath << "\"\n";
    headerOS << "#include \"" << includePath << "\"\n";
}
```

**Expected output for main.cpp**:
```
[INCLUDES] Processing 3 user headers

[INCLUDES] Processing: /project/main.cpp
  → SKIP: Self-file (same as InputFilename)

[INCLUDES] Processing: /project/include/Vector3D.h
  → PASS: Not self-file
  → PASS: Has non-template declarations
  → Include path calculated: src/Vector3D.h
  → PASS: Basename doesn't match
  ✓ EMIT: #include "src/Vector3D.h"

[INCLUDES] Processing: /project/include/Matrix3x3.h
  → PASS: Not self-file
  → PASS: Has non-template declarations
  → Include path calculated: src/Matrix3x3.h
  → PASS: Basename doesn't match
  ✓ EMIT: #include "src/Matrix3x3.h"
```
