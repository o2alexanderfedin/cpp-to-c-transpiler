# Manual Name Mangling Audit Report

## Overview

This report identifies all locations in the codebase where manual name mangling patterns are used instead of the new range-v3 based `NameMangler` API.

The `NameMangler` API provides these functions:
- `mangle_method()` - Mangles C++ methods to C function names
- `mangle_constructor()` - Mangles C++ constructors to C init function names
- `mangle_destructor()` - Mangles C++ destructors to C cleanup function names
- `mangle_function()` - Mangles free-standing functions
- `mangle_class()` - Mangles class names
- `mangle_static_member()` - Mangles static member variables
- `mangle_decl()` - Generic declaration mangler

All are defined in: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/include/NameMangler.h`

---

## File-by-File Analysis

### 1. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/ConstructorHandler.cpp`

**Location: Line 137**
```cpp
std::string baseName = className + "_init";
```

**Location: Line 144-154**
```cpp
std::string mangledName = baseName;
for (const auto* param : ctor->parameters()) {
    clang::QualType paramType = param->getType();
    std::string typeName = getSimpleTypeName(paramType);
    mangledName += "_" + typeName;
}
```

**Function:** `generateConstructorName()`

**Current Approach:** Manual string concatenation with `className + "_init"` + parameter types

**Should Use:** `mangle_constructor()` from `NameMangler.h`

**Mangling Pattern:**
- Constructor name: `ClassName + "_init"` (WRONG - should be `ClassName + "__ctor"`)
- Parameters: `_paramType1_paramType2` (uses single `_` separator for params)

**Issues:**
- Uses single `_` separator instead of `__` for components
- Parameter encoding is manual and inconsistent
- Not using the standardized `NameMangler` API

**Replacement Example:**
```cpp
// OLD:
std::string funcName = generateConstructorName(className, ctor);

// NEW:
std::string funcName = cpptoc::mangle_constructor(ctor);
```

---

### 2. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/DestructorHandler.cpp`

**Location: Line 28**
```cpp
std::string functionName = className + "_destroy";
```

**Function:** `handleDecl()`

**Current Approach:** Manual string concatenation with `className + "_destroy"`

**Should Use:** `mangle_destructor()` from `NameMangler.h`

**Mangling Pattern:** `ClassName + "_destroy"` (WRONG - should be `ClassName + "__dtor"`)

**Issues:**
- Hardcoded separator `_` instead of standardized `__`
- Inconsistent with C++ mangling conventions
- Not using the standardized `NameMangler` API

**Replacement Example:**
```cpp
// OLD:
std::string functionName = className + "_destroy";

// NEW:
std::string functionName = cpptoc::mangle_destructor(cppDestructor);
```

---

### 3. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/MethodHandler.cpp`

**Location: Line 137**
```cpp
return className + "_" + methodName;
```

**Function:** `mangleMethodName()`

**Current Approach:** Manual string concatenation with `className + "_" + methodName`

**Should Use:** `mangle_method()` from `NameMangler.h`

**Mangling Pattern:** `ClassName + "_" + methodName` (WRONG - should be `ClassName + "__" + methodName`)

**Issues:**
- Uses single `_` separator instead of `__`
- Does NOT handle parameter types (important for overloading)
- Does NOT handle operator overloading
- Does NOT handle namespaces in class names
- Not using the standardized `NameMangler` API

**Replacement Example:**
```cpp
// OLD:
std::string mangledName = mangleMethodName(className, methodName);

// NEW:
std::string mangledName = cpptoc::mangle_method(cppMethod);
```

---

### 4. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/handlers/StatementHandler.cpp`

**Location: Line 867**
```cpp
std::string ctorName = className + "_init";
```

**Function:** `generateDefaultConstructorCall()`

**Current Approach:** Manual string concatenation with `className + "_init"`

**Should Use:** `mangle_constructor()` from `NameMangler.h`

**Mangling Pattern:** `ClassName + "_init"`

**Issues:**
- Manual hardcoding of constructor name pattern
- Not using the standardized `NameMangler` API
- No parameter support (but for default constructor, this is acceptable)

**Replacement Example:**
```cpp
// OLD:
std::string ctorName = className + "_init";

// NEW:
// Need to get the constructor declaration first, then:
std::string ctorName = cpptoc::mangle_constructor(constructorDecl);
```

---

### 5. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/ACSLGhostCodeInjector.cpp`

**Location: Line 85**
```cpp
std::string ghostName = ensureUniqueName("ghost_" + paramName + "_init");
```

**Function:** `analyzeGhostOpportunities()`

**Current Approach:** Manual string concatenation with `"ghost_" + paramName + "_init"`

**Should Use:** N/A (This is for ghost code, not real C translation)

**Notes:** This is ACSL ghost code generation, not standard C translation. Mangling rules may differ. Consider if standardization is needed, but likely acceptable as-is.

---

### 6. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/VirtualMethodHandler.cpp`

**Location: Line 383**
```cpp
return className + "__vtable";
```

**Location: Line 398**
```cpp
return className + "__vtable_instance";
```

**Location: Line 442**
```cpp
std::string vtableStructName = className + "__vtable";
```

**Location: Line 494**
```cpp
std::string vtableInstanceName = className + "__vtable_instance";
```

**Functions:** `getVtableStructName()`, `getVtableInstanceName()`, `generateVtableStruct()`, `generateVtableInstance()`

**Current Approach:** Manual string concatenation with `className + "__vtable"` and `className + "__vtable_instance"`

**Should Use:** NOT `mangle_class()` directly - these are special vtable naming conventions

**Notes:**
- Already using `__` separator (correct)
- These are vtable-specific naming conventions, not directly mangled C++ names
- BUT: The `className` part IS produced by mangling, and should use `mangle_class()`
- Also note: Line 506 correctly uses `cpptoc::mangle_method(method)` for vtable entries

**Issues:**
- Manual concatenation of namespace-qualified class names
- Lines 379, 394, 438, 489 manually build `className` with namespace prefix using `+ "__"` pattern
- Should use `mangle_class()` for the base class name

**Current Pattern:**
```cpp
std::string className = classDecl->getNameAsString();
if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(classDecl->getDeclContext())) {
    std::string nsPath = NamespaceHandler::getNamespacePath(ns);
    if (!nsPath.empty()) {
        className = nsPath + "__" + className;  // MANUAL MANGLING
    }
}
return className + "__vtable";
```

**Should Use:**
```cpp
std::string mangledClass = cpptoc::mangle_class(classDecl);  // Already includes namespace
return mangledClass + "__vtable";
```

---

### 7. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/InstanceMethodHandler.cpp`

**Location: Line 219**
```cpp
className = nsPath + "__" + className;
```

**Function:** `createThisParameter()`

**Current Approach:** Manual namespace+class name mangling with `nsPath + "__" + className`

**Should Use:** `mangle_class()` from `NameMangler.h`

**Issues:**
- Manual namespace prefix concatenation
- Not using standardized NameMangler API
- Duplicates logic already in `NameMangler`

**Replacement Example:**
```cpp
// OLD:
std::string className = classDecl->getNameAsString();
if (const auto* ns = llvm::dyn_cast<clang::NamespaceDecl>(classDecl->getDeclContext())) {
    std::string nsPath = NamespaceHandler::getNamespacePath(ns);
    if (!nsPath.empty()) {
        className = nsPath + "__" + className;
    }
}

// NEW:
std::string className = cpptoc::mangle_class(classDecl);
```

---

### 8. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/ConstructorHandler.cpp` (old location, in dispatch/)

**Location: Line 414-417**
```cpp
if (bases.size() == 1 && baseInfo.IsPrimary) {
    vtableInstanceName = className + "_vtable_instance";
} else {
    vtableInstanceName = className + "_" + baseName + "_vtable_instance";
}
```

**Location: Line 436-439**
```cpp
if (bases.size() == 1 && baseInfo.IsPrimary) {
    vtableStructName = className + "_vtable";
} else {
    vtableStructName = className + "_" + baseName + "_vtable";
}
```

**Issues:**
- Uses single `_` separator instead of `__` for base class names
- INCONSISTENT with VirtualMethodHandler which uses `__`
- Should use `mangle_class()` for both `className` and `baseName`

**Replacement Pattern:**
```cpp
// OLD:
vtableInstanceName = className + "_" + baseName + "_vtable_instance";

// NEW:
std::string mangledClass = cpptoc::mangle_class(classDecl);
std::string mangledBase = cpptoc::mangle_class(baseClass);
vtableInstanceName = mangledClass + "__" + mangledBase + "__vtable_instance";
```

---

### 9. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/ConstructorHandler.cpp` (Lines 567, 581)`

**Location: Line 567**
```cpp
std::string vtableInstanceName = className + "_vtable_instance";
```

**Location: Line 581**
```cpp
std::string vtableStructName = className + "_vtable";
```

**Function:** `injectLpVtblInit()`

**Current Approach:** Manual string concatenation with `className + "_vtable_instance"`

**Issues:**
- Uses single `_` separator instead of `__`
- INCONSISTENT with VirtualMethodHandler usage
- Appears to be duplicate logic from earlier in same function

---

### 10. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/ConstructorHandler.cpp` (Line 722)`

**Location: Line 722**
```cpp
std::string baseCtorName = baseName + "_init";
```

**Function:** `createBaseConstructorCall()`

**Current Approach:** Manual string concatenation with `baseName + "_init"`

**Should Use:** Need to access the original C++ `CXXConstructorDecl` to use `mangle_constructor()`

**Issues:**
- Manual constructor name pattern
- No parameter support for parameterized constructors
- Works for default constructor, but fragile

---

## Summary Table

| File | Line(s) | Pattern | Should Use | Severity |
|------|---------|---------|-----------|----------|
| ConstructorHandler.cpp | 137, 144-154 | `className + "_init"` + params | `mangle_constructor()` | HIGH |
| DestructorHandler.cpp | 28 | `className + "_destroy"` | `mangle_destructor()` | HIGH |
| MethodHandler.cpp | 137 | `className + "_" + methodName` | `mangle_method()` | HIGH |
| StatementHandler.cpp | 867 | `className + "_init"` | `mangle_constructor()` | MEDIUM |
| VirtualMethodHandler.cpp | 379, 394, 438, 489 | Manual namespace+class concat | `mangle_class()` | HIGH |
| InstanceMethodHandler.cpp | 219 | `nsPath + "__" + className` | `mangle_class()` | HIGH |
| ConstructorHandler.cpp | 414-417, 436-439 | `className + "_" + baseName + "_vtable"` | `mangle_class()` x2 | HIGH |
| ConstructorHandler.cpp | 567, 581 | `className + "_vtable_instance"` | Fix separator to `__` | MEDIUM |
| ConstructorHandler.cpp | 722 | `baseName + "_init"` | `mangle_constructor()` | MEDIUM |
| ACSLGhostCodeInjector.cpp | 85 | Ghost code pattern | Review separately | LOW |

---

## Separator Consistency Issues

**Critical Finding:** There's INCONSISTENT use of separators:
- Some code uses single `_` separator (ConstructorHandler vtable names)
- Other code uses double `__` separator (VirtualMethodHandler, InstanceMethodHandler)

**The NameMangler API standardizes to `__` (double underscore)**

---

## Recommendations

### Priority 1 (High): Core Function Mangling
1. Replace `generateConstructorName()` with `mangle_constructor()` in ConstructorHandler.cpp
2. Replace manual destructor naming with `mangle_destructor()` in DestructorHandler.cpp
3. Replace `mangleMethodName()` with `mangle_method()` in MethodHandler.cpp
4. Replace `generateDefaultConstructorCall()` logic with `mangle_constructor()` in StatementHandler.cpp

### Priority 2 (High): Class Name Mangling
1. Replace all `className = nsPath + "__" + className` patterns with `mangle_class()`
2. Ensure consistent use of `__` separator throughout (not `_`)

### Priority 3 (Medium): Vtable Naming
1. Standardize vtable naming to use `mangle_class()` for class name parts
2. Keep vtable-specific suffixes (`__vtable`, `__vtable_instance`) but ensure proper spacing

### Priority 4 (Low): Ghost Code
1. Review ACSLGhostCodeInjector.cpp pattern separately
2. Determine if ghost code should follow standard mangling rules

---

## Implementation Strategy

1. **Add #include:** Add `#include "NameMangler.h"` to all affected source files
2. **Systematic Replacement:** Replace manual patterns one handler at a time
3. **Testing:** Ensure no behavior change in name output during transition
4. **Cleanup:** Remove helper functions like `generateConstructorName()`, `mangleMethodName()` once replaced

---

## Files Requiring Updates

```
src/dispatch/ConstructorHandler.cpp       - Priority 1, 3
src/dispatch/DestructorHandler.cpp        - Priority 1
src/dispatch/MethodHandler.cpp            - Priority 1
src/dispatch/VirtualMethodHandler.cpp     - Priority 2, 3
src/dispatch/InstanceMethodHandler.cpp    - Priority 2
src/handlers/StatementHandler.cpp         - Priority 1
src/ACSLGhostCodeInjector.cpp            - Priority 4
```

---

## Related Header Files

These headers need to verify they use NameMangler API:
```
include/dispatch/ConstructorHandler.h
include/dispatch/DestructorHandler.h
include/dispatch/MethodHandler.h
include/dispatch/VirtualMethodHandler.h
include/dispatch/InstanceMethodHandler.h
include/handlers/DestructorHandler.h
```

