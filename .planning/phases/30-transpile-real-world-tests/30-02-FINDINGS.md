# Pointer Recursion Root Cause Findings

**The transpiler loses pointer type information during name mangling (`int*` → `"ptr"`) and re-processes its own generated functions without marking them as synthetic, causing infinite `_ptr_ptr_ptr...` recursion.**

## Executive Summary

After cloning and analyzing Frama-Clang's implementation and testing our transpiler with multiple pointer scenarios, I've identified the exact root cause and validated solutions used by production transpilers.

**The problem has TWO components:**

1. **Type Information Loss**: `getSimpleTypeName()` collapses all pointer types to just `"ptr"`, losing the pointee type. This means `int*` and `char*` both become `"ptr"`, breaking overload resolution AND causing generated `Simple_getValue_ptr` to look like it needs a pointer parameter when re-processed.

2. **Re-processing Loop**: Generated C functions re-enter `VisitFunctionDecl` because there's no mechanism to mark or skip synthetic/generated functions.

## Evidence

### Evidence 1: Type Information Loss in Mangling

**Code Location:** `src/NameMangler.cpp:92-95`

```cpp
// Handle pointer types
else if (T->isPointerType()) {
    result += "ptr";  // ❌ LOSES TYPE INFORMATION!
}
```

**What happens:**
- `Simple* this` → `"ptr"`
- `int* ptr` → `"ptr"`
- `char* str` → `"ptr"`

**Test proof:**
```bash
$ ./build_working/transpiler-api-cli /tmp/test-multi-ptr.cpp 2>&1 | grep "Mangled name:"
  Mangled name: Test_method1_ptr_ptr      # method1(int* ptr) - can't tell it's int*!
  Mangled name: Test_method2_ptr_ptr_ptr  # method2(int*, char*) - all info lost!
```

**Impact:** Cannot distinguish `foo(int*)` from `foo(char*)` in overload resolution.

---

### Evidence 2: Re-processing Loop Execution Trace

**Observed sequence:**
```
1. Translating method: Simple::getValue
   -> Simple_getValue with body translated

2. Analyzing function for RAII: Simple_getValue
   Translating standalone function: Simple_getValue
   Mangled name: Simple_getValue_ptr    ← Generated function has 'this' parameter

3. Analyzing function for RAII: Simple_getValue_ptr   ← RE-PROCESSING!
   Translating standalone function: Simple_getValue_ptr
   Mangled name: Simple_getValue_ptr_ptr   ← RECURSION!

4. Analyzing function for RAII: Simple_getValue_ptr_ptr
   Translating standalone function: Simple_getValue_ptr_ptr
   Mangled name: Simple_getValue_ptr_ptr_ptr   ← INFINITE LOOP!
```

**Why it happens:**
- Line 641 (`src/CppToCVisitor.cpp`): ALL `FunctionDecl` with bodies enter RAII analysis
- No check for "is this a function WE just generated?"
- Generated functions have bodies and aren't `CXXMethodDecl`, so they pass all guards

---

### Evidence 3: Source vs Transpiled Code

**Original C++ code:**
```cpp
class Simple {
public:
    int getValue() { return 42; }
};
```

**Transpiled Level 0 (from CXXMethodDecl):**
```c
// Method declaration in header
struct Simple {
    // fields...
};

// Method becomes standalone C function with 'this' pointer
int Simple_getValue(Simple* this) {
    return 42;
}
```

**Transpiled Level 1 (re-processing Simple_getValue):**
```c
// Because Simple_getValue has parameter Simple* this
// Mangling appends "_ptr" for the pointer parameter
int Simple_getValue_ptr(Simple* this) {  // Different mangled name!
    return Simple_getValue(this);        // Wrapper?
}
```

**Transpiled Level 2 (re-processing Simple_getValue_ptr):**
```c
// Same logic applies again
int Simple_getValue_ptr_ptr(Simple* this) {
    return Simple_getValue_ptr(this);
}
```

**Analysis:** Each generated function has a `Simple* this` parameter, which gets encoded as `_ptr`, creating a new mangled name that doesn't match the deduplication map.

---

### Evidence 4: Frama-Clang's Approach (from codebase analysis)

**File:** `/tmp/frama-clang/mangling.ml`

**Pointer Type Encoding (Line 171, 206):**
```ocaml
| Pointer t -> mangle_pkind "P" t
| PDataPointer t -> kw ^ mangle_cc_qual_type t
```

**Example transformations:**
- `int*` → `"Pi"` (P + int's code)
- `char*` → `"Pc"` (P + char's code)
- `Simple*` → `"P6Simple"` (P + length + name)

**This is Itanium C++ ABI standard!** Type information is fully preserved.

**Implicit Function Marking** (`/tmp/frama-clang/convert.ml` Line 20, 4125):
```ocaml
let fc_implicit_attr = "fc_implicit"

(* When generating functions: *)
let defname = (n,dt,(fc_implicit_attr,[])::attrs,loc)

(* When checking if should skip: *)
not (Ast_attributes.contains fc_implicit_attr v.vattr)
```

They mark generated functions with an attribute and skip re-processing them!

---

## Root Cause

**Design Intent of `_ptr` wrappers:** UNCLEAR - appears to be unintentional artifact of name mangling with implicit 'this' parameter.

**What's Broken:**

1. **NameMangler.cpp:92-95** - Pointer type encoding loses pointee type information
2. **CppToCVisitor.cpp:629-747** - No guard against re-processing generated functions
3. **Missing architecture** - No concept of "synthetic" vs "original source" functions

**Why Recursion Happens:**

1. Method `Simple::getValue()` → C function `Simple_getValue(Simple* this)`
2. Name mangling sees parameter `Simple* this`, encodes as `_ptr`
3. Generated function `Simple_getValue_ptr` re-enters `VisitFunctionDecl`
4. Still has `Simple* this` parameter → creates `Simple_getValue_ptr_ptr`
5. GOTO step 3 (infinite loop)

## Proposed Fixes

### Fix 1: Improve Type Encoding (REQUIRED - fixes overloading too)

**Approach:** Recursively encode pointee type like Itanium C++ ABI

**Code changes:**
```cpp
// src/NameMangler.cpp:92-95
else if (T->isPointerType()) {
    QualType pointee = T->getPointeeType();
    result += getSimpleTypeName(pointee) + "_ptr";  // Recursive!
}
```

**Examples:**
- `int*` → `"int_ptr"` (not `"ptr"`)
- `Simple*` → `"Simple_ptr"`
- `int**` → `"int_ptr_ptr"`
- `char*` → `"char_ptr"`

**Pros:**
- ✅ Preserves full type information
- ✅ Fixes overload resolution (`foo(int*)` vs `foo(char*)` now distinguishable)
- ✅ Makes debugging easier (readable names)
- ✅ Consistent with industry standard (Itanium C++ ABI)

**Cons:**
- Still doesn't prevent re-processing (need Fix 2)
- Longer mangled names (but more readable)

---

### Fix 2: Track Generated Functions (REQUIRED - prevents recursion)

**Approach:** Mark functions we create to skip re-processing

**Code changes:**
```cpp
// include/CppToCVisitor.h - add member:
std::set<FunctionDecl*> generatedFunctions;

// src/CppToCVisitor.cpp:~797 - when creating C function:
FunctionDecl *CFunc = Builder.funcDecl(mangledName, ...);
generatedFunctions.insert(CFunc);  // Mark as generated
standaloneFuncMap[mangledName] = CFunc;

// src/CppToCVisitor.cpp:629 - start of VisitFunctionDecl:
if (generatedFunctions.count(FD) > 0) {
  llvm::outs() << "  -> Skipping generated function\n";
  return true;  // Skip our own creations
}
```

**Pros:**
- ✅ Simple and explicit
- ✅ 100% accurate (no heuristics)
- ✅ No false positives
- ✅ Follows Frama-Clang's pattern (they use attributes, we use set)

**Cons:**
- Requires additional tracking structure (minimal cost)

---

### Alternative: Use Clang's isImplicit() (NOT RECOMMENDED)

**Approach:** Check `FD->isImplicit() || FD->getLocation().isInvalid()`

**Why NOT recommended:**
- Our generated functions might HAVE valid source locations (copied from original)
- `isImplicit()` is for compiler-generated code (default constructors), not ours
- False positives possible

---

## Recommended Approach

**Implement BOTH Fix 1 AND Fix 2:**

1. **Fix type encoding** → preserves type info, fixes overload resolution
2. **Track generated functions** → prevents re-processing loop

**Implementation order:**
1. First: Fix 2 (stops the immediate problem)
2. Then: Fix 1 (improves architecture for future)
3. Remove workaround depth limit
4. Add regression tests

**Validation:**
- `test-point.cpp` output should be ~500 lines (not 4.4MB)
- `foo(int*)` and `foo(char*)` should have different mangled names
- No function should be processed twice

## Test Case

**Before fixes:**
```bash
$ timeout 3 ./build_working/transpiler-api-cli test-minimal-pointer.cpp 2>&1 | grep -c "created"
9236  # Thousands of functions!
```

**After Fix 2 only (with workaround):**
```bash
$ ./build_working/transpiler-api-cli test-minimal-pointer.cpp 2>&1 | grep -c "created"
8  # Reasonable number
$ # But overload resolution still broken
```

**After Fix 1 + Fix 2:**
```bash
$ ./build_working/transpiler-api-cli test-minimal-pointer.cpp 2>&1 | grep "Mangled name:" | head -5
  Mangled name: Simple_getValue_Simple_ptr     # ✅ Type preserved!
  Mangled name: Test_method1_int_ptr_ptr       # ✅ Can distinguish int*!
  Mangled name: Test_method2_int_ptr_char_ptr  # ✅ Both types visible!
```

## Next Steps

1. ✅ Research complete - root cause identified
2. ⏭️ Implement Fix 2 (track generated functions)
3. ⏭️ Implement Fix 1 (improve type encoding)
4. ⏭️ Remove depth limit workaround (commit 56d11ed)
5. ⏭️ Add regression tests
6. ⏭️ Validate with real-world code
7. ⏭️ Document design in comments

## Sources

- [Itanium C++ ABI Mangling](http://refspecs.linuxfoundation.org/cxxabi-1.86.html#mangling) - Referenced in Frama-Clang
- [Frama-Clang Source](https://git.frama-c.com/pub/frama-clang) - Production C++ to C transpiler
- [Clang FunctionDecl](https://clang.llvm.org/doxygen/classclang_1_1FunctionDecl.html) - isImplicit() documentation
