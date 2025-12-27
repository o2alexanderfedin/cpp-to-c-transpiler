# Research: Pointer Recursion Root Cause Investigation

<objective>
Thoroughly investigate WHY the transpiler generates infinite `_ptr` wrapper functions, understand the design intent, identify the actual root cause, and propose a proper fix (not a workaround).

**Why this matters:** The current "fix" (depth limit) is a band-aid that hides the problem. We need to understand:
1. What are these `_ptr` wrapper functions FOR?
2. Why are they being generated recursively?
3. What's the intended termination mechanism that's broken?
4. What would a proper fix look like?

**End goal:** Complete understanding of root cause with concrete examples of source code, transpiled output at each recursion level, and evidence-based fix proposal.
</objective>

<context>
**Current workaround:**
@src/CppToCVisitor.cpp:755-774 - Depth limit preventing >2 `_ptr` occurrences
Commit: `56d11ed`

**Symptoms observed:**
- Simple class `Point` with methods generates thousands of wrapper functions
- Pattern: `Point_getX` → `Point_getX_ptr` → `Point_getX_ptr_ptr` → `Point_getX_ptr_ptr_ptr` → ...
- Each generated function triggers "Analyzing function for RAII" which creates next level
- Output explodes from ~1KB to 4.4MB

**Test cases:**
@test-point.cpp - Original failing case (Point class)
@test-minimal-pointer.cpp - Minimal reproducer (Simple class)

**Key files:**
@src/CppToCVisitor.cpp - Main visitor, contains VisitFunctionDecl
@src/NameMangler.cpp - Name mangling logic (adds `_ptr` suffix)
@include/CppToCVisitor.h - Visitor class definition with maps
@src/TemplateMonomorphizer.cpp - Template handling (might be involved)

**Project conventions:**
@CLAUDE.md - TDD, SOLID, testing requirements
</context>

<research_questions>
## Critical Questions to Answer

### Q1: What Triggers Initial `_ptr` Wrapper Creation?
- **Where** in code does `Point_getX` become `Point_getX_ptr`?
- **Why** is this transformation happening?
- **What's the design intent** - ABI compatibility? Pointer-to-member handling? Template instantiation?

### Q2: Why Does Recursion Happen?
- After creating `Point_getX_ptr`, why does it get analyzed again?
- What makes the transpiler think generated functions are NEW input functions?
- Is there a missing "synthetic function" flag?
- Should RAII analyzer skip generated functions?

### Q3: What's the Intended Termination?
- Should there be a visited set that's not working?
- Should generated functions be marked differently?
- Is there supposed to be a separate map for synthetic functions?
- What prevents this in other transpilers?

### Q4: What Does Transpiled Code Look Like?
- Show EXACT transpiled output for `int getX() const { return x; }`
- Show what `Point_getX_ptr` looks like (signature, body)
- Show what `Point_getX_ptr_ptr` looks like
- Identify the pattern that causes recursion

### Q5: Where's the Loop?
- Trace exact execution path: `VisitFunctionDecl` → `mangleStandaloneFunction` → RAII analysis → ???
- What adds generated functions back to the AST for re-processing?
- Is this a visitor pattern issue?
</research_questions>

<experiments>
## Experiments to Run

### Experiment 1: Trace Execution with Logging
**Goal:** See exact call sequence and function names at each step

**Steps:**
1. Add detailed logging to `VisitFunctionDecl`:
   ```cpp
   llvm::outs() << "=== VisitFunctionDecl START ===\n";
   llvm::outs() << "  Function name: " << FD->getNameAsString() << "\n";
   llvm::outs() << "  Is implicit: " << FD->isImplicit() << "\n";
   llvm::outs() << "  Is templated: " << FD->isTemplateInstantiation() << "\n";
   llvm::outs() << "  Source location: " << FD->getLocation().printToString(SM) << "\n";
   ```

2. Run on minimal test:
   ```bash
   ./build_working/transpiler-api-cli test-minimal-pointer.cpp 2>&1 | head -200 > trace-minimal.txt
   ```

3. Analyze trace to find:
   - Which functions are from original source vs generated
   - What triggers re-analysis of generated functions
   - Call depth when recursion starts

**Expected outcome:** Clear evidence of where generated functions re-enter visitor

---

### Experiment 2: Compare Source vs Transpiled Code
**Goal:** See EXACTLY what gets generated at each recursion level

**Steps:**
1. Create ultra-minimal test (single method):
   ```cpp
   // test-single-method.cpp
   class Minimal {
   public:
       int get() { return 42; }
   };
   ```

2. Transpile with depth limit = 0 (skip all):
   ```bash
   # Temporarily set MAX_POINTER_DEPTH = 0
   ./build_working/transpiler-api-cli test-single-method.cpp --json 2>&1 | jq -r '.c' > depth-0.c
   ```

3. Transpile with depth limit = 1:
   ```bash
   # Set MAX_POINTER_DEPTH = 1
   ./build_working/transpiler-api-cli test-single-method.cpp --json 2>&1 | jq -r '.c' > depth-1.c
   ```

4. Compare:
   ```bash
   diff depth-0.c depth-1.c
   ```

5. Show:
   - Original C++ method signature
   - Transpiled `Minimal_get` signature and body
   - Generated `Minimal_get_ptr` signature and body
   - Identify the difference that triggers recursion

**Expected outcome:** Visual proof of what `_ptr` wrappers are and why they're created

---

### Experiment 3: Find Where Wrappers Are Created
**Goal:** Locate the EXACT code that generates `_ptr` variants

**Steps:**
1. Search for where functions are cloned/duplicated:
   ```bash
   grep -rn "FunctionDecl.*create\|cloneFunction\|addDecl.*Function" src/ include/
   ```

2. Search for where `_ptr` suffix is added during generation (not just mangling):
   ```bash
   grep -rn "ptr.*Builder\|Builder.*ptr\|funcDecl.*ptr" src/
   ```

3. Check if template monomorphization creates these:
   ```bash
   grep -rn "instantiate\|monomorphize" src/TemplateMonomorphizer.cpp src/CppToCVisitor.cpp
   ```

4. Look for code that processes parameter types and creates wrapper variants:
   ```bash
   grep -rn "getPointeeType\|PointerType.*generate" src/
   ```

**Expected outcome:** Source location where `_ptr` wrappers are intentionally created

---

### Experiment 4: Test Without RAII Analysis
**Goal:** Determine if RAII analyzer is the recursion trigger

**Steps:**
1. Temporarily comment out RAII analysis in `VisitFunctionDecl`:
   ```cpp
   // Story #152: Analyze function for RAII objects and inject destructors
   // llvm::outs() << "Analyzing function for RAII: " << FD->getNameAsString() << "\n";
   // ... (comment out entire RAII section)
   ```

2. Rebuild and test:
   ```bash
   cd build_working && make transpiler-api-cli
   ./transpiler-api-cli test-minimal-pointer.cpp 2>&1 | grep -c "created"
   ```

3. Compare function count:
   - With RAII: thousands
   - Without RAII: ???

**Expected outcome:** Proof whether RAII analysis triggers the recursion loop

---

### Experiment 5: Check standaloneFuncMap Usage
**Goal:** See if the deduplication map is working correctly

**Steps:**
1. Add logging when functions are added to map:
   ```cpp
   standaloneFuncMap[mangledName] = CFunc;
   llvm::outs() << "  -> Added to standaloneFuncMap (size: "
                << standaloneFuncMap.size() << ")\n";
   ```

2. Log when duplicate check happens:
   ```cpp
   if (standaloneFuncMap.count(mangledName) > 0) {
     llvm::outs() << "  -> Already in map, skipping (KEY WORKED!)\n";
     return true;
   }
   ```

3. Run test:
   ```bash
   ./build_working/transpiler-api-cli test-minimal-pointer.cpp 2>&1 | grep "standaloneFuncMap\|Already in map"
   ```

**Expected outcome:** Evidence if map-based deduplication is working or bypassed

---

### Experiment 6: Check Function Origin
**Goal:** Distinguish original vs generated functions

**Steps:**
1. Check if generated functions have different source locations:
   ```cpp
   SourceLocation loc = FD->getLocation();
   if (loc.isInvalid()) {
     llvm::outs() << "  -> GENERATED FUNCTION (invalid source location)\n";
   } else {
     llvm::outs() << "  -> ORIGINAL FUNCTION: "
                  << loc.printToString(Context.getSourceManager()) << "\n";
   }
   ```

2. Check for implicit/synthetic flags:
   ```cpp
   llvm::outs() << "  IsImplicit: " << FD->isImplicit() << "\n";
   llvm::outs() << "  IsDefaulted: " << FD->isDefaulted() << "\n";
   llvm::outs() << "  IsDeleted: " << FD->isDeleted() << "\n";
   ```

**Expected outcome:** Way to identify and skip generated functions

</experiments>

<verification>
Research is complete when we can answer ALL of these:

1. ✅ Exact code location where `_ptr` wrappers are first created
2. ✅ Clear explanation of WHAT these wrappers are FOR (design intent)
3. ✅ Execution trace showing recursion entry point
4. ✅ Side-by-side comparison of source code vs transpiled output at each recursion level
5. ✅ Evidence of what's broken (missing flag, broken map, incorrect visitor behavior)
6. ✅ Proposed fix with clear rationale (not a depth limit workaround)
7. ✅ Test case that proves the fix works and explains why

**Documentation required:**
- `30-02-FINDINGS.md` with all evidence
- Code snippets showing exact source → transpiled transformation
- Execution traces proving root cause
- Proposed fix with before/after examples
</verification>

<output>
Create: `.planning/phases/30-transpile-real-world-tests/30-02-FINDINGS.md`

**Required format:**

```markdown
# Pointer Recursion Root Cause Findings

**[One substantive sentence describing the root cause]**

## Executive Summary
[2-3 paragraphs explaining what we found]

## Evidence

### Evidence 1: Execution Trace
[Show exact function call sequence with logging output]

### Evidence 2: Source vs Transpiled Code
**Original C++ code:**
```cpp
[exact source]
```

**Transpiled Level 0 (base function):**
```c
[exact transpiled code for Point_getX]
```

**Transpiled Level 1 (_ptr wrapper):**
```c
[exact transpiled code for Point_getX_ptr]
```

**Transpiled Level 2 (_ptr_ptr wrapper):**
```c
[exact transpiled code for Point_getX_ptr_ptr]
```

**Analysis:** [Why does _ptr wrapper trigger creation of _ptr_ptr?]

### Evidence 3: Code Location
**File:** [exact file:line]
**Code:**
```cpp
[exact code that creates _ptr wrappers]
```

### Evidence 4: Missing Termination
[What's broken - missing flag, incorrect map, visitor bug, etc.]

## Root Cause

[Detailed explanation of WHY this happens]

**Design Intent:** [What _ptr wrappers are supposed to do]

**What's Broken:** [Specific mechanism that fails]

**Why Recursion Happens:** [Exact reason]

## Proposed Fix

### Option 1: [Name] (Recommended: Yes/No)
**Approach:** [How to fix]
**Pros:** [Benefits]
**Cons:** [Drawbacks]
**Code changes:** [Specific files and changes]

### Option 2: [Name] (Recommended: Yes/No)
[Same structure]

### Option 3: [Name] (Recommended: Yes/No)
[Same structure]

## Recommended Approach

[Clear recommendation with rationale]

## Test Case

**Before fix:**
```bash
[command showing bug]
# Output: [thousands of functions]
```

**After fix:**
```bash
[command showing fixed behavior]
# Output: [reasonable number of functions]
```

**Validation:**
```cpp
// Test that proves fix works
[minimal test case]
```

## Next Steps

1. Implement recommended fix
2. Add regression test
3. Validate with real-world code
4. Document design in comments
```
</output>

<success_criteria>
- Root cause identified with high confidence (>90%)
- All 6 experiments run with documented results
- Source code → transpiled code transformation fully documented
- Proposed fix addresses root cause, not symptoms
- Evidence is concrete (code snippets, execution traces, diffs)
- Findings document enables immediate implementation of proper fix
- User can see EXACTLY what fails and how it gets transpiled
</success_criteria>
