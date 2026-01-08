# Phase 2: Constructor Splitting (C1/C2 Variants) Implementation

<objective>
Implement Phase 2 of virtual inheritance support by integrating ConstructorSplitter into ConstructorHandler to generate C1 (complete object) and C2 (base object) constructor variants with VTT parameters.

This phase follows the completed Phase 1 (Foundation) which integrated VirtualInheritanceAnalyzer into RecordHandler, injected vbptr fields, and generated VTT structures. Phase 2 focuses on constructor handling to properly initialize objects with virtual inheritance.

**Why this matters:** Virtual inheritance requires different constructor variants based on whether the object is being constructed as a most-derived class (C1) or as a base subobject (C2). This is mandated by the Itanium C++ ABI and essential for correct virtual base initialization.
</objective>

<context>
**Project:** C++ to C Transpiler (3-stage pipeline: C++ AST → C AST → C Source)

**Current State:**
- Phase 1 complete: RecordHandler detects virtual bases, injects vbptr field, generates VTT
- ConstructorSplitter exists and has unit tests (12/15 passing - 80%)
- VirtualInheritanceAnalyzer exists and works correctly
- Implementation plan: VIRTUAL_INHERITANCE_IMPLEMENTATION_PLAN.md (Tasks 6-9, lines 191-313)

**Phase 2 Tasks:**
1. **Task 6**: Integrate ConstructorSplitter into ConstructorHandler (PRIORITY 1)
2. **Task 7**: Generate C1 constructor (complete object constructor)
3. **Task 8**: Generate C2 constructor (base object constructor)
4. **Task 9**: Add VTT parameter to both constructors

**Files to Examine:**
- Implementation plan: @VIRTUAL_INHERITANCE_IMPLEMENTATION_PLAN.md (lines 191-313)
- Target file: @src/dispatch/ConstructorHandler.cpp
- Reference: @include/ConstructorSplitter.h
- Reference: @include/VirtualInheritanceAnalyzer.h
- Pattern to follow: @src/dispatch/RecordHandler.cpp (Phase 1 implementation)

**Testing Strategy:**
- Unit tests already exist: tests/unit/ConstructorSplitterCorrectnessTest.cpp
- Goal: Improve pass rate from 12/15 (80%) to 15/15 (100%)
- Run tests after implementation to verify correctness
</context>

<requirements>

## Functional Requirements

### Task 6: ConstructorSplitter Integration (PRIORITY 1)
1. Add includes to ConstructorHandler.cpp:
   - `#include "ConstructorSplitter.h"`
   - `#include "VirtualInheritanceAnalyzer.h"`

2. In `handleConstructor()` function, after getting parent class:
   - Create VirtualInheritanceAnalyzer instance
   - Analyze the parent class for virtual bases
   - Check if ANY class in hierarchy has virtual bases (iterate through bases)
   - Set `needsC1C2Split` flag if virtual bases detected

3. Detection logic must check:
   - Direct virtual bases of parent class
   - Virtual bases in any base class in the hierarchy
   - Indirect virtual bases (inherited through intermediate classes)

### Task 7: C1 Constructor Generation
1. When `needsC1C2Split` is true, generate C1 variant
2. C1 constructor responsibilities (in order):
   - Construct virtual bases FIRST (depth-first order)
   - Then construct non-virtual bases (calling their C2 constructors)
   - Initialize own members
   - Set vtable pointers from VTT

3. Implementation pattern:
   ```cpp
   if (needsC1C2Split) {
       ConstructorSplitter splitter(const_cast<clang::ASTContext&>(cppASTContext), viAnalyzer);
       std::string c1Code = splitter.generateC1Constructor(parentClass);

       // TODO: Create C AST FunctionDecl for C1 constructor
       // For Phase 2 MVP, logging the generated code is acceptable
       llvm::outs() << "[ConstructorHandler] Generated C1 constructor for "
                    << className << "\n";
   }
   ```

### Task 8: C2 Constructor Generation
1. When `needsC1C2Split` is true, generate C2 variant
2. C2 constructor responsibilities (in order):
   - SKIP virtual base construction (most-derived constructor handles this)
   - Construct non-virtual bases only
   - Initialize own members
   - Set vtable pointers from VTT

3. Critical distinction: C2 is called when object is a base subobject, not the most-derived object

### Task 9: VTT Parameter Addition
1. Both C1 and C2 constructors need VTT parameter after 'this' parameter
2. VTT type: `const void** vtt`
3. Implementation pattern:
   ```cpp
   clang::QualType vttParamType = cASTContext.getPointerType(
       cASTContext.getPointerType(cASTContext.VoidTy.withConst())
   );

   clang::IdentifierInfo& vttII = cASTContext.Idents.get("vtt");

   clang::ParmVarDecl* vttParam = clang::ParmVarDecl::Create(
       cASTContext,
       nullptr,  // DeclContext set later
       targetLoc,
       targetLoc,
       &vttII,
       vttParamType,
       cASTContext.getTrivialTypeSourceInfo(vttParamType),
       clang::SC_None,
       nullptr
   );

   allParams.push_back(vttParam);  // After 'this' parameter
   ```

## Code Quality Requirements
- Follow existing patterns from Phase 1 (RecordHandler integration)
- Use proper source location tracking (SourceLocationMapper)
- Add debug output (llvm::outs) for all major operations
- Handle edge cases: classes without constructors, empty classes
- Ensure const-correctness (use const_cast only where necessary)
- Follow SOLID principles (particularly SRP - Single Responsibility)

## Testing Requirements
- Run ConstructorSplitterCorrectnessTest after implementation
- Target: 15/15 tests passing (100%)
- Fix any failing tests related to indirect virtual base detection
- Verify detection works for diamond patterns, deep hierarchies
</requirements>

<implementation>

## Step-by-Step Implementation

### Step 1: Read and Understand Current State
1. Read @src/dispatch/ConstructorHandler.cpp to understand current implementation
2. Identify the `handleConstructor()` function
3. Locate where parent class is obtained
4. Understand existing constructor generation logic

### Step 2: Integrate ConstructorSplitter (Task 6)
1. Add necessary includes at the top of ConstructorHandler.cpp
2. In `handleConstructor()`, after getting parent class:
   - Create VirtualInheritanceAnalyzer instance
   - Analyze parent class and all base classes
   - Implement detection loop for virtual bases in hierarchy
   - Set `needsC1C2Split` flag appropriately
3. Add debug output to report when C1/C2 splitting is needed

### Step 3: Generate C1 Constructor (Task 7)
1. Create conditional block: `if (needsC1C2Split)`
2. Instantiate ConstructorSplitter with ASTContext and analyzer
3. Call `generateC1Constructor(parentClass)`
4. Log the generated C1 constructor code
5. Add TODO comment for future C AST node creation

### Step 4: Generate C2 Constructor (Task 8)
1. Within same conditional block
2. Call `generateC2Constructor(parentClass)`
3. Log the generated C2 constructor code
4. Add TODO comment for future C AST node creation

### Step 5: Add VTT Parameter (Task 9)
1. Create VTT parameter type: `const void**`
2. Create ParmVarDecl for VTT parameter
3. Insert VTT parameter after 'this' parameter in parameter list
4. Ensure VTT parameter is added to both C1 and C2 constructors

### Step 6: Build and Test
1. Build the project: `cd build_working && cmake --build . -j4`
2. Build test executable: `cmake --build . --target ConstructorSplitterCorrectnessTest`
3. Run tests: `./ConstructorSplitterCorrectnessTest`
4. Analyze failures and fix issues
5. Repeat until 15/15 tests passing

## What to Avoid (and WHY)

❌ **Don't create C AST nodes yet** - Phase 2 focuses on integration and code generation. C AST node creation is deferred to Phase 3. WHY: String-based code generation is simpler for MVP and allows us to verify logic before committing to AST structure.

❌ **Don't skip indirect virtual base detection** - Must check entire hierarchy, not just direct bases. WHY: Diamond patterns and deep hierarchies have indirect virtual bases that must be detected for correct constructor splitting.

❌ **Don't modify ConstructorSplitter.cpp** - Focus only on integration in ConstructorHandler. WHY: ConstructorSplitter is already tested and working. If tests fail, the issue is likely in detection logic, not generation logic.

❌ **Don't ignore const-correctness** - Use const_cast only where ASTContext parameter requires non-const. WHY: Maintains type safety and follows C++ best practices.

❌ **Don't skip debug output** - Log all major operations for debugging. WHY: Virtual inheritance is complex; comprehensive logging helps diagnose issues during testing.

## Patterns to Follow

✅ **Follow Phase 1 pattern** - Review @src/dispatch/RecordHandler.cpp (lines 213-230) for how VirtualInheritanceAnalyzer was integrated. Use the same pattern in ConstructorHandler.

✅ **Defensive programming** - Check for null pointers, handle edge cases (empty classes, no constructors). WHY: Transpiler must be robust across all valid C++ code.

✅ **Incremental approach** - Implement Task 6 first, verify it works, then proceed to Tasks 7-9. WHY: Early detection of issues prevents cascading failures.
</implementation>

<output>
**Modified Files:**
- `./src/dispatch/ConstructorHandler.cpp` - Add ConstructorSplitter integration, C1/C2 generation, VTT parameters

**Expected Changes:**
- Approximately 80-120 lines added
- New includes: ConstructorSplitter.h, VirtualInheritanceAnalyzer.h
- New detection logic in handleConstructor()
- New conditional block for C1/C2 generation
- New VTT parameter creation code
- Debug output for all major operations

**Console Output After Implementation:**
When processing classes with virtual bases, you should see:
```
[ConstructorHandler] Class Diamond needs C1/C2 splitting (has virtual bases)
[ConstructorHandler] Generated C1 constructor for Diamond
[ConstructorHandler] Generated C2 constructor for Diamond
```
</output>

<verification>
Before declaring Phase 2 complete, verify:

1. **Code Compiles:**
   - Run: `cd build_working && cmake --build . --target cpptoc_core -j4`
   - No compilation errors

2. **Tests Pass:**
   - Run: `cmake --build . --target ConstructorSplitterCorrectnessTest -j4`
   - Run: `./ConstructorSplitterCorrectnessTest`
   - Expected: 15/15 tests passing (100%)
   - If failures remain, analyze and fix detection logic

3. **Detection Works:**
   - SimpleVirtualBase: Detected and split ✓
   - DiamondPattern: Detected and split ✓
   - IndirectVirtualBase: Detected and split ✓ (critical test)
   - DeepHierarchy: Detected and split ✓

4. **Integration Correct:**
   - VirtualInheritanceAnalyzer properly instantiated
   - Hierarchy traversal includes all base classes
   - needsC1C2Split flag set correctly
   - Both C1 and C2 constructors generated
   - VTT parameters added to both constructors

5. **Debug Output Present:**
   - All major operations logged to llvm::outs()
   - Clear indication when splitting is needed
   - Confirmation when constructors generated
</verification>

<success_criteria>
- ✅ All 4 tasks (6-9) implemented according to plan
- ✅ ConstructorSplitterCorrectnessTest: 15/15 passing (100%)
- ✅ Code compiles without errors or warnings
- ✅ Detection logic handles indirect virtual bases
- ✅ Both C1 and C2 constructors generated when needed
- ✅ VTT parameters added to both constructor variants
- ✅ Debug output comprehensive and clear
- ✅ Code follows existing patterns from Phase 1
- ✅ Changes committed with descriptive message following project conventions

**Commit Message Format:**
```
feat(phase56): implement virtual inheritance Phase 2 - constructor splitting

Integrate ConstructorSplitter into ConstructorHandler for C1/C2 generation

Phase 2 Tasks Completed:
✅ Task 6: Integrated ConstructorSplitter and VirtualInheritanceAnalyzer
✅ Task 7: Generated C1 (complete object) constructor
✅ Task 8: Generated C2 (base object) constructor
✅ Task 9: Added VTT parameters to both constructors

Test Results:
- ConstructorSplitterCorrectnessTest: 15/15 passing (100%)

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
```
</success_criteria>

<notes>
**Estimated Effort:** 2-3 hours

**Key Challenge:** Indirect virtual base detection - must traverse entire hierarchy, not just direct bases.

**Phase 3 Preview:** After Phase 2, Phase 3 will focus on VTable enhancement (Task 5), creating proper C AST nodes instead of string generation, and enabling integration/E2E tests.

**Reference Implementation:** Phase 1 (RecordHandler) is in commit ed7d2db. Study this commit for patterns and approach.
</notes>
