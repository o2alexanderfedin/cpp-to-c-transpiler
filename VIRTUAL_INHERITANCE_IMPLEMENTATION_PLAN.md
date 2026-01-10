# Virtual Inheritance Implementation Plan

**Date:** 2026-01-07
**Engineer:** Claude Code (Sonnet 4.5)
**Task:** Implement complete multiple and virtual inheritance handler support
**Based on:** audit-reports/inheritance-handlers-audit.md

---

## Executive Summary

### Current State
- ✅ Virtual inheritance analyzers EXIST and WORK (VirtualInheritanceAnalyzer, VTTGenerator, ConstructorSplitter)
- ✅ Unit tests for analyzers PASS (8/8 VirtualBaseDetectionTest, etc.)
- ❌ RecordHandler SKIPS all polymorphic classes (lines 174-183)
- ❌ Analyzers NOT integrated into handler dispatch chain
- ⚠️ RuntimeFeatureFlags marks VInherit as available but implementation incomplete

### Implementation Goal
Integrate existing analyzer components into the handler dispatch pipeline to enable complete virtual inheritance support.

---

## Architecture: 3-Stage Pipeline

```
Stage 1: C++ AST (from Clang)
    ↓
Stage 2: C AST (handler chain creates C nodes - THIS IS WHERE WE WORK)
    ↓
Stage 3: C Source (code printer emits text)
```

**Critical Principle:** Handlers (Stage 2) make ALL translation decisions and create C AST nodes. They do NOT emit text.

---

## Implementation Tasks

### Task 1: Remove Polymorphic Class Skip in RecordHandler ✅ PRIORITY 1
**File:** `src/dispatch/RecordHandler.cpp` lines 174-183

**Current Code:**
```cpp
// Skip polymorphic classes (vtables not supported yet)
if (const auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(cppRecord)) {
    if (cxxRecord->isPolymorphic()) {
        llvm::errs() << "[RecordHandler] Warning: Skipping polymorphic class (vtables not supported): "
                     << name << "\n";
        return;
    }
}
```

**Action:** REMOVE this block entirely (6 lines)

**Rationale:** Phase 45/46 implemented virtual methods and multiple inheritance. This skip code is obsolete and prevents virtual inheritance from working.

**Risk:** LOW - Virtual methods already work (41/41 tests passing)

---

### Task 2: Integrate VirtualInheritanceAnalyzer into RecordHandler ✅ PRIORITY 1
**File:** `src/dispatch/RecordHandler.cpp`

**Location:** After removing skip code, before field translation (around line 220)

**Code to Add:**
```cpp
#include "VirtualInheritanceAnalyzer.h"
#include "MultipleInheritanceAnalyzer.h"
#include "VTTGenerator.h"

// ... in handleRecord() function, after cRecord->startDefinition():

// Analyze virtual inheritance (if applicable)
bool hasVirtualBases = false;
std::vector<const clang::CXXRecordDecl*> virtualBases;

if (const auto* cxxRecord = llvm::dyn_cast<clang::CXXRecordDecl>(cppRecord)) {
    VirtualInheritanceAnalyzer viAnalyzer;
    viAnalyzer.analyzeClass(cxxRecord);

    hasVirtualBases = viAnalyzer.hasVirtualBases(cxxRecord);

    if (hasVirtualBases) {
        virtualBases = viAnalyzer.getVirtualBases(cxxRecord);
        llvm::outs() << "[RecordHandler] Class " << name
                     << " has " << virtualBases.size()
                     << " virtual base(s)\n";
    }
}
```

**Test:** VirtualBaseDetectionTest should still pass

---

### Task 3: Inject vbptr Field in RecordHandler ✅ PRIORITY 1
**File:** `src/dispatch/RecordHandler.cpp`

**Location:** Before regular field translation (around line 225)

**Pattern:** Follow lpVtbl injection pattern from Phase 45/46

**Code to Add:**
```cpp
// Inject vbptr field for classes with virtual bases
if (hasVirtualBases) {
    // Create vbptr field: const void** vbptr;
    clang::QualType vbptrType = cASTContext.getPointerType(
        cASTContext.getPointerType(cASTContext.VoidTy.withConst())
    );

    clang::IdentifierInfo& vbptrII = cASTContext.Idents.get("vbptr");

    clang::FieldDecl* vbptrField = clang::FieldDecl::Create(
        cASTContext,
        cRecord,
        targetLoc,
        targetLoc,
        &vbptrII,
        vbptrType,
        cASTContext.getTrivialTypeSourceInfo(vbptrType),
        nullptr,  // No bit width
        false,    // Not mutable
        clang::ICIS_NoInit
    );

    vbptrField->setAccess(clang::AS_public);
    vbptrField->setDeclContext(cRecord);
    cRecord->addDecl(vbptrField);

    llvm::outs() << "[RecordHandler] Injected vbptr field for virtual inheritance\n";
}
```

**Test:** Create unit test to verify vbptr field injection

---

### Task 4: Generate and Emit VTT Structs/Instances ✅ PRIORITY 2
**File:** `src/dispatch/RecordHandler.cpp`

**Location:** After complete definition (around line 234)

**Code to Add:**
```cpp
// Generate VTT (Virtual Table Table) for classes with virtual bases
if (hasVirtualBases) {
    VTTGenerator vttGen(const_cast<clang::ASTContext&>(cppASTContext), viAnalyzer);

    std::string vttCode = vttGen.generateVTT(cxxRecord);

    if (!vttCode.empty()) {
        // TODO: For now, log VTT generation. In future, emit to output file.
        llvm::outs() << "[RecordHandler] Generated VTT for " << name << ":\n"
                     << vttCode << "\n";

        // TODO: Create C AST nodes for VTT struct and instance
        // This requires extending CNodeBuilder with VTT generation methods
    }
}
```

**Note:** VTT code generation currently returns strings, not C AST nodes. This violates pipeline separation but is acceptable for Phase 1. Pipeline compliance refactoring can be done later (Gap 11 in audit report).

**Test:** VTTGeneratorTest should still pass

---

### Task 5: Activate Virtual Base Offsets in VtableGenerator ✅ PRIORITY 2
**File:** `src/dispatch/RecordHandler.cpp` (where vtable generation happens)

**Pattern:** Check if class has virtual bases, call `generateVtableWithVirtualBaseOffsets()` instead of regular generation

**Code to Add:**
```cpp
// When generating vtable for polymorphic classes with virtual bases:
if (hasVirtualBases) {
    // Use virtual-base-aware vtable generation
    std::string vtableCode = vtableGen.generateVtableWithVirtualBaseOffsets(cxxRecord, viAnalyzer);
    // Emit vtable code
}
```

**Note:** Need to locate where vtable generation currently happens in RecordHandler. If it doesn't happen there, this may need to be in VtableGenerator's existing integration point.

---

### Task 6: Integrate ConstructorSplitter into ConstructorHandler ✅ PRIORITY 1
**File:** `src/dispatch/ConstructorHandler.cpp`

**Location:** In `handleConstructor()` function, after getting parent class

**Code to Add:**
```cpp
#include "ConstructorSplitter.h"
#include "VirtualInheritanceAnalyzer.h"

// ... in handleConstructor():

// Check if class hierarchy has virtual bases
VirtualInheritanceAnalyzer viAnalyzer;
viAnalyzer.analyzeClass(parentClass);

bool needsC1C2Split = false;
// Check if ANY class in hierarchy has virtual bases
for (auto base : parentClass->bases()) {
    const auto* baseRecord = base.getType()->getAsCXXRecordDecl();
    if (baseRecord) {
        viAnalyzer.analyzeClass(baseRecord);
        if (viAnalyzer.hasVirtualBases(baseRecord)) {
            needsC1C2Split = true;
            break;
        }
    }
}

if (viAnalyzer.hasVirtualBases(parentClass)) {
    needsC1C2Split = true;
}
```

**Test:** Create test verifying detection of virtual inheritance in constructor handling

---

### Task 7: Generate C1 Constructor (Complete Object) ✅ PRIORITY 2
**File:** `src/dispatch/ConstructorHandler.cpp`

**Action:** When `needsC1C2Split` is true, generate C1 constructor variant

**Code Pattern:**
```cpp
if (needsC1C2Split) {
    ConstructorSplitter splitter(const_cast<clang::ASTContext&>(cppASTContext), viAnalyzer);

    std::string c1Code = splitter.generateC1Constructor(parentClass);

    // TODO: Create C AST FunctionDecl for C1 constructor
    // Add VTT parameter: const void** vtt
    llvm::outs() << "[ConstructorHandler] Generated C1 constructor for "
                 << className << "\n";
}
```

**C1 Constructor Responsibilities:**
1. Construct virtual bases FIRST (in depth-first order)
2. Then construct non-virtual bases (calling their C2 constructors)
3. Initialize own members
4. Set vtable pointers from VTT

**Test:** ConstructorSplitterTest should verify C1 generation

---

### Task 8: Generate C2 Constructor (Base Object) ✅ PRIORITY 2
**File:** `src/dispatch/ConstructorHandler.cpp`

**Action:** When `needsC1C2Split` is true, generate C2 constructor variant

**Code Pattern:**
```cpp
if (needsC1C2Split) {
    std::string c2Code = splitter.generateC2Constructor(parentClass);

    // TODO: Create C AST FunctionDecl for C2 constructor
    // Add VTT parameter: const void** vtt
    llvm::outs() << "[ConstructorHandler] Generated C2 constructor for "
                 << className << "\n";
}
```

**C2 Constructor Responsibilities:**
1. SKIP virtual base construction (caller handles it)
2. Construct non-virtual bases only
3. Initialize own members
4. Set vtable pointers from VTT

**Critical:** C2 is called when object is a base subobject, not the most-derived object.

---

### Task 9: Add VTT Parameter to Constructors ✅ PRIORITY 2
**File:** `src/dispatch/ConstructorHandler.cpp`

**Action:** Both C1 and C2 constructors need VTT parameter

**Code Pattern:**
```cpp
// Add VTT parameter after 'this' parameter
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

---

### Task 10: Write Integration Tests ✅ PRIORITY 3
**File:** `tests/integration/handlers/VirtualInheritanceIntegrationTest.cpp` (NEW)

**Test Scenarios:**
1. SimpleVirtualBase - Single virtual base, verify VTT and vbptr
2. DiamondPattern - Classic Base←Left/Right←Diamond, verify single Base instance
3. MixedInheritance - Mix of virtual and non-virtual bases
4. VirtualBaseAccess - Access virtual base members
5. C1C2ConstructorGeneration - Verify both constructor variants generated
6. VTTParameterPassing - Verify VTT parameter in constructors
7. VirtualBaseConstructionOrder - Verify construction order correctness

**Pattern:** Follow `MultipleInheritanceIntegrationTest.cpp` structure (37 tests in Phase 46)

---

### Task 11: Write E2E Tests ✅ PRIORITY 3
**File:** `tests/e2e/phase56/VirtualInheritanceE2ETest.cpp` (NEW)

**Test Scenarios:**
1. ClassicDiamond - Animal/Dog/Cat/Hybrid pattern
2. IOStreamStyle - ios_base←istream/ostream←iostream (virtual)
3. MixinPattern - Multiple virtual bases as mixins
4. MultiLevelVirtual - A←B←C (all virtual)
5. ComplexGraph - Multiple diamonds, multiple paths

**Verification:**
- Generated C code compiles without warnings
- Executable runs without errors
- Output matches expected behavior
- Memory layout correct (sizeof checks)

---

### Task 12: Update Runtime Configuration ✅ PRIORITY 4
**File:** `include/RuntimeFeatureFlags.h`

**Action:** Update documentation/comments to reflect that VInherit is now implemented

**Current:**
```cpp
VInherit      ///< Virtual inheritance support (virtual base tables)
```

**Update to:**
```cpp
VInherit      ///< Virtual inheritance support (IMPLEMENTED: vbptr, VTT, C1/C2 constructors)
```

**File:** Any documentation mentioning "not implemented" for virtual inheritance

---

### Task 13: Update TO-DOS.md ✅ PRIORITY 4
**File:** `TO-DOS.md`

**Action:** Mark virtual inheritance todo as COMPLETED with implementation summary

**Format:**
```markdown
## ✅ COMPLETED: Virtual Inheritance Implementation - 2026-01-07

**Status:** COMPLETED - Handler integration complete, all tests passing

**Implementation:** Integrated VirtualInheritanceAnalyzer, VTTGenerator, and ConstructorSplitter into handler dispatch chain

**Changes:**
- ✅ Removed polymorphic class skip in RecordHandler
- ✅ Integrated VirtualInheritanceAnalyzer
- ✅ Injected vbptr field for classes with virtual bases
- ✅ Generated VTT structs and instances
- ✅ Activated virtual base offset table in vtables
- ✅ Implemented C1/C2 constructor splitting
- ✅ Added VTT parameter to constructors
- ✅ Integration tests: XX/XX passing
- ✅ E2E tests: XX/XX passing
- ✅ All existing tests still passing (41+/41+ or more)

**Files Modified:**
- `src/dispatch/RecordHandler.cpp`
- `src/dispatch/ConstructorHandler.cpp`
- `tests/integration/handlers/VirtualInheritanceIntegrationTest.cpp` (NEW)
- `tests/e2e/phase56/VirtualInheritanceE2ETest.cpp` (NEW)

**Release:** vX.XX.X
```

---

## Implementation Order (TDD Approach)

### Phase 1: Foundation (Tasks 1-4)
1. Remove polymorphic skip code
2. Integrate VirtualInheritanceAnalyzer
3. Inject vbptr field
4. Generate and log VTT (basic integration)

**Verification:** Existing tests still pass, new logs show detection

### Phase 2: Constructor Splitting (Tasks 6-9)
1. Integrate ConstructorSplitter
2. Generate C1 constructor
3. Generate C2 constructor
4. Add VTT parameter

**Verification:** ConstructorSplitterTest passes, constructors generated

### Phase 3: Vtable Enhancement (Task 5)
1. Activate virtual base offset generation

**Verification:** VirtualBaseOffsetTableTest passes

### Phase 4: Testing (Tasks 10-11)
1. Write integration tests
2. Write E2E tests
3. Achieve 100% pass rate

**Verification:** All tests green

### Phase 5: Documentation (Tasks 12-13)
1. Update runtime configuration
2. Update TO-DOS.md

---

## Success Criteria

- ✅ All gaps from audit report addressed
- ✅ All new tests pass
- ✅ All existing tests continue passing (41+ tests)
- ✅ Handlers integrated into dispatch system properly
- ✅ VTable generation includes virtual base offsets
- ✅ Constructor handling emits C1/C2 variants
- ✅ Runtime configuration updated (no "not implemented" markers)
- ✅ Code follows established patterns and conventions
- ✅ Zero compiler warnings
- ✅ Manual transpilation test succeeds
- ✅ TO-DOS.md updated to mark completion

---

## Risk Assessment

### Low Risk
- Task 1 (Remove skip code) - Virtual methods already working
- Task 2 (Integrate analyzer) - Analyzer already tested and working
- Task 3 (vbptr injection) - Same pattern as lpVtbl injection

### Medium Risk
- Task 4 (VTT emission) - String-based, not C AST (pipeline violation, but acceptable for MVP)
- Tasks 6-9 (Constructor splitting) - Complex logic, needs careful testing

### High Risk
- Integration with existing vtable generation - May have unexpected interactions
- E2E tests - Need complete end-to-end flow to work

### Mitigation
- Incremental implementation with testing after each task
- Keep existing tests passing at all times
- Follow TDD: tests before/during implementation
- Use existing patterns (MultipleInheritanceAnalyzer integration as template)

---

## Estimated Effort

- Phase 1 (Foundation): 4-6 hours
- Phase 2 (Constructors): 8-10 hours
- Phase 3 (Vtables): 3-4 hours
- Phase 4 (Testing): 10-15 hours
- Phase 5 (Docs): 2-3 hours

**Total: 27-38 hours** (approximately 1-1.5 weeks full-time)

This is less than the audit report's 43-55 hours estimate because:
1. Analyzers already exist and work
2. We're following established patterns from Phase 45/46
3. We have clear guidance from audit report

---

## Notes

- This plan focuses on **integration**, not creating new analyzers from scratch
- Follows **3-stage pipeline** architecture strictly
- Uses **TDD** methodology throughout
- Maintains **backward compatibility** (all existing tests must pass)
- Accepts **string-based code generation** as temporary solution (can refactor to C AST later)

---

**End of Implementation Plan**
