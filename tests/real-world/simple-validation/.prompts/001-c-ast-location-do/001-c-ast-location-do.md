# Implementation: C AST Node Location Tracking Architecture

## Objective

Implement a new architecture for the C++ to C transpiler that tracks each C AST node's output file location, preventing duplicate declarations and ensuring proper code structure across multiple output files.

**Why this matters:**
- Current architecture creates duplicate enums/structs when same header is included by multiple .cpp files
- Method declarations are missing from header files
- Tests failing at 20% (1/5) instead of required 100% pass rate
- Redefinition errors prevent compilation of transpiled code

**Success criteria:**
- Each C AST node associated with exactly one output file location
- Zero duplicate declarations in transpiled output
- All method declarations properly added to corresponding header files
- 100% (5/5) test pass rate achieved
- Clean compilation of all transpiled C code

## Current Architecture Issues

### Problem 1: Enum Duplication
```
GameState enum defined in include/GameState.h
├─ Included by src/StateMachine.cpp → emits to transpiled/src/StateMachine.h
└─ Included by main.cpp → emits to transpiled/main.h

Result: Redefinition error (GameState defined twice)
```

### Problem 2: Missing Method Declarations
```
StateMachine::transition() in src/StateMachine.cpp
├─ Implementation emitted to transpiled/src/StateMachine.c ✓
├─ Declaration missing from transpiled/src/StateMachine.h ✗
└─ Called from main.c → compilation error (undeclared function)
```

### Root Cause
- Each .cpp file creates separate C++ AST instance
- All C nodes created in shared C ASTContext (correct)
- NO tracking of which output file each C node belongs to
- CppToCVisitor adds nodes to C_TranslationUnit without deduplication
- Same header processed multiple times → duplicate C nodes

## New Architecture Design

### Core Principle
**Each C AST node has exactly one output file location**

### Data Structure
Add to TargetContext or PathMapper:
```cpp
// Map: C AST node → output file path
std::map<const clang::Decl*, std::string> nodeToLocation;

// Map: Enum/Struct name → existing C node (for deduplication)
std::map<std::string, clang::EnumDecl*> globalEnums;
std::map<std::string, clang::RecordDecl*> globalStructs;
```

### Emission Rules

**For each C AST node with location `<path>/<to>/<file-name>.c`:**

1. **Declarations** → `<path>/<to>/<file-name>.h`
   - Enum definitions
   - Struct definitions
   - Typedef declarations
   - Function prototypes
   - Extern variable declarations

2. **Implementations** → `<path>/<to>/<file-name>.c`
   - Function bodies
   - Method implementations
   - Constructor/destructor implementations
   - Static variable definitions

3. **Includes** → `<path>/<to>/<file-name>.c`
   - Always: `#include "<path>/<to>/<file-name>.h"`

4. **Cross-file includes** → `<path>/<to>/<file-name>.h`
   - For each C AST node dependency from `<another-file>.c`:
     - Add: `#include "<path>/<to>/<another-file>.h"`

### Deduplication Algorithm

**On VisitEnumDecl:**
```
1. Get enum name (e.g., "GameState")
2. Check globalEnums map
3. If exists:
   - Reuse existing C EnumDecl
   - Do NOT create new node
   - Do NOT add to C_TranslationUnit
4. If new:
   - Create C EnumDecl
   - Store in globalEnums[name]
   - Record location: nodeToLocation[C_Enum] = currentOutputPath
   - Add to C_TranslationUnit ONLY for this file
```

**Same pattern for:**
- VisitCXXRecordDecl (structs)
- VisitTypedefDecl
- VisitFunctionDecl (global functions)

**Methods are NOT deduplicated** (each class has unique methods)

## Implementation Plan

### Phase 1: Add Tracking Infrastructure (Parallel Tasks)

**Task 1.1: Extend TargetContext**
- Add `std::map<const Decl*, std::string> nodeToLocation`
- Add `std::map<std::string, EnumDecl*> globalEnums`
- Add `std::map<std::string, RecordDecl*> globalStructs`
- Add methods: `recordNode()`, `findEnum()`, `findStruct()`, `getLocation()`

**Task 1.2: Extend PathMapper**
- Add `setNodeLocation(const Decl*, std::string path)`
- Add `getNodeLocation(const Decl*) -> std::string`
- Add `getAllNodesForFile(std::string path) -> vector<const Decl*>`

**Task 1.3: Create DependencyTracker**
- New class to track which nodes depend on which other nodes
- `addDependency(const Decl* node, const Decl* dependency)`
- `getDependenciesForFile(std::string path) -> set<std::string>` (returns needed .h files)

### Phase 2: Update Visitor Logic (Sequential, depends on Phase 1)

**Task 2.1: Update VisitEnumDecl**
- Check `targetCtx.findEnum(enumName)` before creating
- If exists: reuse, don't add to C_TU
- If new: create, record in globalEnums, record location, add to C_TU

**Task 2.2: Update VisitCXXRecordDecl**
- Check `targetCtx.findStruct(structName)` before creating
- If exists: reuse, don't add to C_TU
- If new: create, record in globalStructs, record location, add to C_TU

**Task 2.3: Update VisitCXXMethodDecl**
- Record method location with PathMapper
- Ensure declaration added to appropriate C_TU
- Verify extern linkage set (already fixed)

**Task 2.4: Update VisitTypedefDecl**
- Add deduplication for typedefs
- Record location for each typedef

### Phase 3: Update Code Generation (Sequential, depends on Phase 2)

**Task 3.1: Modify CodeGenerator Header Emission**
- Group nodes by output file using PathMapper
- For each .h file:
  - Emit standard includes
  - Compute dependencies using DependencyTracker
  - Emit `#include` directives for dependencies
  - Emit declarations only (enums, structs, typedefs, function prototypes)

**Task 3.2: Modify CodeGenerator Implementation Emission**
- For each .c file:
  - Emit `#include "corresponding.h"`
  - Emit function implementations
  - Emit static variables

**Task 3.3: Update Include Generation Logic**
- Replace current hardcoded include logic in CppToCConsumer
- Use DependencyTracker to compute required includes
- Emit only necessary includes (no duplicates)

### Phase 4: Testing & Validation (Parallel within, Sequential after Phase 3)

**Task 4.1: Test State Machine (2/5)**
- Verify GameState enum in exactly ONE header file
- Verify transition() method declared in StateMachine.h
- Verify transition() method implemented in StateMachine.c
- Verify main.c compiles without errors
- Verify test passes

**Task 4.2: Test Simple Parser (3/5)**
- Verify Token enum/struct in exactly ONE header file
- Verify all parser methods declared in appropriate headers
- Verify compilation and test pass

**Task 4.3: Test Custom Container (4/5)**
- Address template-related issues
- Verify no duplicate container definitions
- Verify compilation and test pass

**Task 4.4: Test Game Logic (5/5)**
- Fix const reference issues
- Verify no duplicate definitions
- Verify compilation and test pass

**Task 4.5: Run Full Validation Suite**
- Execute validate-all.sh
- Verify 5/5 (100%) pass rate
- Verify zero compilation errors across all tests

### Phase 5: Cleanup & Commit

**Task 5.1: Remove Obsolete Code**
- Remove old enum filtering logic from CppToCVisitor (line 216)
- Remove FileOriginFilter checks that are now redundant
- Clean up debug logging

**Task 5.2: Git Commit**
- Commit all changes with descriptive message
- Tag: `fix-enum-duplication-node-location-tracking`

## Execution Strategy

### Ultrathink Mode
- Use extended thinking for complex architectural decisions
- Document reasoning for each design choice
- Validate assumptions before implementing

### Parallel Execution (Map-Reduce Pattern)

**Map Phase (Worker Pool):**
- Phase 1 tasks execute in parallel (3 workers)
- Phase 4 tests execute in parallel (5 workers)

**Reduce Phase:**
- Collect results from all workers
- Aggregate findings
- Report consolidated status

**Sequential Dependencies:**
- Phase 2 waits for Phase 1 complete
- Phase 3 waits for Phase 2 complete
- Phase 4 waits for Phase 3 complete
- Phase 5 waits for Phase 4 complete

### TodoWrite Integration

**REQUIRED: Use TodoWrite tool extensively**

1. **Initial Planning**: Break down each phase into granular tasks
2. **Progress Tracking**: Mark tasks in_progress/completed as work proceeds
3. **Status Visibility**: User can see exactly what's being done
4. **Nothing Lost**: All subtasks tracked, no work forgotten

Example todo structure:
```json
[
  {"content": "Add nodeToLocation map to TargetContext", "status": "completed", "activeForm": "Added tracking map"},
  {"content": "Implement findEnum() method", "status": "in_progress", "activeForm": "Creating lookup logic"},
  {"content": "Update VisitEnumDecl with deduplication", "status": "pending", "activeForm": "Will check existing enums"}
]
```

### Subtask Execution

**Use Task tool with subagent_type="general-purpose" for:**
- Each Phase 1 task (parallel)
- Each Phase 4 test (parallel)
- Complex refactoring tasks

**Execute directly for:**
- Simple edits (single-file changes)
- Sequential logic updates
- Code cleanup

## Output Specification

### Files Modified

**Header Files:**
- `include/TargetContext.h` - Add tracking maps and methods
- `include/PathMapper.h` - Add node location methods
- `include/DependencyTracker.h` - New file for dependency tracking

**Implementation Files:**
- `src/TargetContext.cpp` - Implement tracking methods
- `src/PathMapper.cpp` - Implement location tracking
- `src/DependencyTracker.cpp` - New file
- `src/CppToCVisitor.cpp` - Update all Visit methods
- `src/CodeGenerator.cpp` - Update emission logic
- `src/CppToCConsumer.cpp` - Update include generation

### Validation Checkpoints

After each phase:
1. Code compiles without errors
2. Existing tests still pass (no regression)
3. TodoWrite updated with phase completion
4. Progress report generated

After Phase 4:
1. All 5 validation tests pass (100%)
2. Zero compilation errors in transpiled code
3. Zero redefinition errors
4. All method declarations present in headers

### Success Metrics

- **Enum deduplication**: 0 duplicate enum definitions
- **Struct deduplication**: 0 duplicate struct definitions
- **Method declarations**: 100% of methods have headers
- **Test pass rate**: 100% (5/5 tests passing)
- **Compilation**: All transpiled C code compiles cleanly
- **Include correctness**: All #includes necessary and sufficient

## Error Handling

### Common Issues & Solutions

**Issue: Enum already exists error**
- Check globalEnums map before creating
- Reuse existing node instead of creating new

**Issue: Method still missing from header**
- Verify nodeToLocation recorded for method
- Check CodeGenerator emits declarations to .h
- Verify C_TU contains method FunctionDecl

**Issue: Circular include dependencies**
- Use forward declarations in headers where possible
- DependencyTracker should detect and warn
- Restructure if necessary

**Issue: Test still failing**
- Read compilation errors carefully
- Check transpiled .h and .c files
- Verify all needed includes present
- Use gcc -E to check preprocessor output

### Recovery Strategy

If any phase fails:
1. Stop execution
2. Report detailed error with file/line
3. Offer recovery options:
   - Retry the phase
   - Skip and continue (for non-critical)
   - Stop and investigate
4. Do NOT proceed to dependent phases if critical phase fails

## Quality Assurance

### Pre-Commit Checklist

- [ ] All TODOs resolved or tracked
- [ ] No hardcoded paths or magic numbers
- [ ] All new functions have assertions for null checks
- [ ] Debug logging added for key operations
- [ ] Memory managed correctly (no leaks)
- [ ] Error messages are actionable
- [ ] Code follows existing style and conventions
- [ ] Comments explain WHY, not just WHAT

### Testing Protocol

1. **Unit validation**: Each phase tested independently
2. **Integration testing**: Full validation suite after Phase 3
3. **Regression testing**: Ensure Math Library still passes
4. **Compilation testing**: All transpiled code must compile
5. **Runtime testing**: All 5 validation tests must pass

## Output Location

Save implementation notes and decisions to:
`.prompts/001-c-ast-location-do/implementation-notes.md`

Save SUMMARY.md to:
`.prompts/001-c-ast-location-do/SUMMARY.md`

## SUMMARY.md Requirements

Create `SUMMARY.md` with:

```markdown
# C AST Node Location Tracking Implementation

**One-liner**: [Substantive description of outcome - NOT generic]

## Version
v1 - Initial implementation

## Key Findings
- [Specific findings from implementation]
- [Challenges encountered and solutions]
- [Performance impact if any]

## Files Modified
- include/TargetContext.h - [What changed]
- src/CppToCVisitor.cpp - [What changed]
- [... all modified files with brief description]

## Decisions Made
- [Architectural decisions with rationale]
- [Trade-offs considered]

## Blockers Encountered
- [Any external impediments]
- [Dependencies that blocked progress]

## Test Results
- Math Library (1/5): PASS
- State Machine (2/5): PASS/FAIL - [details]
- Simple Parser (3/5): PASS/FAIL - [details]
- Custom Container (4/5): PASS/FAIL - [details]
- Game Logic (5/5): PASS/FAIL - [details]
- **Final: X/5 (XX%)**

## Next Step
[Concrete forward action - what to do next]
```

## Metadata Requirements

This is a DO prompt, so metadata should track implementation status:

```xml
<implementation_status>
  <phase name="tracking-infrastructure" status="completed|in_progress|pending" />
  <phase name="visitor-logic" status="completed|in_progress|pending" />
  <phase name="code-generation" status="completed|in_progress|pending" />
  <phase name="testing" status="completed|in_progress|pending" />
  <phase name="cleanup" status="completed|in_progress|pending" />
</implementation_status>

<test_results>
  <test name="math-library" status="pass|fail" />
  <test name="state-machine" status="pass|fail" />
  <test name="simple-parser" status="pass|fail" />
  <test name="custom-container" status="pass|fail" />
  <test name="game-logic" status="pass|fail" />
  <pass_rate>X/5</pass_rate>
</test_results>

<blockers>
  [List any blockers encountered]
</blockers>

<decisions>
  [Key architectural decisions made during implementation]
</decisions>
```

## Success Criteria

Implementation is complete when:

1. ✅ All 5 phases executed successfully
2. ✅ TodoWrite shows all tasks completed
3. ✅ All modified files compile without errors
4. ✅ Full validation suite passes at 100% (5/5)
5. ✅ Zero duplicate declarations in transpiled output
6. ✅ All method declarations present in appropriate headers
7. ✅ SUMMARY.md created with all required sections
8. ✅ implementation-notes.md documents key decisions
9. ✅ Git commit created with all changes
10. ✅ No regression in previously passing tests

**DO NOT mark as complete if any test fails or compilation errors exist!**
