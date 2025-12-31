# Prompt: Function Overloading Support Implementation Plan

## Objective

Design a comprehensive implementation plan for adding robust function overloading support to the C++ to C transpiler. The implementation must work within the existing handler/dispatcher framework and enhance the current name mangling system to support cross-file overload resolution.

**Why it matters:**
- Function overloading is a core C++ feature used extensively in real-world codebases
- Current implementation has limitations: per-file overload tracking, no systematic overload set management
- Proper support enables transpilation of complex C++ projects with heavy use of overloading

## Context

### Existing Implementation

**Name Mangling** (`include/NameMangler.h`, `src/NameMangler.cpp`):
- **Methods**: `ClassName_methodName_paramTypes` (always includes params for cross-file consistency)
- **Constructors**: `ClassName__ctor[_paramCount]`
- **Standalone Functions**: First occurrence uses simple name, overloads append param types
- **Type Encoding**: Primitives, pointers, references, const qualification, record types
- **Namespace Support**: Full qualified names (`ns1_ns2_ClassName`)
- **Limitations**: Per-file `usedNames` set, no cross-file tracking, no overload set API

**Handler/Dispatcher Framework** (`include/dispatch/`, `src/dispatch/`):
- **Pattern**: Chain of Responsibility with predicate-based routing
- **Key Handlers**: FunctionHandler, StaticMethodHandler, InstanceMethodHandler, VirtualMethodHandler
- **Mappers**: DeclMapper, TypeMapper, ExprMapper, StmtMapper for translation storage
- **Path Tracking**: PathMapper for multi-file support
- **Design**: SOLID principles, exact type matching (not isa<>), recursive dispatch

### Current Gaps

1. **No Cross-File Overload Tracking**: Each file starts fresh with `usedNames`
2. **No Overload Set Management**: Can't query "all overloads of function foo"
3. **No Call Site Validation**: Assumes Clang resolved calls correctly
4. **Limited Diagnostics**: No warnings for ambiguous overloads
5. **Handler Pattern Split**: Legacy handlers/ vs modern dispatch/ frameworks

### Project Principles

- **SOLID**: Single Responsibility, Open/Closed, Liskov Substitution, Interface Segregation, Dependency Inversion
- **KISS**: Keep It Simple - prefer simple solutions over complex ones
- **DRY**: Don't Repeat Yourself - extract common functionality
- **YAGNI**: You Aren't Gonna Need It - don't build features until needed
- **TDD**: Write failing test first, implement to pass, refactor

## Requirements

### Functional Requirements

1. **Overload Set Tracking**
   - Track all overloads of each function/method globally across all files
   - Provide API to query overload sets
   - Support namespace-qualified lookups
   - Handle template specializations (if applicable)

2. **Name Mangling Enhancement**
   - Ensure consistent mangling across translation units
   - Support function pointer types in parameters
   - Handle variadic functions
   - Maintain backward compatibility with existing mangled names

3. **Handler Integration**
   - Create handlers within existing dispatcher framework
   - Follow established handler patterns (predicate + visitor)
   - Use existing mappers (DeclMapper, TypeMapper, etc.)
   - Support recursive dispatch for child nodes

4. **Call Site Validation**
   - Verify mangled names match call site signatures
   - Provide diagnostics for unresolved overloads
   - Handle function pointers and indirect calls

5. **Testing**
   - Unit tests for each new handler
   - Integration tests for multi-file overloading
   - Test overload resolution across translation units
   - Verify call site translation matches declaration mangling

### Non-Functional Requirements

1. **Performance**: Minimal overhead for non-overloaded functions
2. **Maintainability**: Follow existing code patterns and style
3. **Documentation**: Clear comments, architecture notes
4. **Backward Compatibility**: Don't break existing tests

## Output Specification

**Output Location**: `.prompts/054-function-overloading-plan/function-overloading-plan.md`

**Plan Structure**:

```markdown
# Function Overloading Support Implementation Plan

## 1. Architecture Overview

### 1.1 High-Level Design
- System components diagram
- Data flow between components
- Integration points with existing code

### 1.2 Key Design Decisions
- Overload set storage strategy (global registry vs distributed)
- Name mangling algorithm enhancements
- Handler responsibilities and boundaries

### 1.3 Dependencies
- Existing classes/files that will be modified
- New classes/files to be created
- External dependencies (if any)

## 2. Component Design

### 2.1 OverloadSetTracker (NEW)
**Purpose**: Global tracking of function overload sets
**Location**: `include/OverloadSetTracker.h`, `src/OverloadSetTracker.cpp`
**Responsibilities**:
- Store all overloads for each function/method
- Provide query API for overload sets
- Support namespace-qualified lookups
**Interface**:
```cpp
class OverloadSetTracker {
public:
    void registerOverload(const FunctionDecl* FD, const std::string& mangledName);
    std::vector<std::string> getOverloads(const std::string& baseName) const;
    std::string selectOverload(const CallExpr* CE) const;
    // ... additional methods
};
```

### 2.2 NameMangler Enhancements
**Location**: `include/NameMangler.h`, `src/NameMangler.cpp`
**Changes**:
- Integrate with OverloadSetTracker
- Add `mangleFunctionSignature()` for signature-only encoding
- Enhance `getSimpleTypeName()` for function pointer types
- Add variadic function support
**Backward Compatibility**: Ensure existing tests still pass

### 2.3 FunctionOverloadHandler (NEW or enhance existing FunctionHandler)
**Purpose**: Handle function overload translation
**Location**: `include/dispatch/FunctionOverloadHandler.h`, `src/dispatch/FunctionOverloadHandler.cpp`
**Pattern**: Standard handler pattern (predicate + visitor)
**Predicate**: `canHandle(const Decl* D)` - matches FunctionDecl but not CXXMethodDecl
**Visitor**: `handleFunction(disp, cppCtx, cCtx, FD)`
**Responsibilities**:
- Register overload with OverloadSetTracker
- Delegate to NameMangler for consistent naming
- Store mapping in DeclMapper

### 2.4 CallExprHandler (NEW or enhance existing)
**Purpose**: Validate and translate call expressions
**Location**: `include/dispatch/CallExprHandler.h`, `src/dispatch/CallExprHandler.cpp`
**Responsibilities**:
- Map CallExpr::getDirectCallee() to mangled C function name
- Validate resolved overload matches declaration
- Provide diagnostics for unresolved calls

## 3. Implementation Phases

### Phase 1: Foundation (Week 1)
**Deliverables**:
- [ ] OverloadSetTracker class implementation
- [ ] Unit tests for OverloadSetTracker
- [ ] NameMangler integration (registry hooks)

**Files**:
- `include/OverloadSetTracker.h` (NEW)
- `src/OverloadSetTracker.cpp` (NEW)
- `tests/OverloadSetTrackerTest.cpp` (NEW)
- `include/NameMangler.h` (MODIFY)
- `src/NameMangler.cpp` (MODIFY)

**Success Criteria**:
- All new unit tests pass
- Existing NameMangler tests still pass
- Can register and query overload sets

### Phase 2: Handler Implementation (Week 2)
**Deliverables**:
- [ ] FunctionOverloadHandler implementation
- [ ] Integration with dispatcher
- [ ] Unit tests for handler dispatch

**Files**:
- `include/dispatch/FunctionOverloadHandler.h` (NEW or MODIFY FunctionHandler)
- `src/dispatch/FunctionOverloadHandler.cpp` (NEW or MODIFY)
- `tests/unit/dispatch/FunctionOverloadHandlerDispatcherTest.cpp` (NEW)

**Success Criteria**:
- Handler registered and dispatching correctly
- Overloads detected and tracked
- Names mangled consistently

### Phase 3: Call Site Validation (Week 3)
**Deliverables**:
- [ ] CallExprHandler implementation
- [ ] Validation logic for call site matching
- [ ] Diagnostic messages for errors

**Files**:
- `include/dispatch/CallExprHandler.h` (NEW or enhance existing)
- `src/dispatch/CallExprHandler.cpp` (NEW or enhance)
- `tests/unit/dispatch/CallExprHandlerDispatcherTest.cpp` (NEW or enhance)

**Success Criteria**:
- Call expressions translated correctly
- Overload resolution validated
- Diagnostics emitted for unresolved calls

### Phase 4: Integration Testing (Week 4)
**Deliverables**:
- [ ] Multi-file overload integration tests
- [ ] Cross-TU overload resolution tests
- [ ] Namespace-qualified overload tests
- [ ] Function pointer parameter tests

**Files**:
- `tests/integration/FunctionOverloadIntegrationTest.cpp` (NEW)
- Test fixtures in `tests/fixtures/overloading/` (NEW)

**Success Criteria**:
- All integration tests pass
- No regressions in existing tests
- Coverage for edge cases

## 4. Testing Strategy

### 4.1 Unit Tests
- OverloadSetTracker: Registration, queries, edge cases
- NameMangler: Signature encoding, parameter types, namespaces
- Handlers: Predicate matching, translation correctness

### 4.2 Integration Tests
- Multi-file projects with shared overloads
- Cross-TU call site resolution
- Namespace-qualified function calls
- Function pointers with overloaded functions

### 4.3 Edge Cases
- Variadic functions
- Function templates (if supported)
- Overloads differing only in const-qualification
- Overloads with default arguments

### 4.4 Regression Tests
- Ensure existing tests still pass
- No changes to non-overloaded function translation
- Backward compatibility with existing mangled names

## 5. Files to Create/Modify

### New Files
- `include/OverloadSetTracker.h`
- `src/OverloadSetTracker.cpp`
- `tests/OverloadSetTrackerTest.cpp`
- `include/dispatch/FunctionOverloadHandler.h` (if new)
- `src/dispatch/FunctionOverloadHandler.cpp` (if new)
- `tests/unit/dispatch/FunctionOverloadHandlerDispatcherTest.cpp`
- `include/dispatch/CallExprHandler.h` (if new)
- `src/dispatch/CallExprHandler.cpp` (if new)
- `tests/unit/dispatch/CallExprHandlerDispatcherTest.cpp` (if new)
- `tests/integration/FunctionOverloadIntegrationTest.cpp`

### Modified Files
- `include/NameMangler.h` (integrate tracker)
- `src/NameMangler.cpp` (integrate tracker)
- `tests/NameManglerTest.cpp` (add new test cases)
- `CMakeLists.txt` (add new test targets)
- Potentially: `include/dispatch/FunctionHandler.h` (if enhancing existing)
- Potentially: `src/dispatch/FunctionHandler.cpp` (if enhancing existing)

## 6. Alternative Approaches Considered

### Approach A: Global Overload Registry (RECOMMENDED)
**Pros**:
- Centralized management
- Easy cross-file lookups
- Clear ownership of overload sets

**Cons**:
- Additional global state
- Need to ensure thread-safety (if parallelizing in future)

### Approach B: Distributed Per-File Tracking
**Pros**:
- Simpler implementation
- No global state

**Cons**:
- Cross-file consistency issues
- Complex merge logic needed
- Same problems as current implementation

### Approach C: AST Annotation
**Pros**:
- Leverages existing Clang infrastructure
- No separate data structure

**Cons**:
- Harder to query
- Couples translation to AST traversal order
- Less flexible

**Decision**: Choose Approach A (Global Registry) for clarity and maintainability.

## 7. Critical Success Factors

1. **Handler Pattern Compliance**
   - Follow exact type matching (getKind(), not isa<>)
   - Use static methods for predicate/visitor
   - Delegate child translation via dispatcher

2. **Name Mangling Consistency**
   - Same signature always produces same mangled name
   - Cross-file consistency guaranteed
   - Backward compatibility maintained

3. **Test Coverage**
   - 100% handler code coverage
   - Integration tests for all edge cases
   - No regressions in existing tests

4. **Documentation**
   - Clear architecture notes
   - Handler interface documented
   - Example usage in tests

## 8. Risks and Mitigations

### Risk 1: Breaking Existing Tests
**Mitigation**: Run full test suite after each phase, fix regressions immediately

### Risk 2: Complex Edge Cases
**Mitigation**: Start with simple overloads, incrementally add complexity

### Risk 3: Performance Overhead
**Mitigation**: Profile before/after, optimize hot paths

### Risk 4: Name Mangling Collisions
**Mitigation**: Use comprehensive type encoding, add numeric suffixes if needed

## 9. Verification Criteria

### Must Pass
- [ ] All existing tests still pass (no regressions)
- [ ] All new unit tests pass
- [ ] All integration tests pass
- [ ] Name mangling is consistent across files
- [ ] Call sites resolve to correct overloads

### Should Pass
- [ ] Performance within 10% of baseline
- [ ] Code coverage >90% for new code
- [ ] No compiler warnings

### Nice to Have
- [ ] Architecture documentation updated
- [ ] Examples in documentation
- [ ] Benchmarks for overload-heavy code
```

**Metadata Requirements**:

Add the following metadata at the end of the plan:

```xml
<metadata>
<confidence>HIGH</confidence>
<dependencies>
  <dependency>NameMangler class must remain stable</dependency>
  <dependency>Handler/dispatcher framework API stable</dependency>
  <dependency>Clang AST provides overload resolution info</dependency>
</dependencies>
<open_questions>
  <question>Should we support template function overloading in this phase?</question>
  <question>How to handle overloads across dynamically loaded modules?</question>
  <question>Should we emit warnings for potential ABI issues?</question>
</open_questions>
<assumptions>
  <assumption>Clang has already resolved C++ overloads in AST</assumption>
  <assumption>Single-threaded transpilation (no parallel file processing)</assumption>
  <assumption>Target C compiler supports long identifiers (mangled names)</assumption>
</assumptions>
</metadata>
```

## Success Criteria

**Plan Creation:**
- Plan file created at specified location
- All sections filled with concrete details
- Phases have clear deliverables and success criteria
- Files to create/modify are listed
- Alternative approaches evaluated
- Metadata included (confidence, dependencies, questions, assumptions)

**Plan Quality:**
- Follows existing handler/dispatcher patterns
- Integrates with NameMangler appropriately
- Addresses cross-file consistency
- Includes comprehensive testing strategy
- Identifies risks and mitigations
- Provides clear verification criteria

**Plan Completeness:**
- Architecture overview with diagrams (Mermaid or ASCII)
- Component design with interfaces
- Implementation phases with timelines
- Testing strategy covering unit/integration/edge cases
- Files to create/modify enumerated
- Alternative approaches considered
