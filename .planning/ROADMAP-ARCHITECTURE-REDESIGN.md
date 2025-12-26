# Roadmap: C++ to C Transpiler Architecture Redesign

**Project**: Ground-up redesign with Chain of Responsibilities pattern
**Brief**: `.planning/BRIEF-ARCHITECTURE-REDESIGN.md`
**Created**: 2025-12-25
**Status**: ACTIVE

## Overview

Four phases to build proper architectural foundation:

1. **Research** - Understand Clang C++ AST nodes
2. **Architecture** - Design handler chain with diagrams
3. **Planning** - Create implementation roadmap (simple → complex)
4. **Foundation** - Implement & test basic handlers (functions, variables, expressions)

## Principles

- **TDD mandatory**: Tests before implementation
- **Surgical precision**: Unit test each handler independently
- **Progressive complexity**: Simple features first, build up gradually
- **SOLID compliance**: Each handler has single responsibility
- **Documentation first**: Architecture documented before coding

---

# Phase 36: C++ AST Research

**Goal**: Catalog all C++ AST nodes in Clang, understand hierarchy and relationships

## Deliverables

1. **AST Node Catalog** (`docs/architecture/clang-ast-catalog.md`):
   - Complete list of C++ AST node types
   - Node hierarchy (inheritance relationships)
   - Which nodes are needed for basic features (functions, variables, expressions)
   - Which nodes are needed for advanced features (classes, templates, etc.)

2. **AST Node Examples** (`docs/architecture/ast-examples/`):
   - Small C++ code samples
   - Their corresponding AST dumps
   - Annotations explaining each node

3. **Feature-to-Node Mapping** (`docs/architecture/feature-node-mapping.md`):
   - Map C++ features to required AST nodes
   - Complexity ranking (simple → complex)
   - Dependencies between features

## Tasks

### 36-01: Catalog Basic AST Nodes
- Research Clang AST documentation
- Create catalog of nodes for:
  - Functions: `FunctionDecl`, `ParmVarDecl`, `CompoundStmt`
  - Variables: `VarDecl`, `DeclRefExpr`
  - Expressions: `BinaryOperator`, `UnaryOperator`, `IntegerLiteral`, `CallExpr`
  - Flow control: `IfStmt`, `WhileStmt`, `ForStmt`, `SwitchStmt`, `ReturnStmt`
- Document node hierarchy and relationships

### 36-02: Catalog Class/Struct AST Nodes
- Research nodes for structs and classes:
  - `RecordDecl`, `CXXRecordDecl`
  - `FieldDecl`
  - `CXXMethodDecl`, `CXXConstructorDecl`, `CXXDestructorDecl`
  - `MemberExpr`, `CXXMemberCallExpr`
- Document differences between C structs and C++ classes

### 36-03: Catalog Advanced AST Nodes
- Research nodes for advanced features:
  - Templates: `ClassTemplateDecl`, `FunctionTemplateDecl`, `TemplateSpecializationType`
  - Inheritance: `CXXBaseSpecifier`, `CXXThisExpr`
  - Enums: `EnumDecl`, `EnumConstantDecl`
  - Type system: `QualType`, `BuiltinType`, `PointerType`, `ReferenceType`

### 36-04: Create AST Examples
- Write small C++ samples for each category
- Generate AST dumps using `clang -Xclang -ast-dump`
- Annotate dumps to explain structure

### 36-05: Create Feature Mapping
- Map C++ features to AST nodes
- Rank by complexity (1-5 scale)
- Identify dependencies (feature X requires feature Y)
- Create progressive implementation order

## Verification

- [ ] All major AST node types cataloged
- [ ] Examples compile and produce correct AST dumps
- [ ] Feature mapping shows clear progression path
- [ ] Documentation reviewed for completeness

## Dependencies

None (starting from scratch)

---

# Phase 37: Handler Chain Architecture Design

**Goal**: Design Chain of Responsibilities pattern for C++ AST → C AST translation

## Deliverables

1. **Architecture Overview** (`docs/architecture/handler-chain-design.md`):
   - System architecture diagram (Mermaid)
   - 3-stage pipeline explanation
   - Handler chain pattern explanation
   - Interface definitions

2. **Handler Specifications** (`docs/architecture/handlers/`):
   - One document per handler type
   - Responsibility definition
   - Input/output specifications
   - C++ AST nodes it processes
   - C AST nodes it produces
   - Dependencies on other handlers

3. **Handler Interfaces** (`docs/architecture/handler-interfaces.md`):
   - Base handler interface
   - Handler context (shared state)
   - Registration and dispatch mechanism
   - Error handling strategy

4. **Test Strategy** (`docs/architecture/test-strategy.md`):
   - How to unit test individual handlers
   - How to test handler chain integration
   - Mock strategy for C AST verification
   - Test fixtures and utilities

## Tasks

### 37-01: Design Pipeline Architecture
- Document 3-stage pipeline:
  - Stage 1: Clang → C++ AST (existing)
  - Stage 2: Handler chain → C AST (new)
  - Stage 3: Code generator → C files (simplified)
- Create Mermaid diagram showing data flow
- Define stage boundaries and interfaces

### 37-02: Design Handler Chain Pattern
- Define base `ASTHandler` interface
- Design `HandlerContext` (shared state, symbol tables, type info)
- Design handler registration and dispatch
- Create Mermaid sequence diagram showing handler invocation

### 37-03: Design Basic Handlers
- **FunctionHandler**: `FunctionDecl` → C function
- **VariableHandler**: `VarDecl` → C variable
- **ExpressionHandler**: Expression nodes → C expressions
- **StatementHandler**: Statement nodes → C statements
- Document each handler's responsibility and interface

### 37-04: Design Class/Struct Handlers
- **RecordHandler**: `CXXRecordDecl` → C struct
- **MethodHandler**: `CXXMethodDecl` → C function with `this`
- **ConstructorHandler**: `CXXConstructorDecl` → init function
- **MemberAccessHandler**: `MemberExpr` → field access or function call

### 37-05: Design Advanced Handlers
- **EnumHandler**: Scoped enums → prefixed constants
- **TemplateHandler**: Template instantiation → concrete types
- **InheritanceHandler**: Base classes → struct composition
- Document complexity and dependencies

### 37-06: Design Test Strategy
- How to create isolated handler tests
- How to mock C AST creation
- How to verify transformations without code emission
- Test fixture design for common scenarios

### 37-07: Create Architecture Documentation
- Consolidate all designs into coherent documentation
- Add Mermaid diagrams:
  - System architecture
  - Handler chain flow
  - Handler sequence diagrams
  - Class diagram showing handler relationships
- Review for completeness and clarity

## Verification

- [ ] Architecture documents are clear and complete
- [ ] Mermaid diagrams accurately represent design
- [ ] Handler responsibilities have no overlap (SRP)
- [ ] Handler interfaces are minimal and focused (ISP)
- [ ] Test strategy allows unit testing of handlers
- [ ] Design reviewed for SOLID compliance

## Dependencies

- Phase 36 complete (AST research informs handler design)

---

# Phase 38: Implementation Roadmap

**Goal**: Create detailed step-by-step plan to implement handlers (simple → complex)

## Deliverables

1. **Implementation Phases** (`docs/architecture/implementation-phases.md`):
   - Break implementation into 10-15 phases
   - Each phase adds one category of functionality
   - Clear progression from simple to complex
   - Estimated complexity for each phase

2. **Handler Implementation Order** (`docs/architecture/implementation-order.md`):
   - Exact order to implement handlers
   - Dependencies between handlers
   - Which handlers can be done in parallel
   - Verification criteria for each

3. **Test Plan** (`docs/architecture/test-plan.md`):
   - Test cases for each handler
   - Integration test scenarios
   - Progressive validation (each phase builds on previous)

## Tasks

### 38-01: Define Phase 1 - Basic Functions
- Standalone functions (no classes)
- Function parameters and return values
- Local variables
- Arithmetic expressions (+, -, *, /, %)
- Function calls
- Return statements
**Handlers**: FunctionHandler, VariableHandler (local), ExpressionHandler (arithmetic), StatementHandler (return)

### 38-02: Define Phase 2 - Flow Control
- If/else statements
- While loops
- For loops
- Switch/case statements
- Break/continue
**Handlers**: StatementHandler (control flow), ExpressionHandler (comparisons, logical ops)

### 38-03: Define Phase 3 - Global Variables & Types
- Global variables
- Typedefs
- Basic type conversions (casts)
**Handlers**: VariableHandler (global), TypeHandler

### 38-04: Define Phase 4 - Structs (C-style)
- Struct declarations (no methods)
- Struct field access
- Struct initialization
- Passing structs to functions
**Handlers**: RecordHandler (basic), MemberAccessHandler (field-only)

### 38-05: Define Phase 5 - Pointers & References
- Pointer types
- Address-of and dereference operators
- Pointer arithmetic
- C++ references → C pointers
**Handlers**: ExpressionHandler (pointer ops), TypeHandler (pointer types)

### 38-06: Define Phase 6 - Classes (Simple)
- Class declarations → structs
- Member functions → functions with `this` parameter
- Constructor → init function
- Destructor → cleanup function
**Handlers**: RecordHandler (with methods), MethodHandler, ConstructorHandler, DestructorHandler

### 38-07: Define Phase 7 - Method Calls
- Member function calls → function calls with `this`
- Method overloading → name mangling
**Handlers**: MemberAccessHandler (method calls), MethodHandler (overload resolution)

### 38-08: Define Phase 8 - Enums
- Unscoped enums → C enums
- Scoped enums → prefixed constants
- Enum constant references
**Handlers**: EnumHandler

### 38-09: Define Phase 9 - Inheritance (Single)
- Single inheritance → struct composition
- Base class field access
- Virtual methods → function pointers (basic)
**Handlers**: InheritanceHandler

### 38-10: Define Phase 10 - Templates (Monomorphization)
- Class templates → concrete structs
- Function templates → concrete functions
- Template parameter handling
**Handlers**: TemplateHandler

### 38-11: Create Test Plan
- For each implementation phase, define:
  - Unit tests for new handlers
  - Integration tests for complete features
  - Validation criteria (transpiled C code compiles and runs correctly)
- Progressive test suite that grows with each phase

### 38-12: Create Implementation Timeline
- Consolidate phases into roadmap
- Identify parallelization opportunities
- Define verification gates between phases

## Verification

- [ ] Implementation phases progress from simple to complex
- [ ] Each phase is independently testable
- [ ] Dependencies between phases are clear
- [ ] Test plan covers all functionality
- [ ] Roadmap is achievable with TDD approach

## Dependencies

- Phase 37 complete (architecture design informs implementation plan)

---

# Phase 39: Foundation Implementation (Phases 1-3)

**Goal**: Implement and test basic handlers for functions, variables, expressions, and flow control

## Scope

Implement implementation phases 1-3 from Phase 38:
- Phase 1: Basic functions, arithmetic, local variables
- Phase 2: Flow control (if/while/for/switch)
- Phase 3: Global variables and types

## Deliverables

1. **Handler Implementations**:
   - `include/handlers/FunctionHandler.h` + `src/handlers/FunctionHandler.cpp`
   - `include/handlers/VariableHandler.h` + `src/handlers/VariableHandler.cpp`
   - `include/handlers/ExpressionHandler.h` + `src/handlers/ExpressionHandler.cpp`
   - `include/handlers/StatementHandler.h` + `src/handlers/StatementHandler.cpp`
   - `include/handlers/TypeHandler.h` + `src/handlers/TypeHandler.cpp`

2. **Handler Infrastructure**:
   - `include/handlers/ASTHandler.h` - Base interface
   - `include/handlers/HandlerContext.h` - Shared state
   - `include/handlers/HandlerRegistry.h` - Registration/dispatch

3. **Unit Tests**:
   - `tests/unit/handlers/FunctionHandlerTest.cpp`
   - `tests/unit/handlers/VariableHandlerTest.cpp`
   - `tests/unit/handlers/ExpressionHandlerTest.cpp`
   - `tests/unit/handlers/StatementHandlerTest.cpp`
   - `tests/unit/handlers/TypeHandlerTest.cpp`

4. **Integration Tests**:
   - `tests/integration/phase1_basic_functions/` - 10+ test cases
   - `tests/integration/phase2_flow_control/` - 10+ test cases
   - `tests/integration/phase3_global_vars/` - 5+ test cases

## Tasks

This phase will be further broken down into atomic plans (39-01, 39-02, etc.) following TDD:
1. Write unit test for handler
2. Implement handler to pass test
3. Write integration test for feature
4. Verify transpiled C code compiles and runs
5. Refactor while keeping tests green
6. Review and commit

## Verification

- [ ] All unit tests pass (100%)
- [ ] All integration tests pass (100%)
- [ ] Transpiled C code compiles without errors
- [ ] Transpiled C code produces same output as original C++
- [ ] Code review by separate agent
- [ ] All linters pass (zero warnings)

## Dependencies

- Phase 38 complete (implementation plan ready)

---

# Status Summary

| Phase | Status | Description |
|-------|--------|-------------|
| 36 | ⏳ NEXT | C++ AST Research |
| 37 | ⏳ PLANNED | Handler Chain Architecture Design |
| 38 | ⏳ PLANNED | Implementation Roadmap |
| 39 | ⏳ PLANNED | Foundation Implementation (Phases 1-3) |

---

# Next Steps

1. Execute Phase 36 (C++ AST Research)
2. Document all findings
3. Move to Phase 37 (Architecture Design)
