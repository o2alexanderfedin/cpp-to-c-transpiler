# Architecture Documentation

This directory contains the architecture decision rationale and design specifications for the C++ to C transpiler.

## Architecture Documents

### [architecture-decision.md](architecture-decision.md) - Architecture Rationale (949 lines)

**v1.5 + v1.5.1 Addendum** - Complete architecture decision process

**v1.5 Decision: Direct C Generation (NOT TreeTransform)**
- Why TreeTransform was rejected
- Direct AST → C text emission approach
- Evaluated approaches comparison
- Confidence: 95%

**v1.5.1 Refinement: Intermediate C AST**
- Trigger: Frama-C code quality priority
- Two-Phase Translation approach
- CNodeBuilder helper library design
- Clang DeclPrinter/StmtPrinter integration
- Runtime library separation
- Confidence upgrade: 97%+

**Key Sections:**
- Architecture decision criteria
- Trade-off analysis
- Implementation approach
- Code quality vs. implementation simplicity
- Formal verification considerations

### [prototype-comparison.md](prototype-comparison.md) - Quantitative Analysis (863 lines)

**Empirical Validation** - Code quality and implementation complexity metrics

**Approach Comparison:**
- Direct text emission (v1.5)
- Intermediate C AST (v1.5.1)
- TreeTransform (rejected)

**Metrics:**
- Lines of code (implementation vs. generated)
- Code quality scores
- Frama-C tractability
- Maintenance burden
- Precedence handling

**Key Findings:**
- v1.5.1: 40% more implementation, 80% cleaner output, 10x easier verification
- v1.5: 60% less implementation, moderate quality, 5x harder verification
- TreeTransform: Highest implementation cost, poor code generation support

### [runtime-library-design.md](runtime-library-design.md) - Runtime Library Specification (713 lines)

**Runtime Library API** - Specification for exception_runtime.c, rtti_runtime.c, etc.

**Modules:**
- **exception_runtime.c** - PNaCl SJLJ implementation (400-600 LOC)
- **rtti_runtime.c** - type_info + dynamic_cast (500-800 LOC)
- **vtable_runtime.c** - Virtual function dispatch (300-500 LOC)
- **memory_runtime.c** - RAII + smart pointers (400-600 LOC)

**Total Size Estimate:** 1.7-2.8 KB compiled

**Key Sections:**
- API specifications
- Thread safety guarantees
- Memory management
- Frama-C verification strategy
- Size and performance estimates

### [01-pipeline-architecture.md](01-pipeline-architecture.md) - 3-Stage Pipeline (430 lines)

**Phase 37 Deliverable** - Complete transpiler pipeline architecture

**3-Stage Pipeline:**
1. **Stage 1**: Clang Frontend (C++ source → C++ AST)
2. **Stage 2**: Handler Chain (C++ AST → C AST) - Translation decisions
3. **Stage 3**: Code Generator (C AST → C source) - Pure emission

**Key Principles:**
- Clear separation of concerns between stages
- Each stage independently testable
- **Golden Rule**: Stage 2 decides WHAT, Stage 3 decides HOW
- Mermaid diagrams showing data flow

**References:**
- Handler chain pattern specification
- Handler specifications (9 handlers)
- Test strategy
- Code generator specification

### [02-handler-chain-pattern.md](02-handler-chain-pattern.md) - Handler Chain Architecture (1,700+ lines)

**Phase 37 Deliverable** - Chain of Responsibilities pattern for Stage 2

**Complete Architecture:**
- ASTHandler base interface
- HandlerContext (shared state, symbol tables, type mappings)
- HandlerRegistry (handler dispatch)
- TranslationOrchestrator (handler coordination)
- CNodeBuilder (C AST construction)

**Mermaid Diagrams:**
- Handler class hierarchy
- Handler sequence flow
- Symbol registration patterns

**Key Features:**
- Each handler has single responsibility (SRP)
- Handlers independently testable
- Extensible without modification (OCP)
- Symbol table and type mapping strategies

### [03-test-strategy.md](03-test-strategy.md) - TDD Strategy (566 lines)

**Phase 37 Deliverable** - Comprehensive testing strategy for handler-based architecture

**Testing Pyramid:**
- **Unit Tests** (50+ per handler): Isolated C++ AST → C AST translation
- **Handler Integration** (20-30 per phase): Multi-handler scenarios
- **E2E Integration** (5-10 per phase): C++ source → working C code

**Key Approaches:**
- Red-Green-Refactor TDD workflow
- Mock and fixture utilities
- AST matchers for verification
- 100% coverage requirement for handlers
- CI pipeline configuration

**Test Organization:**
- Unit tests verify AST structure (not text)
- Integration tests verify handler cooperation
- E2E tests verify compiled C code works

### [04-code-generator.md](04-code-generator.md) - Code Generator Specification (780 lines)

**Phase 37 Deliverable** - Complete Stage 3 specification

**C AST Visitor:**
- Pure emission component (no translation decisions)
- Walks C AST and generates formatted C text
- Separates declarations (header) from definitions (implementation)

**Key Principle:** "Just print what's in the AST - don't think"

**Complete Specification:**
- Class structure and visitor methods
- Header vs implementation split logic
- Emission examples for all C constructs
- Anti-patterns: What NOT to do
- Type emission helpers
- Indentation management
- Testing strategy for code generator

**Mermaid Diagrams:**
- Emission sequence flow

### [handlers/](handlers/) - Handler Specifications Directory

**Phase 37 Deliverable** - 9 complete handler specifications

**Basic Handlers (Phase 1-3):**
- FunctionHandler.md - Function declarations/definitions
- VariableHandler.md - Local/global variables
- ExpressionHandler.md - All expression types (recursive)
- StatementHandler.md - Control flow statements

**Class Handlers (Phase 6-7):**
- RecordHandler.md - Class → struct transformation
- MethodHandler.md - Method → function with `this` parameter
- ConstructorHandler.md - Constructor → init function
- MemberAccessHandler.md - Member access translation

**Advanced Handlers (Phase 8):**
- EnumHandler.md - Scoped enum → prefixed constants

**Each specification includes:**
- Responsibility and AST nodes processed
- Translation strategy with examples
- Algorithm and implementation details
- 5+ test cases
- 5-10 edge cases
- Integration points

## Architecture Timeline

| Version | Date | Achievement |
|---------|------|-------------|
| v1.0 | Initial | Feasibility assessment |
| v1.5 | Dec 8 | Direct C generation validated |
| v1.5.1 | Dec 8 | Intermediate C AST refinement |
| Phase 36 | Dec 25 | AST node research (47 nodes cataloged) |
| Phase 37 | Dec 25 | Handler chain architecture design |

## Key Decisions

1. **Use Clang AST infrastructure** (not custom parser)
2. **Direct C generation** (not TreeTransform)
3. **Intermediate C AST** (not direct text emission)
4. **Runtime library** (not inline runtime)
5. **Optimize for Frama-C** (not implementation simplicity)

## Architecture Diagram

```
C++ Source Code
    ↓
[Stage 1] Clang Parser + Sema
    ↓
AST #1 (Full C++ AST - READ ONLY)
    ↓
[Stage 2] Handler Chain (TranslationOrchestrator)
    ├─ FunctionHandler
    ├─ VariableHandler
    ├─ ExpressionHandler
    ├─ StatementHandler
    ├─ RecordHandler
    ├─ MethodHandler
    ├─ ConstructorHandler
    ├─ MemberAccessHandler
    └─ EnumHandler
    ↓
AST #2 (Pure C AST - GENERATED via CNodeBuilder)
    ↓
[Stage 3] Code Generator (C AST Visitor)
    ├─ Header File (.h) - Declarations
    └─ Implementation File (.c) - Definitions
    ↓
Clean C Code + Runtime Library
    ↓
Frama-C Verification
```

## Related Documentation

- [../SUMMARY.md](../SUMMARY.md) - Executive summary
- [../CHANGELOG.md](../CHANGELOG.md) - Version history
- [../feasibility-and-roadmap.md](../feasibility-and-roadmap.md) - Implementation plan

---

*Part of C++ to C Transpiler Research v1.5.1*
