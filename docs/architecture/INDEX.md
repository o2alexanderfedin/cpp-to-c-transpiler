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

## Architecture Timeline

| Version | Date | Achievement |
|---------|------|-------------|
| v1.0 | Initial | Feasibility assessment |
| v1.5 | Dec 8 | Direct C generation validated |
| v1.5.1 | Dec 8 | Intermediate C AST refinement |

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
Clang Parser + Sema
    ↓
AST #1 (Full C++ AST - READ ONLY)
    ↓
Translation Layer (RecursiveASTVisitor)
    ↓
AST #2 (Pure C AST - GENERATED)
    ↓
Clang DeclPrinter/StmtPrinter
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
