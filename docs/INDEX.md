# C++ to C Transpiler Documentation

**Version:** 1.5.1 (Architecture Refinement Complete)
**Status:** Research Complete - Ready for Phase 1 POC
**Confidence:** 97%+

## Quick Navigation

### Primary Documents

1. **[SUMMARY.md](SUMMARY.md)** - Executive summary (316 lines)
   - Quick overview of research findings
   - Confidence assessment
   - Key breakthroughs

2. **[CHANGELOG.md](CHANGELOG.md)** - Version history and breakthroughs
   - Research timeline (v1.0 → v1.5.1)
   - Key decisions and pivots
   - Architecture evolution

3. **[feasibility-and-roadmap.md](feasibility-and-roadmap.md)** - Implementation plan (1,023 lines)
   - 6-month roadmap to production
   - Phase-by-phase breakdown
   - Risk assessment

4. **[technical-analysis.md](technical-analysis.md)** - Complete technical analysis (2,333 lines)
   - Comprehensive research findings
   - Clang AST infrastructure analysis
   - Implementation patterns

### Feature-Specific Guides

5. **[features/exceptions.md](features/exceptions.md)** - PNaCl SJLJ exception handling (599 lines)
   - Thread-safe exception pattern
   - Action table implementation
   - RAII + exceptions integration

6. **[features/rtti.md](features/rtti.md)** - RTTI implementation (938 lines)
   - Itanium ABI patterns
   - type_info generation
   - dynamic_cast translation

7. **[features/virtual-inheritance.md](features/virtual-inheritance.md)** - Virtual inheritance (997 lines)
   - VTT generation
   - Diamond problem resolution
   - Virtual base offset tables

8. **[features/coroutines.md](features/coroutines.md)** - C++20 coroutines (1,321 lines)
   - State machine transformation
   - LLVM CoroSplit patterns
   - Promise type generation

### Architecture Documentation

9. **[architecture/architecture-decision.md](architecture/architecture-decision.md)** - Architecture rationale (949 lines)
   - v1.5 + v1.5.1 decision process
   - Intermediate C AST approach
   - Why not TreeTransform

10. **[architecture/prototype-comparison.md](architecture/prototype-comparison.md)** - Quantitative analysis (863 lines)
    - Code quality metrics
    - LOC comparisons
    - Frama-C tractability

11. **[architecture/runtime-library-design.md](architecture/runtime-library-design.md)** - Runtime library spec (713 lines)
    - exception_runtime.c design
    - rtti_runtime.c design
    - Size estimates (1.7-2.8 KB)

### Implementation Guides

12. **[CONSTRUCTOR-GUIDE.md](CONSTRUCTOR-GUIDE.md)** - Constructor implementation guide
    - Constructor splitting and initialization
    - Member initialization lists
    - Base class constructor chaining

13. **[RUNTIME_CONFIGURATION.md](RUNTIME_CONFIGURATION.md)** - Runtime configuration guide
    - Runtime modes (library vs inline)
    - Feature flags
    - Size optimization strategies

14. **[MIGRATION_GUIDE.md](MIGRATION_GUIDE.md)** - Migration guide for developers
    - Transpiling existing C++ codebases
    - Common patterns and solutions
    - Best practices

15. **[PROFILING_GUIDE.md](PROFILING_GUIDE.md)** - Performance profiling guide
    - Profiling transpiled code
    - Performance optimization strategies
    - Benchmarking methodology

16. **[FORMAL_VERIFICATION_GUIDE.md](FORMAL_VERIFICATION_GUIDE.md)** - Formal verification guide
    - Frama-C integration
    - ACSL annotations
    - Verification workflow

17. **[ACSL_ANNOTATIONS.md](ACSL_ANNOTATIONS.md)** - ACSL annotation reference
    - ACSL syntax and semantics
    - Annotation patterns for generated code
    - Verification examples

18. **[TEST_SUITE.md](TEST_SUITE.md)** - Test suite documentation (958 lines)
    - 66 test files, 492+ test functions, 1,956+ assertions
    - 9 test categories (virtual functions, exceptions, RTTI, coroutines, etc.)
    - Integration tests and performance benchmarks
    - Test expansion roadmap

## Research Archive

See **[../research-archive/INDEX.md](../research-archive/INDEX.md)** for the complete research process documentation.

## Total Documentation

**15,461+ lines** of comprehensive technical research and implementation guides across 18 primary documents.

## Key Achievements

- ✅ STL Self-Bootstrapping (v1.1)
- ✅ Exception Handling - PNaCl SJLJ (v1.2)
- ✅ Template Authoring - Transpiler workflow (v1.3)
- ✅ Advanced Features - RTTI, virtual inheritance, coroutines (v1.4)
- ✅ Architecture Validation - Direct C generation (v1.5)
- ✅ Architecture Refinement - Intermediate C AST (v1.5.1)

## Next Steps

Proceed to **Phase 1: Proof of Concept** (3-4 weeks):
- Implement CNodeBuilder helper library
- Simple C++ class → C struct translation
- Clang printer integration with #line directives
- Frama-C compatibility validation

---

*Research completed December 2025 | Generated with [Claude Code](https://claude.com/claude-code)*
