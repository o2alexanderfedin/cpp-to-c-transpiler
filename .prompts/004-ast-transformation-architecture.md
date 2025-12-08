# Research Prompt: AST Transformation vs Direct C Generation Architecture

**Prompt ID:** 004-ast-transformation-architecture
**Created:** 2025-12-08
**Purpose:** Investigate architectural approaches for C++ to C conversion: AST transformation + runtime library vs. direct C code generation

---

## Research Mission

Conduct comprehensive analysis of two fundamental architectural approaches for C++ to C conversion, evaluate trade-offs, and recommend optimal strategy (potentially hybrid) for implementing the converter tool. Produce actionable architectural guidance with concrete prototypes and decision criteria.

---

## Context and Background

### Project Status (v1.4 Complete)

**All research complete, ready for implementation:**
- ✅ v1.1: STL via self-bootstrapping
- ✅ v1.2: Exceptions via PNaCl SJLJ pattern
- ✅ v1.3: Template authoring via transpiler workflow
- ✅ v1.4: Advanced features (RTTI, virtual inheritance, coroutines) documented

**Current research assumes direct C generation:**
- Generate complete C code with inline runtime support
- Exception frames, type_info tables, VTT structures emitted as C code
- Self-contained output with no external dependencies

### Critical Architectural Question

**Should we transform the AST and use a runtime library instead?**

This affects implementation strategy for:
1. **RAII** - Destructor injection at exit points
2. **Exceptions** - Frame setup, unwinding, catch handling
3. **RTTI** - Type info tables, dynamic_cast algorithm
4. **Virtual inheritance** - VTT generation, vbase pointer access
5. **Multiple inheritance** - Pointer adjustment thunks
6. **Coroutines** - State machine transformation
7. **Lambdas** - Closure generation

**Almost every C++ feature could use AST transformation.**

---

## Two Fundamental Approaches

### Approach 1: Direct C Code Generation

**Architecture:**
```
C++ Source → Clang Parse → AST
                            ↓
                    RecursiveASTVisitor
                            ↓
                   Analyze & Generate C
                            ↓
                    Emit C Code (text)
                            ↓
              Generated .c/.h files (self-contained)
```

**Characteristics:**
- Tool walks AST, generates C code as text strings
- All runtime support inlined in generated C
- No external dependencies
- Complete control over generated code structure

**Example (exceptions):**
```c
// Generated C code (inline runtime)
void example(void) {
    // Inline exception frame
    struct __cxx_exception_frame frame;
    static const struct __cxx_action_entry actions[] = {
        { (void(*)(void*))&Resource__dtor, &r },
        { NULL, NULL }
    };
    frame.actions = actions;
    frame.next = __cxx_exception_stack;

    Resource r;
    Resource__ctor(&r);

    if (setjmp(frame.jmpbuf) == 0) {
        __cxx_exception_stack = &frame;
        mayThrow();
        __cxx_exception_stack = frame.next;
        Resource__dtor(&r);
    } else {
        // Catch handler (destructors already called)
        void* ex = frame.exception_object;
        // ... handle exception
    }
}
```

### Approach 2: AST Transformation + Runtime Library

**Architecture:**
```
C++ Source → Clang Parse → AST
                            ↓
                    ASTConsumer/TreeTransform
                            ↓
                   Transform AST (modify in-place)
                            ↓
                    Modified AST
                            ↓
                   Clang CodeGen (C backend)
                            ↓
              Generated .c/.h + runtime library
```

**Characteristics:**
- Tool modifies AST before CodeGen
- Inject runtime library calls into AST
- Clang's CodeGen emits C code
- Runtime library compiled separately

**Example (exceptions):**
```c
// Generated C code (via Clang CodeGen)
void example(void) {
    __cxx_exception_frame frame;

    // Runtime library calls injected via AST
    __cxx_try_begin(&frame, example_actions);

    Resource r;
    Resource__ctor(&r);
    mayThrow();
    Resource__dtor(&r);

    __cxx_try_end(&frame);
}

// runtime.c (generated once, compiled separately)
void __cxx_try_begin(__cxx_exception_frame* frame,
                     const __cxx_action_entry* actions) {
    frame->actions = actions;
    frame->next = __cxx_exception_stack;
    if (setjmp(frame->jmpbuf) == 0) {
        __cxx_exception_stack = frame;
    }
}
```

### Approach 3: Hybrid (Potentially Optimal)

**Use AST transformation for some features, direct generation for others:**

**AST Transformation:**
- RAII destructor injection (CFG-based insertion of destructor calls)
- Coroutine state machine (huge transformation, let Clang handle codegen)
- Exception frame setup/teardown (inject runtime calls)

**Direct C Generation:**
- Runtime library implementation (exception handling, RTTI functions)
- Static data structures (type_info tables, vtables, VTT)
- Complex constructs Clang can't express well

---

## Research Goals

### Goal 1: Understand Clang AST Transformation APIs

**Questions:**
1. What AST transformation APIs does Clang provide?
2. Can we use `TreeTransform<Derived>` for type-safe transformations?
3. How does `Rewriter` work for text-based modifications?
4. Can we create custom `ASTConsumer` with transformation passes?
5. What are the limitations of AST transformation?

**Research:**
- Clang documentation on AST transformation
- Existing Clang tools that transform AST (clang-tidy, refactoring tools)
- LLVM transformation passes vs. AST transformation
- Source-to-source transformation examples

### Goal 2: Evaluate Code Quality for Each Approach

**Metrics:**
1. **Generated code size** - Which produces smaller C output?
2. **Generated code readability** - Which is easier to debug?
3. **Compilation speed** - Does runtime library help?
4. **Frama-C compatibility** - Which is easier to verify?

**Method:**
- Prototype both approaches for simple feature (e.g., RAII)
- Generate C code for same C++ input
- Compare output quality, size, readability
- Test with Frama-C analysis

### Goal 3: Analyze Implementation Complexity

**Questions:**
1. Which approach is easier to implement initially?
2. Which approach is easier to maintain and extend?
3. What is the learning curve for Clang AST transformation?
4. How much code is required for each approach?

**Method:**
- Estimate LOC for each approach
- Identify Clang APIs needed
- Assess developer experience required
- Consider long-term maintainability

### Goal 4: Determine Feature-Specific Recommendations

For each major feature, determine best approach:

| Feature | Direct C Gen | AST Transform | Hybrid | Why? |
|---------|--------------|---------------|--------|------|
| RAII | ? | ? | ? | ? |
| Exceptions | ? | ? | ? | ? |
| RTTI | ? | ? | ? | ? |
| Virtual Inheritance | ? | ? | ? | ? |
| Coroutines | ? | ? | ? | ? |
| Lambdas | ? | ? | ? | ? |

**Research each feature:**
- What AST transformations are needed?
- Can Clang express the result?
- What runtime support is needed?
- What's the complexity trade-off?

---

## Detailed Research Tracks

### Track 1: Clang AST Transformation APIs

**Investigate:**

1. **ASTConsumer and ASTFrontendAction:**
   - How to create custom AST consumer
   - How to integrate into Clang pipeline
   - Can we run multiple transformation passes?

2. **TreeTransform<Derived>:**
   - Type-safe AST node transformations
   - How to transform specific node types (CXXTryStmt, CXXThrowExpr, etc.)
   - Can we inject new statements?
   - Can we create new declarations?

3. **Rewriter:**
   - Text-based source modifications
   - How to insert/delete/replace code
   - Limitations (doesn't update AST)

4. **ASTContext Manipulation:**
   - Creating new AST nodes programmatically
   - Adding declarations to translation unit
   - Managing memory (ASTContext owns nodes)

5. **Clang Refactoring Tools:**
   - How does clang-tidy transform AST?
   - Clang-rename, clang-format internals
   - LibTooling examples

**Sources:**
- Clang AST Transformation documentation
- LibTooling tutorials
- Existing Clang transformation tools source code
- LLVM mailing list discussions

**Deliverable:**
- Document available APIs with code examples
- Identify what transformations are possible vs. impossible
- Provide working prototype: simple AST transformation

### Track 2: Runtime Library Design

**Investigate:**

1. **What goes in runtime library?**
   - Exception handling functions (__cxx_throw, __cxx_catch)
   - RTTI functions (__dynamic_cast, __cxx_type_matches)
   - Memory management (coroutine frame allocation)
   - VTT management functions

2. **How is runtime library packaged?**
   - Single runtime.c/runtime.h?
   - Modular (exception_runtime.c, rtti_runtime.c)?
   - Header-only vs. compiled library?

3. **Portability concerns:**
   - Platform-specific code (setjmp/longjmp, thread-local)
   - Dependency management (libc only?)
   - Cross-compilation support

4. **Frama-C verification:**
   - How to annotate runtime library with ACSL?
   - Can runtime be verified once and reused?
   - What assertions/preconditions are needed?

**Sources:**
- libcxxabi source code (reference runtime)
- emmtrix eCPP2C approach (if documented)
- Existing C runtime libraries
- Frama-C runtime verification examples

**Deliverable:**
- Runtime library architecture design
- API specification for runtime functions
- Prototype runtime implementation for exceptions

### Track 3: Comparative Prototyping

**Build three prototypes for RAII feature:**

**Prototype 1: Direct C Generation**
```cpp
// Input
void func() {
    Resource r;
    use(r);
}
```

Generate via text emission:
```c
void func(void) {
    Resource r;
    Resource__ctor(&r);
    use(&r);
    Resource__dtor(&r);
}
```

**Prototype 2: AST Transformation**
- Transform AST to inject destructor calls
- Use Clang CodeGen to emit C

**Prototype 3: Hybrid**
- Use CFG analysis to find exit points
- Inject calls to runtime library for complex cases

**Compare:**
1. Implementation LOC
2. Generated code quality
3. Time to implement
4. Debuggability
5. Frama-C compatibility

### Track 4: Feature Analysis

For each major feature, analyze transformation feasibility:

#### RAII (Destructor Injection)

**Direct C Generation:**
- Use CFG to find all exit points
- Emit destructor calls as text
- Handle: return, break, continue, goto, exception

**AST Transformation:**
- Use CFG to find exit points
- Insert CallExpr nodes for destructors
- Let Clang CodeGen emit the calls

**Recommendation:** ?

#### Exceptions (PNaCl SJLJ Pattern)

**Direct C Generation:**
- Emit exception frame structs
- Emit setjmp/longjmp code
- Emit action tables
- Emit catch handlers

**AST Transformation:**
- Replace CXXTryStmt with if(setjmp)
- Replace CXXThrowExpr with __cxx_throw call
- Generate action tables as static data

**Recommendation:** ?

#### RTTI (typeid, dynamic_cast)

**Direct C Generation:**
- Emit type_info structs as static data
- Replace typeid/dynamic_cast with function calls
- Emit __dynamic_cast implementation

**AST Transformation:**
- Replace CXXTypeidExpr with call to __cxx_typeid
- Replace CXXDynamicCastExpr with call to __cxx_dynamic_cast
- Generate type_info in runtime library

**Recommendation:** ?

#### Virtual Inheritance (VTT, vbase pointers)

**Direct C Generation:**
- Emit VTT structures as static data
- Emit modified constructors with vbase init
- Emit vbase offset calculations

**AST Transformation:**
- Transform vbase access to runtime calls
- Inject VTT parameter in constructors
- Complex: may exceed AST transformation capabilities

**Recommendation:** ?

#### C++20 Coroutines (State Machines)

**Direct C Generation:**
- Emit coroutine frame struct
- Emit switch-based state machine
- Emit promise object
- Complex but total control

**AST Transformation:**
- Transform coroutine function to state machine
- HUGE transformation, many nodes affected
- Let Clang CodeGen emit resulting C
- May be simpler than manual emission

**Recommendation:** ? (Likely AST transformation wins here)

---

## Evaluation Criteria

### Primary Criteria:

1. **Implementation Complexity**
   - LOC required
   - Clang API learning curve
   - Maintainability

2. **Generated Code Quality**
   - Readability (human can understand)
   - Size (code bloat)
   - Debuggability (#line directives, meaningful names)

3. **Frama-C Compatibility**
   - Can Frama-C analyze the output?
   - Can runtime library be verified separately?
   - Annotation burden

4. **Flexibility**
   - Can we handle edge cases?
   - Can we optimize generated code?
   - Can we support multiple targets?

5. **Portability**
   - Pure C output
   - Minimal dependencies
   - Cross-platform support

### Decision Matrix Template:

For each feature, score 1-5:

| Criterion | Direct C | AST Transform | Hybrid |
|-----------|----------|---------------|--------|
| Implementation Complexity | ? | ? | ? |
| Generated Code Quality | ? | ? | ? |
| Frama-C Compatibility | ? | ? | ? |
| Flexibility | ? | ? | ? |
| Portability | ? | ? | ? |
| **Total** | ? | ? | ? |

---

## Existing Tool Analysis

### emmtrix eCPP2C

**Critical questions:**
1. Does emmtrix use AST transformation or direct C generation?
2. Do they ship a runtime library?
3. How do they handle Frama-C compatibility?
4. What is their code generation strategy?

**Research:**
- Product documentation
- Marketing materials
- Technical papers/presentations
- Customer case studies

### Cfront (Historical)

**Questions:**
1. How did Cfront generate C code?
2. Did it transform AST or generate directly?
3. Did it use runtime library?

### LLVM C Backend (llvm-cbe)

**Why it produces unreadable code:**
- Works on LLVM IR (too low-level)
- Lost high-level C++ semantics
- Could we use Clang CodeGen differently?

---

## Output Specification

### File Structure

Create in `.prompts/004-ast-transformation-architecture/`:

1. **`ast-transformation-research.md`** (2000+ lines)
   - XML-structured comprehensive analysis
   - API documentation with examples
   - Transformation feasibility for each feature
   - Comparative analysis

2. **`ARCHITECTURE-DECISION.md`** (500+ lines)
   - Executive summary
   - Recommendation: Direct / Transform / Hybrid
   - Decision matrix for each feature
   - Implementation roadmap

3. **`PROTOTYPE-COMPARISON.md`** (400+ lines)
   - Side-by-side code examples
   - LOC metrics
   - Generated code quality comparison
   - Performance measurements

4. **`RUNTIME-LIBRARY-DESIGN.md`** (400+ lines)
   - Runtime library architecture
   - API specification
   - Module structure
   - Frama-C annotation strategy

5. **`SUMMARY.md`** (200+ lines)
   - Human-readable findings
   - Clear recommendation
   - Next steps

6. **`prototype/`** directory
   - `direct_c_gen/` - Prototype using direct generation
   - `ast_transform/` - Prototype using AST transformation
   - `hybrid/` - Prototype using hybrid approach
   - Each with working code examples

### Content Requirements

**✓ API Documentation:**
```cpp
// Complete API examples
class RAIITransformer : public RecursiveASTVisitor<RAIITransformer> {
    bool VisitCXXConstructExpr(CXXConstructExpr* E);
    bool VisitReturnStmt(ReturnStmt* S);
    // ... full working example
};
```

**✓ Transformation Examples:**
```
C++ Input:
[C++ code]

AST Nodes:
[AST structure]

Transformed AST:
[Modified AST structure]

Generated C:
[Resulting C code]
```

**✓ Decision Criteria:**
- Quantitative metrics (LOC, code size, compile time)
- Qualitative assessment (readability, maintainability)
- Risk assessment
- Recommendation with confidence level

**✓ Implementation Roadmap:**
- If Direct C Gen: Steps to implement
- If AST Transform: Steps to implement
- If Hybrid: Which features use which approach + steps

---

## Research Execution Plan

### Phase 1: API Research (Days 1-2)
- Study Clang AST transformation documentation
- Examine existing transformation tools
- Identify what's possible vs. impossible
- Document APIs with examples

### Phase 2: Prototyping (Days 3-5)
- Build 3 prototypes for RAII
- Implement simple exception handling in each
- Measure complexity, code quality
- Test with Frama-C

### Phase 3: Feature Analysis (Days 6-7)
- Analyze each major feature
- Fill decision matrix
- Evaluate trade-offs
- Identify hybrid opportunities

### Phase 4: Runtime Design (Day 8)
- Design runtime library architecture
- Specify API
- Plan Frama-C verification strategy

### Phase 5: Synthesis (Days 9-10)
- Write comprehensive analysis
- Make clear recommendation
- Document implementation roadmap
- Update main research documents

**Total Duration:** 10 days intensive research with prototyping

---

## Success Criteria

- [ ] **API Understanding:** Clear documentation of what Clang AST APIs can do
- [ ] **Working Prototypes:** Three prototypes demonstrating different approaches
- [ ] **Quantitative Comparison:** Metrics for code size, complexity, quality
- [ ] **Feature Recommendations:** Clear decision for each C++ feature
- [ ] **Overall Recommendation:** Direct / Transform / Hybrid with confidence level
- [ ] **Implementation Roadmap:** Step-by-step guide for chosen approach
- [ ] **Confidence Level:** HIGH or VERY HIGH for recommended approach

---

## Integration with Existing Research

### Update These Documents:

**1. feasibility-and-roadmap.md:**
```markdown
## Architecture Decision (v1.5)

**Approach:** [Direct C Generation / AST Transformation / Hybrid]

**Rationale:** [Explanation based on research]

**Impact on Implementation:**
- Phase 1 POC: [What to prototype]
- Runtime library: [Yes/No, design]
- Feature-specific strategies: [List]
```

**2. SUMMARY.md:**
- Add v1.5 architecture decision
- Update implementation roadmap
- Document runtime library if applicable

**3. CHANGELOG.md:**
- Version 1.5 entry
- Architecture research findings
- Decision and rationale

---

## Key Questions to Answer

**Architectural:**
1. Direct C generation or AST transformation or hybrid?
2. Do we need a runtime library?
3. Which features use which approach?

**Technical:**
4. Can Clang AST transformation do what we need?
5. What are the hard limitations?
6. How does Clang CodeGen emit C?

**Practical:**
7. Which approach is easier to implement?
8. Which produces better generated code?
9. Which is easier to maintain long-term?

**Quality:**
10. Frama-C compatibility for each approach?
11. Debuggability and #line directives?
12. Code size and compilation speed?

---

## Begin Research Now

Execute comprehensive analysis with prototyping. Produce clear architectural recommendation ready for v1.5 documentation.

**Expected outcome:** Confident architectural decision enabling Phase 1 POC implementation to proceed efficiently.

**Start with:** Clang AST transformation API research, then build prototypes for comparison.
