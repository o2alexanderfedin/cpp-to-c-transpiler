# Research Prompt: Advanced C++ Features Implementation Patterns

**Prompt ID:** 003-advanced-features-research
**Created:** 2025-12-08
**Purpose:** Investigate RTTI, virtual inheritance, and coroutines implementation in C++ compilers that generate C output

---

## Research Mission

Conduct comprehensive historical and technical research to discover how RTTI (typeid/dynamic_cast), virtual inheritance, and C++20 coroutines were implemented in C++ compilers that generated C or C-like output. Produce actionable implementation guidance with concrete code examples and complexity assessments.

---

## Context and Background

### Project Status (v1.3)

**C++ to C Converter Tool - All Major Challenges SOLVED:**
- ✅ **v1.1:** STL via self-bootstrapping (tool converts STL implementations automatically)
- ✅ **v1.2:** Exceptions + RAII via PNaCl SJLJ pattern (proven, documented, production-tested)
- ✅ **v1.3:** Template authoring via transpiler workflow (C++ is source, C is build artifact)

**Current State:**
- Zero fundamental limitations identified
- General-purpose modern C++ to C conversion is viable
- Three advanced features require implementation work: RTTI, virtual inheritance, coroutines
- Status: Implementable but lacking documented solution patterns

### Success Pattern from Previous Research

**Exception Handling (v1.2):**
- Historical research discovered PNaCl SJLJ pattern
- Found proven solution that Cfront (1993) failed to implement
- Delivered concrete implementation guide with code examples
- Result: Transformed "complex challenge" into "solved with known pattern"

**Goal:** Replicate this success for RTTI, virtual inheritance, and coroutines.

---

## Three Research Tracks

### Track 1: RTTI (Runtime Type Information)

**Features to Investigate:**
1. `typeid` operator - returns `std::type_info` reference
2. `dynamic_cast` - type-safe downcasting with runtime checking
3. Type information tables and structures
4. Type hierarchy encoding for inheritance checking

**Key Questions:**
- How did Cfront represent type_info in C structs?
- What algorithm did early compilers use for dynamic_cast pointer adjustment?
- How are type hierarchies encoded for `is_base_of` checks?
- What simplifications did embedded compilers make?
- Can RTTI be disabled/optional (like -fno-rtti)?

**Research Sources:**
- Cfront source code or documentation (if available)
- Itanium C++ ABI specification (type_info structure)
- GCC libstdc++ implementation (type_info.cc, type_info.h)
- Embedded C++ specification (EC++ may restrict RTTI)
- CUDA C++ restrictions (does nvcc support RTTI?)
- emmtrix eCPP2C documentation

**Expected Deliverable:**
Implementation guide showing:
```c
// Example desired output:
struct __type_info {
    const char* name;
    const struct __type_info** bases;  // For inheritance checking
    size_t num_bases;
};

// Generated type_info for class hierarchy
extern const struct __type_info __ti_Base;
extern const struct __type_info __ti_Derived;

// dynamic_cast implementation
void* __dynamic_cast(void* ptr, const struct __type_info* from,
                     const struct __type_info* to, ptrdiff_t offset);
```

### Track 2: Virtual Inheritance

**Features to Investigate:**
1. Virtual base pointers (vbptr) in object layout
2. Diamond problem resolution (single shared base instance)
3. Constructor/destructor calling order
4. Vtable layouts for virtual inheritance
5. Pointer adjustment for virtual base access

**Key Questions:**
- How did Cfront handle virtual inheritance before 1993?
- What is the Itanium C++ ABI layout for virtual bases?
- How are vbase_offsets stored and accessed?
- How do constructors initialize virtual bases exactly once?
- What simplifications make this tractable?

**Research Sources:**
- Cfront documentation on virtual inheritance
- Itanium C++ ABI specification (virtual base class layout)
- GCC/Clang vtable implementation details
- Microsoft C++ ABI (may differ but provides comparison)
- Academic papers on multiple inheritance implementation
- CUDA C++ restrictions (does nvcc support virtual inheritance?)

**Expected Deliverable:**
Implementation guide showing:
```c
// Example desired output:
struct Base { int base_field; };

struct Derived1 {
    struct __vtable* vptr;
    ptrdiff_t vbase_offset;  // Offset to virtual base
    int derived1_field;
};

struct Derived2 {
    struct __vtable* vptr;
    ptrdiff_t vbase_offset;
    int derived2_field;
};

struct Diamond {
    struct __vtable* vptr_derived1;
    int derived1_field;
    struct __vtable* vptr_derived2;
    int derived2_field;
    struct Base base;  // Single shared instance
};

// Constructor pattern for Diamond
void Diamond__ctor(Diamond* this, int is_most_derived) {
    if (is_most_derived) {
        Base__ctor(&this->base);  // Init virtual base once
    }
    Derived1__ctor_base(this, 0);  // Don't init virtual base
    Derived2__ctor_base(this, 0);
}
```

### Track 3: Coroutines (C++20)

**Features to Investigate:**
1. Coroutine state machines
2. Heap-allocated coroutine frames
3. Suspend/resume point implementation
4. Promise objects and return values
5. `co_await`, `co_yield`, `co_return` operators

**Key Questions:**
- How can coroutine state be represented as C struct?
- What state machine pattern is used for suspend points?
- How are coroutine frames allocated/deallocated?
- Are there prior art examples (async/await in other languages)?
- What simplifications make this implementable?

**Research Sources:**
- C++20 coroutines specification
- LLVM coroutine lowering passes (CoroSplit, CoroFrame)
- Academic papers on coroutine compilation
- Async/await implementations in C (e.g., protothreads, Duff's device)
- State machine generation patterns
- Does any C++ to C compiler support coroutines?

**Expected Deliverable:**
Implementation guide showing:
```c
// Example desired output:
enum __coro_state { CORO_START, CORO_SUSPENDED_1, CORO_SUSPENDED_2, CORO_DONE };

struct generator_int_frame {
    enum __coro_state state;
    int current_value;
    // Local variables hoisted to frame
    int i;
};

// Generated from: generator<int> count_to(int n) { ... }
void generator_int_resume(struct generator_int_frame* frame) {
    switch (frame->state) {
        case CORO_START:
            frame->i = 0;
            goto label_1;
        case CORO_SUSPENDED_1:
            goto label_1;
        case CORO_DONE:
            return;
    }

label_1:
    if (frame->i < frame->n) {
        frame->current_value = frame->i++;
        frame->state = CORO_SUSPENDED_1;
        return;  // co_yield
    }
    frame->state = CORO_DONE;
}
```

---

## Research Methodology

### Phase 1: Source Discovery (Web Research)

For each track, search for:

1. **Historical Compiler Documentation:**
   - Cfront implementation notes
   - Comeau C++ technical documentation
   - Early GCC/EDG papers or documentation
   - AT&T C++ compiler history

2. **Specifications and Standards:**
   - Itanium C++ ABI (most detailed ABI spec)
   - Microsoft C++ ABI documentation
   - Embedded C++ specification
   - C++20 coroutines specification

3. **Modern Compiler Implementations:**
   - LLVM/Clang implementation (libcxxabi, vtable generation)
   - GCC libstdc++ implementation
   - CUDA C++ language restrictions
   - emmtrix eCPP2C feature support

4. **Academic and Technical Papers:**
   - "The Annotated C++ Reference Manual" (Ellis & Stroustrup)
   - "Inside the C++ Object Model" (Stanley Lippman)
   - Papers on multiple inheritance implementation
   - Coroutine compilation techniques

### Phase 2: Code Analysis

Examine actual implementations:
- libcxxabi source code (type_info, dynamic_cast)
- Clang CodeGen for virtual inheritance
- LLVM coroutine passes
- Any available Cfront source code

### Phase 3: Synthesis and Documentation

For each feature, produce:

1. **Technical Overview:**
   - How the feature works in C++
   - Runtime requirements
   - Data structures needed

2. **C Transformation Pattern:**
   - C++ input example
   - Generated C output example
   - Supporting runtime functions

3. **Implementation Algorithm:**
   - Step-by-step code generation process
   - AST traversal requirements
   - Edge cases and corner cases

4. **Complexity Assessment:**
   - Implementation effort (days/weeks/months)
   - Technical risk level (low/medium/high)
   - Dependencies on other features

5. **Simplifications and Restrictions:**
   - Optional features that can be deferred
   - Restrictions that reduce complexity
   - Trade-offs to consider

---

## Output Specification

### File Structure

Create in `.prompts/003-advanced-features-research/`:

1. **`advanced-features-research.md`** (Main document, 2500+ lines)
   - XML-structured for Claude-to-Claude consumption
   - Three major sections (RTTI, virtual inheritance, coroutines)
   - Comprehensive technical details
   - Code examples throughout

2. **`RTTI-IMPLEMENTATION-GUIDE.md`** (400+ lines)
   - Similar to EXCEPTION-HANDLING-SOLUTION.md
   - Data structures, algorithms, code examples
   - Implementation checklist with effort estimates

3. **`VIRTUAL-INHERITANCE-GUIDE.md`** (400+ lines)
   - Object layout patterns
   - Constructor/destructor algorithms
   - Vtable generation

4. **`COROUTINES-GUIDE.md`** (400+ lines)
   - State machine transformation
   - Frame allocation strategy
   - Suspend/resume implementation

5. **`SUMMARY.md`** (200+ lines)
   - Executive summary for humans
   - Key findings for each feature
   - Complexity assessments
   - Recommendations

6. **`CHANGELOG.md`**
   - Research progression
   - Discoveries made
   - Confidence assessment

### Content Requirements

Each implementation guide must include:

**✓ Core Data Structures:**
```c
// Complete C struct definitions
// Runtime function prototypes
// Supporting type definitions
```

**✓ Transformation Examples:**
```
C++ Input:
[concrete C++ code]

Generated C Output:
[complete C code with comments]
```

**✓ Implementation Algorithm:**
- Step-by-step pseudocode
- AST traversal pattern
- Code emission strategy

**✓ Edge Cases:**
- List all corner cases
- Show how each is handled
- Test cases

**✓ Complexity Assessment:**
- Effort estimate (weeks)
- Risk level (low/medium/high)
- Dependencies

**✓ Implementation Checklist:**
- [ ] Phase 1: Data structures (X weeks)
- [ ] Phase 2: Code generation (X weeks)
- [ ] Phase 3: Edge cases (X weeks)
- [ ] Phase 4: Testing (X weeks)

### Quality Standards

**Must match EXCEPTION-HANDLING-SOLUTION.md quality:**
- Concrete and actionable (not theoretical)
- Production-ready patterns (proven where possible)
- Complete code examples (not fragments)
- Clear complexity assessment
- Implementation roadmap

**Success Criteria:**
- ✓ Found proven patterns from historical compilers
- ✓ Concrete algorithms, not just concepts
- ✓ Confidence assessment: HIGH or VERY HIGH
- ✓ Clear implementation path for each feature
- ✓ No fundamental blockers identified

---

## Specific Research Questions to Answer

### RTTI Questions:

1. **Structure:** How is type_info represented in C? What fields?
2. **Hierarchy:** How are base classes encoded for `is_base_of` checks?
3. **dynamic_cast:** What algorithm finds target type and adjusts pointer?
4. **typeid:** How is the type_info reference returned?
5. **Simplifications:** Can we restrict cross-casts? Require -fno-rtti mode?
6. **Effort:** Days, weeks, or months to implement?

### Virtual Inheritance Questions:

1. **Layout:** Where are vbase pointers stored in object?
2. **Offset:** How are vbase_offsets computed and stored?
3. **Construction:** How do constructors init virtual bases exactly once?
4. **Vtables:** What additional vtable entries are needed?
5. **Simplifications:** Can we restrict depth of virtual inheritance?
6. **Effort:** Days, weeks, or months to implement?

### Coroutines Questions:

1. **State Machine:** What states are needed? How many suspend points?
2. **Frame:** What goes in coroutine frame struct?
3. **Allocation:** Heap or stack? Can we optimize?
4. **Promise:** How is promise object implemented?
5. **Simplifications:** Can we support only generators? Defer async?
6. **Effort:** Days, weeks, or months to implement?

---

## Historical Compiler Analysis

### Key Compilers to Research:

**1. Cfront (1983-1993):**
- Original C++ to C translator by Bjarne Stroustrup
- **Critical:** Did it implement RTTI? Virtual inheritance? (likely pre-RTTI)
- May have implemented virtual inheritance
- Research: Available documentation, papers, source code fragments

**2. Comeau C++ (1990s-2000s):**
- Commercial C++ to C compiler
- Known to support full C++ features
- **Critical:** Likely implemented RTTI and virtual inheritance
- Research: Any available documentation or technical papers

**3. Early GCC/EDG (1990s):**
- Before native code generation became standard
- May have had C backend
- Research: Historical GCC documentation, EDG papers

**4. CUDA C++ / nvcc (2007-present):**
- Restricted C++ subset for GPU programming
- **Critical:** What restrictions exist for RTTI, virtual inheritance?
- Does not support full C++ (no exceptions confirmed)
- Research: CUDA C++ Programming Guide restrictions list

**5. Embedded C++ Compilers:**
- Resource-constrained environments
- Often restrict RTTI and virtual inheritance
- Research: Embedded C++ specification, commercial compiler docs

**6. emmtrix eCPP2C (present):**
- Commercial C++17 to C for safety-critical
- **Critical:** What features do they support? How?
- Research: Product documentation, marketing materials, technical papers

---

## Deliverable Integration

### Update Existing Research:

**1. Update `feasibility-and-roadmap.md`:**
```markdown
### Advanced Features - NOW DOCUMENTED (v1.4)

✅ **RTTI - Implementation Pattern Found**
- [Summary of findings]
- Effort: X weeks
- Verdict: IMPLEMENTABLE with [pattern name]

✅ **Virtual Inheritance - Implementation Pattern Found**
- [Summary of findings]
- Effort: X weeks
- Verdict: IMPLEMENTABLE with [pattern name]

✅ **Coroutines - Implementation Pattern Found**
- [Summary of findings]
- Effort: X weeks
- Verdict: IMPLEMENTABLE with [pattern name]
```

**2. Update `SUMMARY.md`:**
- Add v1.4 summary
- Include complexity assessments
- Update "Next Steps" with implementation priorities

**3. Create `CHANGELOG.md` entry:**
- Version 1.4 - Advanced Features Research
- Key discoveries
- Implementation complexity confirmed

---

## Success Criteria Checklist

Before completing research, verify:

- [ ] **RTTI:** Found concrete implementation pattern with code examples
- [ ] **Virtual Inheritance:** Found object layout and constructor patterns
- [ ] **Coroutines:** Found state machine transformation pattern
- [ ] **Historical Validation:** Identified at least one compiler that implemented each feature
- [ ] **Complexity:** Provided effort estimates for each feature
- [ ] **Confidence:** Assessment is HIGH or VERY HIGH for implementability
- [ ] **Blockers:** Confirmed no fundamental blockers exist
- [ ] **Actionable:** Implementation guides provide step-by-step roadmap
- [ ] **Quality:** Output matches EXCEPTION-HANDLING-SOLUTION.md standard

---

## Research Execution

**Execute this research immediately. Proceed through:**

1. **Web research** - Historical compilers, specifications, papers
2. **Code analysis** - Examine libcxxabi, Clang, LLVM implementations
3. **Synthesis** - Create implementation guides with concrete examples
4. **Documentation** - Produce all required deliverables
5. **Integration** - Update existing research documents

**Expected Research Duration:** 2-4 hours of focused research

**Target Completion:** Comprehensive documentation ready for v1.4 release

---

## Begin Research Now

You are a research agent with access to web search, code analysis, and document creation tools. Conduct this research thoroughly and produce actionable implementation guidance for RTTI, virtual inheritance, and coroutines in a C++ to C converter.

**Start with:** Historical compiler analysis to find proven patterns, then proceed to technical implementation details.

**Remember:** Success looks like finding the "PNaCl pattern" equivalent for each feature - proven, documented, actionable.
