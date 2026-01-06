# Research: COM/DCOM Vtable Architecture for Strongly-Typed VMT

<objective>
Research how Microsoft COM/DCOM implements virtual method tables in plain C with strongly-typed function pointers, and evaluate whether this pattern should replace our current generic function pointer approach.

**Why this matters:** Our current vtable implementation uses generic function pointers cast at call sites. The COM/DCOM pattern uses:
1. Strongly-typed function pointers in vtable structs
2. Static C functions matching exact signatures
3. Compile-time type safety instead of runtime casts
4. Better debugging and readability

**End goal:**
- Complete understanding of COM vtable patterns with concrete code examples
- Comparison of COM approach vs current transpiler approach
- Evidence-based recommendation on whether to adopt COM patterns
- If adopted: implementation plan with migration strategy

</objective>

<context>
**Current VMT implementation:**
@src/VtableGenerator.cpp:110-130 - Generates generic function pointers:
```c
struct ClassName_vtable {
    const struct __class_type_info *type_info;
    ReturnType (*methodName)(struct ClassName *this, params...);
    void (*destructor)(struct ClassName *this);
};
```

**Current initialization:**
@src/VtableInitializer.cpp - Initializes vtables with casts

**Key files:**
@src/VtableGenerator.cpp - Vtable struct generation
@src/VtableInitializer.cpp - Vtable initialization
@src/VirtualMethodAnalyzer.cpp - Virtual method detection
@src/OverrideResolver.cpp - Override resolution
@include/VtableGenerator.h - Interface definition

**Project conventions:**
@CLAUDE.md - TDD, SOLID, type safety requirements

**Recent work:**
- Just completed pointer recursion fix (commit df8e4b9)
- Optimized name mangling to skip 'this' parameter
- Strong emphasis on type safety and compile-time checking
</context>

<research_questions>
## Critical Questions to Answer

### Q1: How Does COM Define Vtables in C?
- What does a COM interface vtable struct look like?
- How are function pointers declared (generic void* or strongly typed)?
- Where are method signatures defined?
- Example from actual COM code (IUnknown, IClassFactory, custom interfaces)

### Q2: How Are COM Vtables Initialized?
- Are static functions declared separately?
- How are vtable instances populated?
- Pattern for mapping C++ methods to C static functions
- Type safety enforcement mechanisms

### Q3: How Are COM Virtual Methods Invoked?
- Call syntax from client code
- How is 'this' pointer passed?
- Comparison to our current approach
- Performance implications (if any)

### Q4: What Are the Benefits of COM Pattern?
- **Type Safety**: Compile-time vs runtime checking
- **Debuggability**: Function names in debugger vs generic pointers
- **Readability**: Clear signatures vs casts
- **Tooling**: IDE support, static analysis benefits

### Q5: What Are the Costs of COM Pattern?
- Code size increase (explicit static functions)
- Build time impact
- Complexity in generator code
- Migration effort from current approach

### Q6: Should We Adopt This Pattern?
- For all methods or just virtual methods?
- Incremental adoption strategy
- Backwards compatibility concerns
- Testing requirements

### Q7: How Do Other C++ to C Transpilers Handle This?
- Frama-Clang approach
- Other transpilers (if any)
- Industry patterns
</research_questions>

<experiments>
## Research Tasks

### Task 1: Analyze COM Interface Patterns
**Goal:** Get concrete examples of COM vtable declarations in C

**Steps:**
1. Web search for "COM interface definition C vtable structure"
2. Find IUnknown interface definition (canonical example)
3. Find custom COM interface examples
4. Document exact patterns used

**Expected outcome:** Code examples showing COM vtable struct definitions

---

### Task 2: Analyze COM Implementation Patterns
**Goal:** See how COM interfaces are implemented in C

**Steps:**
1. Web search for "implementing COM interface in C"
2. Find examples of static function implementations
3. Document vtable initialization patterns
4. Look for type safety enforcement mechanisms

**Expected outcome:** Code examples of COM implementation with static functions

---

### Task 3: Compare Current vs COM Approach
**Goal:** Side-by-side comparison with actual code

**Steps:**
1. Take example from our codebase (simple class with virtual methods)
2. Show current transpiled output
3. Show what COM-style output would look like
4. Highlight differences in type safety, readability

**Example input:**
```cpp
class Shape {
public:
    virtual int getArea() = 0;
    virtual void draw() = 0;
    virtual ~Shape() {}
};

class Circle : public Shape {
    int radius;
public:
    int getArea() override { return 3.14 * radius * radius; }
    void draw() override { /* ... */ }
};
```

**Expected outcome:**
- Current transpiled C code
- COM-style transpiled C code
- Analysis of trade-offs

---

### Task 4: Research Frama-Clang's Approach
**Goal:** See how production C++ to C transpiler handles vtables

**Steps:**
1. Check Frama-Clang codebase (already cloned at /tmp/frama-clang)
2. Search for vtable generation code
3. Document their approach
4. Compare to COM pattern

**Expected outcome:** Understanding of Frama-Clang's design choices

---

### Task 5: Performance Analysis
**Goal:** Determine if COM pattern has runtime cost

**Steps:**
1. Analyze call overhead: direct function pointer vs typed pointer
2. Look for any indirection differences
3. Check if compilers optimize both equally

**Expected outcome:** Evidence on performance impact (if any)

---

### Task 6: Create Prototype COM-Style Generator
**Goal:** Proof-of-concept implementation

**Steps:**
1. Create new generator class: `ComStyleVtableGenerator`
2. Implement for simple test case (Shape/Circle example)
3. Generate both current and COM-style output
4. Compile both, measure code size
5. Test correctness

**Expected outcome:** Working prototype with measurable comparison

</experiments>

<verification>
Research is complete when we can answer ALL of these:

1. ✅ Concrete COM vtable examples with code
2. ✅ COM implementation pattern with static functions
3. ✅ Side-by-side comparison: current vs COM approach
4. ✅ Type safety analysis (what catches errors at compile time)
5. ✅ Performance analysis (any runtime cost)
6. ✅ Code size analysis (binary bloat concerns)
7. ✅ Frama-Clang's approach documented
8. ✅ Clear recommendation: adopt, hybrid, or reject
9. ✅ If adopt: implementation plan with phases
10. ✅ If reject: rationale with evidence

**Documentation required:**
- `31-01-FINDINGS.md` with all evidence
- Code examples (COM, current, proposed)
- Comparison tables (benefits, costs, metrics)
- Discussion points for architectural decision
</verification>

<output>
Create: `.planning/phases/31-com-vmt-architecture/31-01-FINDINGS.md`

**Required sections:**

```markdown
# COM/DCOM Vtable Architecture Research Findings

**[One sentence recommendation: adopt, hybrid approach, or stay with current]**

## Executive Summary
[2-3 paragraphs: what is COM pattern, key findings, recommendation]

## COM Vtable Pattern Explained

### IUnknown Example
[Code showing canonical COM interface]

### Custom Interface Example
[Code showing real-world COM interface]

### Implementation Pattern
[Code showing static functions and vtable initialization]

## Current Transpiler Approach

### Current Vtable Structure
[Code from VtableGenerator.cpp]

### Current Invocation
[Code showing how virtual methods are called]

## Side-by-Side Comparison

### Example: Shape/Circle Classes

**Input C++ code:**
[Shape and Circle classes]

**Current transpiler output:**
[Generated C code with current approach]

**COM-style output (proposed):**
[What it would look like with COM pattern]

## Type Safety Analysis

### Errors Caught at Compile Time
[Examples of type mismatches caught by compiler]

### Current Approach Type Safety
[What current approach catches/misses]

### COM Approach Type Safety
[What COM approach catches/misses]

## Performance Analysis
[Call overhead, indirection, compiler optimization]

## Code Size Analysis
[Binary size comparison, readability trade-offs]

## Frama-Clang Approach
[How production transpiler handles this]

## Benefits of COM Pattern
1. [Benefit with evidence]
2. [Benefit with evidence]
...

## Costs of COM Pattern
1. [Cost with evidence]
2. [Cost with evidence]
...

## Recommendation

### Primary Recommendation
[Adopt / Hybrid / Reject with clear rationale]

### Implementation Strategy (if adopt/hybrid)
- Phase 1: [First step]
- Phase 2: [Second step]
...

### Migration Plan (if adopt/hybrid)
[How to transition from current approach]

### Testing Strategy
[How to validate correctness]

## Discussion Points

### For User Decision
1. [Key trade-off to discuss]
2. [Architectural choice]
...

### Open Questions
1. [Questions requiring user input]
2. [Unclear design choices]
...

## Code Examples

### Appendix A: Full COM IUnknown
[Complete working example]

### Appendix B: Full Current Transpiler Output
[Complete example from current code]

### Appendix C: Full COM-Style Proposal
[Complete example of proposed approach]
```

</output>

<success_criteria>
Research succeeds when:
- COM patterns fully understood with concrete examples
- Current approach fully documented
- Side-by-side comparison shows exact differences
- Type safety, performance, code size quantified
- Clear recommendation with evidence
- Implementation plan ready (if adopting)
- Discussion points prepared for user
- User can make informed architectural decision
</success_criteria>
