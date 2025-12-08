# Technical Architecture Document Generation

## Objective

Create a comprehensive, implementation-focused technical architecture document for the C++ to C transpiler that synthesizes research findings into a cohesive architectural blueprint. The document should serve as the authoritative reference for implementers, covering all architectural layers while maintaining visual clarity through Mermaid diagrams.

**Why this matters:** With 13,545+ lines of research across 11 documents, we need a single cohesive architecture document that bridges research findings with implementation guidance. This enables developers to understand the complete system design without reading thousands of lines of research notes.

## Context

### Source Documentation

Read and synthesize from these documents:

**Primary Architecture:**
- `docs/architecture/architecture-decision.md` - v1.5 + v1.5.1 rationale, Two-Phase Translation approach
- `docs/architecture/prototype-comparison.md` - Quantitative analysis, code quality metrics
- `docs/architecture/runtime-library-design.md` - Runtime API specifications

**Core Documentation:**
- `docs/SUMMARY.md` - Executive summary, confidence assessment
- `docs/CHANGELOG.md` - Version history, key decisions
- `docs/feasibility-and-roadmap.md` - Implementation plan, phase breakdown
- `docs/technical-analysis.md` - Complete technical analysis (2,333 lines)

**Feature Implementation:**
- `docs/features/exceptions.md` - PNaCl SJLJ exception handling (599 lines)
- `docs/features/rtti.md` - Itanium ABI RTTI patterns (938 lines)
- `docs/features/virtual-inheritance.md` - VTT generation (997 lines)
- `docs/features/coroutines.md` - State machine transformation (1,321 lines)

### Research Context

- **Architecture Version:** v1.5.1 (Two-Phase Translation with Intermediate C AST)
- **Confidence Level:** 97%+
- **Total Research:** 13,545+ lines across 11 documents
- **Implementation Phases:** 5 phases over 6 months
- **Key Decision:** Intermediate C AST > Direct text emission (80% cleaner output, 10x easier verification)

## Requirements

### Document Structure

Create `docs/ARCHITECTURE.md` with the following sections:

#### 1. Executive Overview (1-2 pages)
- One-paragraph system description
- Key architectural decisions summary
- Technology stack overview
- Link to [docs/SUMMARY.md](docs/SUMMARY.md) for research context

#### 2. System Architecture

**2.1 High-Level Architecture**
- Mermaid C4 context diagram or architecture diagram
- Major components and their interactions
- Data flow overview (C++ source → C output)
- Link to [docs/architecture/architecture-decision.md](docs/architecture/architecture-decision.md) for decision rationale

**2.2 Two-Phase Translation Pipeline**
- Mermaid flowchart showing complete pipeline:
  - C++ Source → Clang Parser + Sema → AST #1 (C++ AST)
  - AST #1 → Translation Layer (RecursiveASTVisitor) → AST #2 (C AST)
  - AST #2 → Clang Printer (DeclPrinter/StmtPrinter) → C Code
  - Generated C Code + Runtime Library → Frama-C Verification
- Key transformation points highlighted
- Link to [docs/architecture/prototype-comparison.md](docs/architecture/prototype-comparison.md) for metrics

**2.3 Architecture Decision Record**
- Why Intermediate C AST? (synthesize from architecture-decision.md)
- Why not TreeTransform? (key points only, link for details)
- Why Runtime Library? (benefits summary, link to runtime-library-design.md)

#### 3. Component Design

**3.1 CNodeBuilder**
- Purpose: Encapsulate verbose Clang C node creation
- Mermaid class diagram showing key builder methods
- Estimated size: 500-800 LOC
- Example API (1-2 minimal code snippets showing usage pattern)

**3.2 Translation Layer (RecursiveASTVisitor)**
- Purpose: C++ AST → C AST transformation
- Mermaid sequence diagram for translation flow
- Key visitor methods (VisitCXXThrowExpr, VisitCXXTryStmt, VisitLambdaExpr, etc.)
- Transformation strategies per C++ feature
- Link to feature-specific docs for details

**3.3 Clang Printer Integration**
- DeclPrinter/StmtPrinter usage
- PrintingPolicy configuration for C99
- #line directive injection
- Precedence and formatting (handled by Clang)

**3.4 Runtime Library**
- Mermaid component diagram showing runtime modules:
  - exception_runtime.c (PNaCl SJLJ)
  - rtti_runtime.c (type_info + dynamic_cast)
  - vtable_runtime.c (virtual function dispatch)
  - memory_runtime.c (RAII + smart pointers)
- Size estimates: 1.7-2.8 KB compiled
- API surface (link to [docs/architecture/runtime-library-design.md](docs/architecture/runtime-library-design.md) for full spec)

#### 4. Feature Implementation Architecture

For each major feature, provide:
- Transformation approach (C++ → C)
- Key data structures
- Mermaid diagram (appropriate type: flow for transformations, structure for layouts)
- Minimal illustrative code (if essential)
- Link to detailed implementation guide

**4.1 Exception Handling**
- PNaCl SJLJ pattern overview
- Mermaid sequence diagram: throw → setjmp/longjmp → catch
- Thread-local frame stack
- Action tables for destructors
- Link to [docs/features/exceptions.md](docs/features/exceptions.md)

**4.2 RTTI (Runtime Type Information)**
- Itanium ABI pattern
- type_info structure (Mermaid entity diagram)
- dynamic_cast algorithm (Mermaid flowchart)
- Class hierarchy tables
- Link to [docs/features/rtti.md](docs/features/rtti.md)

**4.3 Virtual Inheritance**
- VTT (Virtual Table Tables) concept
- Diamond problem resolution (Mermaid diagram)
- Virtual base offset tables
- Memory layout (Mermaid diagram)
- Link to [docs/features/virtual-inheritance.md](docs/features/virtual-inheritance.md)

**4.4 C++20 Coroutines**
- State machine transformation
- Coroutine frame layout (Mermaid structure)
- Suspend/resume mechanics (Mermaid state diagram)
- Promise type translation
- Link to [docs/features/coroutines.md](docs/features/coroutines.md)

**4.5 Other Features (Brief)**
- Classes & Inheritance (vtables, vptrs)
- Templates (STL self-bootstrapping)
- RAII (CFG-based destructor injection)
- Lambdas (struct + function pointer)
- Smart Pointers (reference counting)

#### 5. Data Flow & Transformations

**5.1 AST Transformation Patterns**
- Mermaid flowchart showing common transformation patterns:
  - Expression transformation (CXXThrowExpr → CallExpr)
  - Statement transformation (CXXTryStmt → IfStmt + setjmp)
  - Declaration transformation (CXXRecordDecl → struct + functions)

**5.2 Name Mangling**
- Purpose and strategy
- Itanium ABI mangling scheme
- Collision avoidance

**5.3 Memory Layout**
- Class layout with single inheritance
- Multiple inheritance layout
- Virtual inheritance layout (link to virtual-inheritance.md)

#### 6. Implementation Roadmap

Synthesize from [docs/feasibility-and-roadmap.md](docs/feasibility-and-roadmap.md):

- Mermaid Gantt chart for 5 implementation phases
- Phase 1: POC (3-4 weeks) - deliverables
- Phase 2: Core Features (4-8 weeks) - deliverables
- Phase 3: Advanced Features (8-12 weeks) - deliverables
- Phase 4: Expert Features (8-12 weeks) - deliverables
- Phase 5: Production Hardening (4-8 weeks) - deliverables

#### 7. Technology Stack

- **Parser:** Clang LibTooling (AST access, semantic analysis)
- **Build:** CMake 3.20+, C++17
- **Target:** C99 output
- **Verification:** Frama-C
- **References:** Itanium C++ ABI, PNaCl specifications

#### 8. Design Principles & Trade-offs

Synthesize key principles:
- Type safety first (strongly-typed C output)
- Code quality over implementation simplicity (80% cleaner output worth 40% more implementation)
- Frama-C tractability (verify library once, not every function)
- Battle-tested components (Clang printer over custom)

#### 9. Appendices

**A. Glossary**
- AST, RecursiveASTVisitor, TreeTransform, DeclPrinter, StmtPrinter
- VTT, RTTI, SJLJ, PNaCl
- Itanium ABI, Frama-C

**B. References**
- Link to all docs/ files
- External references (Clang docs, Itanium ABI, PNaCl)
- Commercial validation (emmtrix eCPP2C)

## Output Specification

### Primary Output

**File:** `docs/ARCHITECTURE.md`

**Format:**
- Markdown with Mermaid diagrams
- Extensive use of headings and subheadings
- Link-heavy (prefer links to lengthy quotes)
- Diagrams for all major concepts
- Minimal code snippets (only when essential)

**Diagram Guidelines:**
- Use appropriate Mermaid diagram types:
  - `graph TD` / `flowchart TD` for data flow, pipelines, transformations
  - `classDiagram` for component APIs, data structures
  - `sequenceDiagram` for interactions, call flows
  - `stateDiagram-v2` for state machines (coroutines)
  - `gantt` for implementation timeline
  - `C4Context` / architecture blocks for high-level system view
- Keep diagrams focused (one concept per diagram)
- Use descriptive labels and notes
- Ensure diagrams are readable without referring to text

**Linking Strategy:**
- Link to docs/ files for detailed explanations
- Link to specific sections when possible (e.g., `docs/features/exceptions.md#action-tables`)
- Use descriptive link text (not "click here")
- Provide context before links ("For the complete SJLJ implementation pattern, see [Exception Handling Guide](docs/features/exceptions.md)")

**Code Snippet Guidelines:**
- Use sparingly (diagrams preferred)
- Keep snippets under 10 lines
- Focus on API usage patterns, not implementations
- Prefer pseudocode to actual C/C++ when illustrating concepts

### SUMMARY.md

**File:** `.prompts/001-technical-architecture-doc-do/SUMMARY.md`

**Required sections:**

**One-liner:** Substantive description of what was accomplished (not "Architecture document created")

**Version:** v1.0

**Key Findings:**
- Number of pages in ARCHITECTURE.md
- Number of Mermaid diagrams created
- Key architectural insights surfaced
- Coverage of components and features

**Files Created:**
- List all created/modified files with descriptions

**Decisions Needed:**
- Any architectural ambiguities requiring user input
- Trade-offs that need stakeholder approval

**Blockers:**
- Missing research (if any)
- Unclear specifications

**Next Step:**
- Concrete action (e.g., "Review ARCHITECTURE.md for accuracy", "Begin Phase 1 POC implementation")

## Success Criteria

**Completeness:**
- ✓ All 9 major sections present
- ✓ All 4 feature implementations covered
- ✓ Implementation roadmap synthesized
- ✓ Mermaid diagrams for all major concepts (minimum 10 diagrams)

**Quality:**
- ✓ Self-contained executive overview (can read in 5 minutes)
- ✓ Implementation-focused (provides actionable guidance)
- ✓ Visual clarity (diagrams explain, text supplements)
- ✓ Hybrid linking (critical content synthesized, details linked)

**Usability:**
- ✓ Clear navigation (ToC, section headers)
- ✓ Appropriate diagram types for each concept
- ✓ Links work and provide context
- ✓ Code snippets are minimal and illustrative

**Technical Accuracy:**
- ✓ Correctly represents Two-Phase Translation architecture
- ✓ Accurately synthesizes research findings
- ✓ Links to source documents for verification
- ✓ No contradictions with research docs

## Execution Notes

**Reading Strategy:**
1. Start with docs/SUMMARY.md for context
2. Read docs/architecture/architecture-decision.md for core rationale
3. Skim other docs/ files to understand scope
4. Deep-read sections relevant to each architecture section
5. Extract key points, create diagrams, synthesize content

**Diagram Creation:**
- Use Mermaid live editor to validate syntax: https://mermaid.live
- Test complex diagrams before embedding
- Use notes and annotations for clarity

**Writing Approach:**
- Write executive overview last (after understanding full scope)
- Create diagrams first, then write text to explain them
- Maintain consistent terminology (match research docs)
- Use active voice, present tense ("The Translation Layer transforms...")

**Link Management:**
- Use relative links (docs/features/exceptions.md not absolute paths)
- Test all links (files must exist)
- Provide link context ("see X for Y" not just "see X")

---

**Generated:** 2025-12-08
**Purpose:** Create comprehensive technical architecture document
**Target:** docs/ARCHITECTURE.md
**Approach:** Synthesize research, diagram-heavy, implementation-focused
