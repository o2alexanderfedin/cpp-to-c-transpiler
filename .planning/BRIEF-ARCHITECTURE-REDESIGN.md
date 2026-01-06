# C++ to C Transpiler: Ground-Up Architecture Redesign

## Vision

Build a properly architected C++ to C transpiler based on **Chain of Responsibilities** pattern, where each C++ AST node type has its own specialized handler. Start from the simplest constructions and gradually build up to sophisticated features.

## Current State

The existing transpiler (`CppToCVisitor`) is a "magic servlet" anti-pattern - one massive class handling all AST traversal, translation, mapping, template monomorphization, and more. This violates SOLID principles and makes testing, debugging, and maintenance extremely difficult.

## Problem

We're trying to race in Formula-1 with a half-assembled car:
- No clear separation between C++ AST → C AST translation and C code emission
- Translation decisions scattered throughout the codebase
- Difficult to unit test individual transformations
- Hard to add new C++ feature support
- No systematic progression from simple to complex features

## Solution

**Phase 1: Research**
- Catalog all C++ AST nodes in Clang
- Understand the node hierarchy and relationships
- Identify which nodes are needed for basic C++ features

**Phase 2: Architecture Design**
- Design Chain of Responsibilities pattern for translation
- Create detailed architecture documents with Mermaid diagrams
- Define clear interfaces between components
- Plan the 3-stage pipeline: C++ AST → C AST → C code

**Phase 3: Implementation Plan**
- Create step-by-step implementation plan
- Start with simplest C++ constructions:
  - Functions (standalone, no classes)
  - Variables (local, global)
  - Arithmetic expressions
  - Flow control (if/else, while, for, switch)
- Gradually add complexity:
  - Structs (without methods)
  - Functions with structs
  - Classes (with methods)
  - Inheritance
  - Templates
  - Advanced features

**Phase 4: Unit-Tested Implementation**
- Each handler gets comprehensive unit tests BEFORE implementation (TDD)
- Test C++ AST → C AST transformation independently from code emission
- Surgical precision - examine each transformation thoroughly

## Success Criteria

1. **Architecture documents** with:
   - Complete C++ AST node catalog
   - Mermaid diagrams showing handler chain
   - Clear interface definitions
   - Progressive complexity roadmap

2. **Implementation plan** that:
   - Starts with primitives (functions, variables, expressions)
   - Each step is independently testable
   - Complexity increases gradually
   - Every handler is unit-tested before integration

3. **Clean separation**:
   - Stage 1: Clang frontend → C++ AST (existing)
   - Stage 2: Handler chain → C AST (new architecture)
   - Stage 3: Code generator → C files (simplified)

4. **SOLID compliance**:
   - Single Responsibility: Each handler does ONE thing
   - Open/Closed: Easy to add new handlers without modifying existing
   - Liskov Substitution: Handlers are interchangeable
   - Interface Segregation: Clean, minimal interfaces
   - Dependency Inversion: Depend on abstractions, not concretions

## Non-Goals (for initial architecture)

- NOT fixing existing bugs in current implementation
- NOT achieving 100% pass rate on current tests (those tests validate broken architecture)
- NOT preserving backward compatibility with current implementation

## Timeline Approach

No time estimates. Focus on:
1. Get research complete
2. Get architecture documented
3. Get implementation plan detailed
4. Start implementing from simplest features

Each phase completes when its artifacts are done, tested, and reviewed.
