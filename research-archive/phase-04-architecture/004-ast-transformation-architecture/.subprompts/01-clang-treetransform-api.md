# Research Task: Clang TreeTransform API Analysis

## Objective
Investigate Clang's TreeTransform API for type-safe AST transformations. Document capabilities, limitations, and provide working code examples.

## Research Questions
1. How does TreeTransform<Derived> work?
2. What AST node types can be transformed?
3. Can we inject new statements into AST?
4. Can we create new declarations?
5. What are the limitations?

## Deliverables
1. API documentation with code examples (500+ lines)
2. Working prototype: simple transformation (e.g., replace CXXThrowExpr)
3. List of transformable vs non-transformable nodes
4. Assessment: feasibility for C++ to C conversion

## Sources
- Clang TreeTransform.h documentation
- Clang source code examples
- Existing transformer implementations
- LLVM documentation

## Output File
`.prompts/004-ast-transformation-architecture/research-notes/01-treetransform-api.md`
