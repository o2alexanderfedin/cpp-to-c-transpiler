# C++ to C Transpiler Architecture

## Critical: The Transpiler Pipeline

The transpiler operates as a **3-stage pipeline** where each stage is independent and can be tested separately:

### Stage 1: C++ AST Generation (Clang Frontend)
- **Input**: C++ source files
- **Process**: Clang frontend parses C++ code
- **Output**: C++ AST (Abstract Syntax Tree)
- **Responsibility**: Parsing and semantic analysis of C++

### Stage 2: C++ AST → C AST Translation (CppToCVisitor)
- **Input**: C++ AST from Stage 1
- **Process**: Walk through C++ AST using RecursiveASTVisitor
- **Output**: C AST representing equivalent C code
- **Responsibility**:
  - Decide how to represent C++ constructs in C
  - Transform classes to structs
  - Transform methods to functions with explicit `this` parameter
  - Transform scoped enums to prefixed enum constants
  - Transform constructors to initialization functions
  - Build complete C AST nodes using CNodeBuilder
- **Key Point**: This stage creates C AST nodes, NOT text output

### Stage 3: C Code Emission (CodeGenerator)
- **Input**: C AST from Stage 2
- **Process**: Walk through C AST with a dedicated visitor
- **Output**: C source files (.h and .c)
- **Responsibility**:
  - Visit C AST nodes and emit text representation
  - Manage output file generation (header vs implementation)
  - Handle C syntax formatting
  - **Important**: Should NOT make translation decisions, only emit what's in C AST

## Pipeline Separation Principles

1. **Stage 1 and 2 are separate**: CppToCVisitor receives C++ AST, doesn't control parsing
2. **Stage 2 and 3 are separate**: CppToCVisitor creates C AST, doesn't emit text
3. **Each stage is testable**: Can unit test C AST creation independently of text emission

## Current Architecture Issues

The current implementation violates the pipeline separation in CodeGenerator (Stage 3):
- `printExpr()` makes translation decisions (e.g., converting `GameState::Menu` to `GameState__Menu`)
- This is WRONG - translation should happen in CppToCVisitor (Stage 2)
- CodeGenerator should only emit what's already in the C AST

## Correct Approach

**CppToCVisitor (Stage 2)** should:
- Translate `GameState::Menu` (C++ EnumConstantDecl) to `GameState__Menu` (C EnumConstantDecl)
- Create DeclRefExpr pointing to the C EnumConstantDecl with correct name
- Create CallExpr for translated method calls
- Store all translated nodes in C AST

**CodeGenerator (Stage 3)** should:
- Simply emit the name from EnumConstantDecl: `ECD->getNameAsString()`
- Simply emit the function name from CallExpr
- No translation logic, just text generation

## Testing Strategy

Each stage should be testable:
1. **Test Stage 1**: Verify C++ AST is correct
2. **Test Stage 2**: Verify C AST has correct structure and names (without emitting text)
3. **Test Stage 3**: Verify C code emission matches C AST (without translation logic)

## Remember

- **We do NOT use LLVM IR** - only Clang frontend for parsing
- **Pipeline: C++ source → C++ AST → C AST → C source**
- **Each stage is independent and testable**
- **Translation decisions belong in Stage 2, NOT Stage 3**

## Refactoring Recommendations

### Current Issues

**CppToCVisitor Violates Single Responsibility**:
- Handles AST traversal, expression translation, statement translation
- Manages method mapping, template monomorphization, destructor injection
- Mixes concerns: file organization, declaration filtering, code generation prep
- Result: "Magic servlet" anti-pattern - hard to understand, test, and maintain

### Recommended Architecture: Chain of Responsibilities

Split CppToCVisitor into specialized handlers:

1. **FileOriginFilter**: Determines which AST nodes belong to current file
2. **EnumTranslator**: Handles enum → C enum translation
3. **ClassToStructTranslator**: Handles class → struct transformation
4. **MethodToFunctionTranslator**: Handles method → function with `this` parameter
5. **ExpressionTranslator**: Handles all expression translations
6. **StatementTranslator**: Handles all statement translations
7. **TemplateMonomorphizer**: Handles template instantiation (already exists)
8. **TranslationOrchestrator**: Coordinates the chain, manages C_TU

Each handler:
- Has ONE clear responsibility (SRP)
- Is independently testable
- Can be extended without modifying others (OCP)
- Has well-defined inputs/outputs

### Implementation Strategy

1. **Get to 100% pass rate** with current architecture
2. **Write integration tests** for all 5 validation cases
3. **Refactor incrementally**:
   - Extract one handler at a time
   - Tests ensure no regression
   - Each extraction is a separate commit
4. **Document each handler** with clear contracts

### Benefits

- **Easier debugging**: Each handler's logic is isolated
- **Better testability**: Unit test individual translators
- **Clearer code**: Each file has one purpose
- **Easier onboarding**: New developers can understand one handler at a time
- **SOLID compliance**: Proper separation of concerns
