# Research Note: Existing Clang Transformation Tools Analysis

**Research Date:** 2025-12-08
**Purpose:** Learn from production tools (clang-tidy, clang-refactor)

---

## Executive Summary

**Key Finding:** Production Clang tools (clang-tidy, clang-refactor) use **AST Matchers + Rewriter** for transformations, NOT TreeTransform.

**Pattern Identified:** AST Matchers (find nodes) + Rewriter (modify source) + FixItHints (apply changes)

**Lesson:** Simple, text-based transformation works better than complex AST manipulation for production tools.

**Relevance to C++ to C:** Confirms direct code generation approach is correct. Production tools avoid complex AST transformation.

---

## clang-tidy Architecture

### What is clang-tidy?

> A clang-based C++ "linter" tool providing an extensible framework for diagnosing and fixing typical programming errors.

### Architecture Pattern:

```
C++ Source
    ↓
Clang AST
    ↓
AST Matchers (find problematic patterns)
    ↓
Checks (analyze matched nodes)
    ↓
FixItHints (text-based replacements via Rewriter)
    ↓
Modified Source
```

### Key Components:

**1. AST Matchers**
```cpp
// Find function calls matching pattern
void registerMatchers(ast_matchers::MatchFinder *Finder) {
    Finder->addMatcher(
        callExpr(callee(functionDecl(hasName("old_api")))).bind("call"),
        this);
}
```

**2. Check Implementation**
```cpp
void check(const MatchFinder::MatchResult &Result) {
    const auto *Call = Result.Nodes.getNodeAs<CallExpr>("call");

    // Emit diagnostic with fix
    diag(Call->getBeginLoc(), "use new API instead")
        << FixItHint::CreateReplacement(Call->getSourceRange(),
                                         "new_api()");
}
```

**3. FixItHint (uses Rewriter internally)**
- `CreateInsertion` → Insert text
- `CreateReplacement` → Replace text
- `CreateRemoval` → Remove text

### Transformation Strategy: TEXT-BASED

**Critical Observation:** clang-tidy does NOT use TreeTransform!

It uses:
- AST Matchers to FIND nodes
- Rewriter to MODIFY source text
- NO AST node creation or modification

**Why?**
- Simpler
- More reliable
- Sufficient for refactoring
- Production-proven

---

## clang-refactor Architecture

### What is clang-refactor?

> Clang's official refactoring engine providing rename, extract function, and other refactorings.

### Architecture:

```
RefactoringAction
    ↓
createRefactoringActionRule()
    ↓
AtomicChange (based on Rewriter concepts)
    ↓
Apply text changes
```

### Key Class: AtomicChange

From documentation:
> AtomicChange represents a set of source changes to a single file. It maintains a  string-based representation of file content.

```cpp
class AtomicChange {
    // Insert text
    void insert(unsigned Offset, StringRef Text);

    // Replace text
    void replace(unsigned Offset, unsigned Length, StringRef Text);

    // Based on Rewriter concepts!
};
```

### Transformation Strategy: TEXT-BASED

**Again:** clang-refactor uses text-based changes, NOT AST transformation!

---

## CoARCT: Code Analysis and Refactoring with Clang Tools

### What is CoARCT?

From GitHub (LANL):
> Demonstrates sustained examples of refactoring and analyzing code with AST Matchers and the clang Refactoring Tool.

### Architecture:

Uses same pattern:
1. AST Matchers to find nodes
2. Rewriter to apply changes
3. Text-based transformations

### Example Refactorings:

- Replace function calls
- Update variable types
- Modify control flow
- Add/remove code

**All done via text replacements!**

---

## Pattern Analysis: Why Text-Based Wins

### Common Pattern Across All Tools:

```cpp
// 1. FIND with AST Matchers or RecursiveASTVisitor
bool VisitCallExpr(CallExpr *E) {
    if (needsTransformation(E)) {
        found_nodes.push_back(E);
    }
}

// 2. ANALYZE
for (CallExpr *E : found_nodes) {
    analyze(E);
}

// 3. MODIFY with text operations
for (CallExpr *E : found_nodes) {
    rewriter.ReplaceText(E->getSourceRange(), generateNewCode(E));
}
```

### Why This Pattern Works:

**1. Separation of concerns:**
- Analysis: AST level (semantic understanding)
- Modification: Text level (simple and reliable)

**2. No AST complexity:**
- No need to create AST nodes
- No need to maintain AST consistency
- No Sema dependency for modification

**3. Flexibility:**
- Can generate arbitrary text
- Not limited by AST node types
- Easy to implement complex transformations

**4. Reliability:**
- Text operations are simple
- Less chance of breaking Clang invariants
- Proven in production

---

## Comparison: Production Tools vs TreeTransform

| Aspect | Production Tools | TreeTransform |
|--------|------------------|---------------|
| **Finding Nodes** | AST Matchers / RecursiveASTVisitor | TreeTransform traversal |
| **Modification** | Text-based (Rewriter) | AST node manipulation |
| **New Node Creation** | N/A (text) | Cumbersome |
| **Complexity** | LOW | HIGH |
| **Flexibility** | HIGH | LIMITED |
| **Reliability** | HIGH (proven) | MEDIUM (complex) |
| **Use in Tools** | clang-tidy, clang-refactor, CoARCT | Rarely used |

---

## Key Lessons for C++ to C Converter

### Lesson 1: Analyze at AST Level, Generate at Text Level

**What production tools do:**
```cpp
// Analyze: AST
bool VisitFunctionDecl(FunctionDecl *F) {
    FunctionInfo info = analyzeFunctionDecl(F);
    function_infos.push_back(info);
}

// Generate: Text
for (const FunctionInfo &info : function_infos) {
    std::string c_code = generateCFunction(info);
    writeToFile(c_code);
}
```

**This is the right pattern!**

### Lesson 2: Don't Try to Modify AST

Production tools teach us:
- AST is for ANALYSIS
- Text is for GENERATION
- Don't mix the two

**For C++ to C converter:**
- Use AST to understand C++ code
- Generate C code as text
- Don't try to "transform" AST to C AST

### Lesson 3: Simple is Better

clang-tidy could use TreeTransform but doesn't. Why?
- Text-based is simpler
- Text-based is more reliable
- Text-based is sufficient

**For C++ to C converter:**
- Direct text generation is simpler than AST transformation
- Proven approach from production tools

### Lesson 4: Custom Generation for Custom Needs

Production tools generate text because they need:
- Arbitrary code patterns
- Not limited by AST expressiveness
- Full control over output

**C++ to C converter needs:**
- Custom name mangling
- Custom struct layouts
- Custom vtable generation
- Full control over C output

**Conclusion:** Direct text generation is the right approach.

---

## AST Matchers vs RecursiveASTVisitor

### AST Matchers (clang-tidy's approach):

```cpp
// Declarative pattern matching
Finder->addMatcher(
    cxxRecordDecl(
        hasName("MyClass"),
        has(cxxMethodDecl(isVirtual()))
    ).bind("class"),
    this);
```

**Pros:**
- Declarative and concise
- Good for finding specific patterns
- Composable

**Cons:**
- Learning curve
- Overkill for comprehensive traversal

### RecursiveASTVisitor (simpler approach):

```cpp
// Imperative traversal
bool VisitCXXRecordDecl(CXXRecordDecl *R) {
    // Process every class
    processClass(R);
    return true;
}
```

**Pros:**
- Straightforward
- Good for comprehensive analysis
- Simple to understand

**Cons:**
- More verbose for specific patterns

### Recommendation for C++ to C Converter:

**Use RecursiveASTVisitor:**
- Need comprehensive analysis (every class, function, etc.)
- Simpler for full translation
- Don't need complex pattern matching

**Use AST Matchers:**
- Only if needed for specific patterns
- Could be useful for finding specific C++ constructs

**Primary tool: RecursiveASTVisitor**

---

## ModulariImplementation Pattern from clang-tidy

### Check Structure:

```cpp
class MyCheck : public ClangTidyCheck {
public:
    // Register what to look for
    void registerMatchers(MatchFinder *Finder) override;

    // Handle found nodes
    void check(const MatchFinder::MatchResult &Result) override;

private:
    // Helper functions
    std::string generateFix(const Expr *E);
};
```

### Applied to C++ to C Converter:

```cpp
class CppFeatureConverter {
public:
    // Register visitor
    void registerVisitor(RecursiveASTVisitor &Visitor);

    // Convert specific feature
    void convert(ASTContext &Context, CCodeEmitter &Emitter);

private:
    // Helper functions
    std::string generateCCode(const Decl *D);
};
```

**Modularity Benefits:**
- Each feature has own converter
- Easy to test individually
- Clear separation of concerns

---

## External Clang-Tidy Modules Pattern

From search results:
> "Modern usage allows loadable clang-tidy modules"

### Plugin Architecture:

```cpp
// Define check
class MyCppToC Check : public ClangTidyCheck {
    // ... implementation
};

// Register check
static ClangTidyModuleRegistry::Add<MyCppToCModule>
X("cpptoc", "C++ to C converter module");
```

### Applied to C++ to C Converter:

**Could implement as clang-tidy module:**
- Pros: Reuse clang-tidy infrastructure
- Cons: Not really a "tidy" check, full transpiler

**Better:** Standalone tool using LibTooling
- More appropriate for transpiler
- Full control over output
- Not bound by clang-tidy conventions

---

## Development Workflow from Microsoft Tutorial

### Recommended Workflow:

1. **Prototype with clang-query:**
   ```bash
   clang-query input.cpp --
   clang-query> match functionDecl()
   ```

2. **Develop with unit tests:**
   ```cpp
   TEST(CppToCConverter, ConvertSimpleClass) {
       std::string input = "class Foo { int x; };";
       std::string expected = "struct Foo { int x; };";
       EXPECT_EQ(convert(input), expected);
   }
   ```

3. **Refine with real code:**
   - Test on actual C++ projects
   - Handle edge cases
   - Improve generated code quality

**Applied to C++ to C Converter:**
- Use clang-query for exploring AST
- Write comprehensive unit tests
- Iterate on generated code quality

---

## Final Assessment

### What We Learned from Production Tools

**1. Architecture Pattern:**
- ✅ AST for analysis
- ✅ Text for generation
- ❌ NOT AST transformation

**2. Tools Used:**
- ✅ RecursiveASTVisitor or AST Matchers
- ✅ Rewriter for text operations
- ❌ NOT TreeTransform

**3. Implementation Strategy:**
- ✅ Simple text-based transformations
- ✅ Modular converter components
- ✅ Comprehensive testing

### Application to C++ to C Converter

**Architecture:**
```
C++ Source
    ↓
Clang Parse
    ↓
AST
    ↓
RecursiveASTVisitor (analyze)
    ↓
CCodeEmitter (generate text)
    ↓
C Source + Headers
```

**This matches production tool patterns!**

---

## Conclusion

**Production Clang tools validate our architectural decision:**

The evidence is clear:
1. **clang-tidy uses text-based transformation** (Rewriter, FixItHints)
2. **clang-refactor uses text-based transformation** (AtomicChange)
3. **CoARCT uses text-based transformation** (AST Matchers + Rewriter)
4. **NONE use TreeTransform for production transformations**

**Key Takeaway:** The most successful, widely-used Clang transformation tools use:
- AST for analysis
- Text generation for output
- NOT AST node creation/modification

**Recommendation:** Our planned architecture (RecursiveASTVisitor + direct C generation) is **validated by production tools**. This is the proven, reliable approach.

---

## References

1. [Microsoft: Exploring Clang Tooling Part 3: Rewriting Code with clang-tidy](https://devblogs.microsoft.com/cppblog/exploring-clang-tooling-part-3-rewriting-code-with-clang-tidy/)
2. [Clang's refactoring engine documentation](https://clang.llvm.org/docs/RefactoringEngine.html)
3. [Microsoft: Exploring Clang Tooling Part 1: Extending Clang-Tidy](https://devblogs.microsoft.com/cppblog/exploring-clang-tooling-part-1-extending-clang-tidy/)
4. [GitHub: lanl/CoARCT - Code Analysis and Refactoring with Clang Tools](https://github.com/lanl/CoARCT)
5. [Eli Bendersky: AST matchers and Clang refactoring tools](https://eli.thegreenplace.net/2014/07/29/ast-matchers-and-clang-refactoring-tools)
