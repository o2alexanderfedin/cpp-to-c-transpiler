# Research Note: ASTConsumer and ASTFrontendAction Analysis

**Research Date:** 2025-12-08
**Purpose:** Understanding Clang's plugin architecture for transformation passes

---

## Executive Summary

**Verdict:** ASTConsumer and ASTFrontendAction provide the **standard integration point** for Clang-based tools. They are the **correct architecture** for implementing a C++ to C converter.

**Key Finding:** Almost all Clang tools (clang-tidy, clang-refactor, custom analyzers) use ASTConsumer/ASTFrontendAction. This is the proven pattern.

**Recommendation:** **USE THIS ARCHITECTURE** for the C++ to C converter. It's the standard, well-documented approach.

---

## Architecture Overview

### The Three-Layer Pattern

```
User Tool (main.cpp)
    ↓
ASTFrontendAction (creates consumer)
    ↓
ASTConsumer (handles AST)
    ↓
RecursiveASTVisitor (traverses nodes)
```

**This is the standard pattern used by ALL Clang tools.**

---

## Component 1: ASTConsumer

### What is ASTConsumer?

From Clang documentation:

> ASTConsumer is an abstract interface that should be implemented by clients that read ASTs. This abstraction layer insulates the client from having to know the AST for a specific language.

**Key Methods:**

```cpp
class ASTConsumer {
public:
    // Called when AST parsing is initialized
    virtual void Initialize(ASTContext &Context) {}

    // Called for each top-level declaration
    virtual bool HandleTopLevelDecl(DeclGroupRef D) { return true; }

    // Called after entire translation unit is parsed
    virtual void HandleTranslationUnit(ASTContext &Ctx) {}

    // Called at end of source file
    virtual void HandleTranslationUnitDecl(ASTContext &Ctx) {}
};
```

### Typical Implementation:

```cpp
class MyCppToCConsumer : public ASTConsumer {
    ASTContext *context;

public:
    // Initialize with ASTContext
    void Initialize(ASTContext &Context) override {
        context = &Context;
    }

    // Process each top-level declaration as it's parsed
    bool HandleTopLevelDecl(DeclGroupRef DG) override {
        for (DeclGroupRef::iterator i = DG.begin(), e = DG.end();
             i != e; ++i) {
            const Decl *D = *i;
            // Process declaration
            if (const FunctionDecl *FD = dyn_cast<FunctionDecl>(D)) {
                processFunctionDecl(FD);
            }
        }
        return true; // Continue parsing
    }

    // Process entire translation unit after parsing complete
    void HandleTranslationUnit(ASTContext &Context) override {
        // Use RecursiveASTVisitor for full traversal
        MyVisitor visitor(Context);
        visitor.TraverseDecl(Context.getTranslationUnitDecl());

        // Generate C code
        generateCCode();
    }
};
```

---

## Component 2: ASTFrontendAction

### What is ASTFrontendAction?

From Clang documentation:

> Almost all front end actions inherit from ASTFrontendAction, which means they work with the generated AST.

**Key Method:**

```cpp
class ASTFrontendAction {
public:
    // Create your custom ASTConsumer
    virtual std::unique_ptr<ASTConsumer>
    CreateASTConsumer(CompilerInstance &CI, StringRef InFile) = 0;
};
```

### Typical Implementation:

```cpp
class MyCppToCAction : public ASTFrontendAction {
public:
    std::unique_ptr<ASTConsumer>
    CreateASTConsumer(CompilerInstance &CI, StringRef File) override {
        // Create and return your consumer
        return std::make_unique<MyCppToCConsumer>();
    }
};
```

---

## Component 3: RecursiveASTVisitor Integration

### Full Integration Pattern:

```cpp
// 1. Define Visitor
class MyCppAnalyzer : public RecursiveASTVisitor<MyCppAnalyzer> {
    ASTContext &context;

public:
    explicit MyCppAnalyzer(ASTContext &C) : context(C) {}

    bool VisitFunctionDecl(FunctionDecl *F) {
        // Analyze function
        llvm::outs() << "Found function: " << F->getName() << "\n";
        return true;
    }

    bool VisitCXXRecordDecl(CXXRecordDecl *R) {
        // Analyze class
        llvm::outs() << "Found class: " << R->getName() << "\n";
        return true;
    }
};

// 2. Use Visitor in Consumer
class MyCppToCConsumer : public ASTConsumer {
public:
    void HandleTranslationUnit(ASTContext &Context) override {
        MyCppAnalyzer analyzer(Context);
        analyzer.TraverseDecl(Context.getTranslationUnitDecl());
    }
};

// 3. Create Consumer in Action
class MyCppToCAction : public ASTFrontendAction {
public:
    std::unique_ptr<ASTConsumer>
    CreateASTConsumer(CompilerInstance &CI, StringRef File) override {
        return std::make_unique<MyCppToCConsumer>();
    }
};
```

---

## Running Your Tool

### Method 1: Using LibTooling (Recommended)

```cpp
#include "clang/Tooling/CommonOptionsParser.h"
#include "clang/Tooling/Tooling.h"

static llvm::cl::OptionCategory ToolCategory("cpptoc options");

int main(int argc, const char **argv) {
    // Parse command line options
    auto ExpectedParser =
        clang::tooling::CommonOptionsParser::create(argc, argv, ToolCategory);

    if (!ExpectedParser) {
        llvm::errs() << ExpectedParser.takeError();
        return 1;
    }

    clang::tooling::CommonOptionsParser &OptionsParser = ExpectedParser.get();

    // Create tool with your action
    clang::tooling::ClangTool Tool(
        OptionsParser.getCompilations(),
        OptionsParser.getSourcePathList());

    // Run tool with your FrontendAction
    return Tool.run(
        clang::tooling::newFrontendActionFactory<MyCppToCAction>().get());
}
```

**Compile with:**
```bash
clang++ -std=c++17 \
    cpptoc.cpp \
    -I/path/to/llvm/include \
    -L/path/to/llvm/lib \
    -lclangTooling -lclangFrontend -lclangParse \
    -lclangSema -lclangAST -lclangBasic \
    -o cpptoc
```

**Run:**
```bash
./cpptoc input.cpp -- -std=c++17
```

### Method 2: Using Clang Plugin

```cpp
// Register as Clang plugin
#include "clang/Frontend/FrontendPluginRegistry.h"

static FrontendPluginRegistry::Add<MyCppToCAction>
X("cpptoc", "C++ to C converter");
```

**Load plugin:**
```bash
clang++ -Xclang -load -Xclang ./cpptoc.so \
        -Xclang -plugin -Xclang cpptoc \
        input.cpp
```

---

## Multi-Pass Architecture

### Supporting Multiple Transformation Passes

**Challenge:** Often need multiple passes over AST:
1. First pass: Collect type information
2. Second pass: Generate C code

**Solution: Multiple Consumers or Single Consumer with Multiple Visitors**

#### Option 1: Multiple Visitors in One Consumer

```cpp
class MyCppToCConsumer : public ASTConsumer {
public:
    void HandleTranslationUnit(ASTContext &Context) override {
        // Pass 1: Collect information
        InfoCollectorVisitor collector(Context);
        collector.TraverseDecl(Context.getTranslationUnitDecl());

        // Pass 2: Generate C code using collected info
        CCodeGeneratorVisitor generator(Context, collector.getInfo());
        generator.TraverseDecl(Context.getTranslationUnitDecl());
    }
};
```

#### Option 2: Multiple Actions (Complex)

```cpp
// Not common, but possible
// Run tool twice with different actions
```

**Recommendation:** Use Option 1 (multiple visitors in one consumer). Simpler and more efficient.

---

## Accessing Clang Infrastructure

### ASTContext

The `ASTContext` object provides access to all Clang infrastructure:

```cpp
void HandleTranslationUnit(ASTContext &Context) override {
    // Access source manager
    SourceManager &SM = Context.getSourceManager();

    // Access language options
    const LangOptions &LO = Context.getLangOpts();

    // Access type system
    QualType intType = Context.IntTy;

    // Access target information
    const TargetInfo &TI = Context.getTargetInfo();

    // Access diagnostics
    DiagnosticsEngine &Diags = Context.getDiagnostics();

    // Access translation unit decl
    TranslationUnitDecl *TU = Context.getTranslationUnitDecl();
}
```

### CompilerInstance

Available in `CreateASTConsumer`:

```cpp
std::unique_ptr<ASTConsumer>
CreateASTConsumer(CompilerInstance &CI, StringRef File) override {
    // Access source manager
    SourceManager &SM = CI.getSourceManager();

    // Access preprocessor
    Preprocessor &PP = CI.getPreprocessor();

    // Access file manager
    FileManager &FM = CI.getFileManager();

    // Create consumer with access to compiler infrastructure
    return std::make_unique<MyCppToCConsumer>(CI);
}
```

---

## State Management

### Passing Data Between Components

**Challenge:** Need to maintain state across visitor calls.

**Solution: Store state in Consumer**

```cpp
class MyCppToCConsumer : public ASTConsumer {
    // State storage
    std::vector<ClassInfo> classes;
    std::vector<FunctionInfo> functions;
    std::map<std::string, std::string> mangledNames;

    // Code generator
    CCodeEmitter emitter;

public:
    void HandleTranslationUnit(ASTContext &Context) override {
        // Pass 1: Collect info
        InfoCollectorVisitor collector(Context, classes, functions);
        collector.TraverseDecl(Context.getTranslationUnitDecl());

        // Generate mangled names
        generateMangledNames();

        // Pass 2: Generate C code
        CCodeGeneratorVisitor generator(Context, classes, functions,
                                         mangledNames, emitter);
        generator.TraverseDecl(Context.getTranslationUnitDecl());

        // Write output
        emitter.writeAllFiles();
    }

private:
    void generateMangledNames();
};
```

---

## Error Handling and Diagnostics

### Using Clang's Diagnostics System

```cpp
class MyCppToCConsumer : public ASTConsumer {
    DiagnosticsEngine *Diags;

public:
    void Initialize(ASTContext &Context) override {
        Diags = &Context.getDiagnostics();
    }

    void HandleTranslationUnit(ASTContext &Context) override {
        MyVisitor visitor(Context);

        // Example: emit warning
        unsigned DiagID = Diags->getCustomDiagID(
            DiagnosticsEngine::Warning,
            "C++ feature not supported in C conversion: %0");

        visitor.TraverseDecl(Context.getTranslationUnitDecl());
    }
};

// In visitor:
bool VisitCXXRecordDecl(CXXRecordDecl *R) {
    if (R->hasVirtualFunctions()) {
        // Emit diagnostic
        unsigned DiagID = context.getDiagnostics().getCustomDiagID(
            DiagnosticsEngine::Warning,
            "Class with virtual functions requires vtable generation");

        context.getDiagnostics().Report(R->getLocation(), DiagID);
    }
    return true;
}
```

---

## Practical Examples from Production Tools

### clang-tidy Architecture

```cpp
// ClangTidyCheck is essentially an ASTConsumer
class MyCheck : public ClangTidyCheck {
public:
    void registerMatchers(ast_matchers::MatchFinder *Finder) override {
        // Register AST matchers
    }

    void check(const ast_matchers::MatchFinder::MatchResult &Result) override {
        // Handle matched nodes
    }
};
```

**Key Point:** Even clang-tidy uses ASTConsumer pattern under the hood!

### clang-refactor Architecture

```cpp
// RefactoringAction uses ASTConsumer
class RenameAction : public RefactoringAction {
    std::unique_ptr<ASTConsumer>
    CreateASTConsumer(CompilerInstance &CI, StringRef InFile) override {
        // Return consumer that finds and renames symbols
        return std::make_unique<RenameConsumer>();
    }
};
```

---

## Performance Considerations

### Efficient AST Traversal

**Best Practice: Incremental Processing**

```cpp
class MyCppToCConsumer : public ASTConsumer {
public:
    // Process declarations as they're parsed (incremental)
    bool HandleTopLevelDecl(DeclGroupRef DG) override {
        for (Decl *D : DG) {
            // Process immediately
            // Memory can be freed after processing
            processDecl(D);
        }
        return true;
    }

    // OR: Process entire TU at once (simple but uses more memory)
    void HandleTranslationUnit(ASTContext &Context) override {
        // All AST nodes are in memory
        MyVisitor visitor(Context);
        visitor.TraverseDecl(Context.getTranslationUnitDecl());
    }
};
```

**Recommendation for C++ to C Converter:**
- Use `HandleTranslationUnit` for simplicity
- Need full AST for cross-reference analysis anyway
- Memory usage acceptable for typical source files

---

## Recommended Architecture for C++ to C Converter

### Complete Implementation Template:

```cpp
// File: CppToCConverter.h

class CppToCConverter {
    // Phase 1: Analysis
    class AnalysisVisitor : public RecursiveASTVisitor<AnalysisVisitor> {
        ASTContext &context;
        CppToCConverter &converter;

    public:
        AnalysisVisitor(ASTContext &C, CppToCConverter &Conv)
            : context(C), converter(Conv) {}

        bool VisitCXXRecordDecl(CXXRecordDecl *R);
        bool VisitFunctionDecl(FunctionDecl *F);
        bool VisitVarDecl(VarDecl *V);
    };

    // Phase 2: Code Generation
    class GeneratorVisitor : public RecursiveASTVisitor<GeneratorVisitor> {
        ASTContext &context;
        CppToCConverter &converter;
        CCodeEmitter &emitter;

    public:
        GeneratorVisitor(ASTContext &C, CppToCConverter &Conv,
                         CCodeEmitter &E)
            : context(C), converter(Conv), emitter(E) {}

        bool VisitCXXRecordDecl(CXXRecordDecl *R);
        bool VisitFunctionDecl(FunctionDecl *F);
    };

    // State
    std::vector<ClassInfo> classes;
    std::vector<FunctionInfo> functions;
    std::map<std::string, std::string> mangledNames;

    ASTContext *context;

public:
    // Called by Consumer
    void Convert(ASTContext &Context);

    // Accessors for visitors
    void addClass(const ClassInfo &info) { classes.push_back(info); }
    void addFunction(const FunctionInfo &info) { functions.push_back(info); }
};

// Consumer
class CppToCConsumer : public ASTConsumer {
    CppToCConverter converter;

public:
    void Initialize(ASTContext &Context) override {
        // Initialization if needed
    }

    void HandleTranslationUnit(ASTContext &Context) override {
        converter.Convert(Context);
    }
};

// Action
class CppToCAction : public ASTFrontendAction {
public:
    std::unique_ptr<ASTConsumer>
    CreateASTConsumer(CompilerInstance &CI, StringRef File) override {
        return std::make_unique<CppToCConsumer>();
    }
};

// Main
int main(int argc, const char **argv) {
    auto ExpectedParser =
        CommonOptionsParser::create(argc, argv, ToolCategory);

    if (!ExpectedParser) {
        llvm::errs() << ExpectedParser.takeError();
        return 1;
    }

    CommonOptionsParser &OptionsParser = ExpectedParser.get();
    ClangTool Tool(OptionsParser.getCompilations(),
                   OptionsParser.getSourcePathList());

    return Tool.run(newFrontendActionFactory<CppToCAction>().get());
}
```

---

## Comparison with Alternatives

| Approach | Pros | Cons |
|----------|------|------|
| **ASTConsumer + RecursiveASTVisitor** | ✅ Standard pattern<br>✅ Well-documented<br>✅ Full AST access<br>✅ Production-proven | ⚠️ Requires LibTooling<br>⚠️ More setup code |
| **TreeTransform** | ✅ Type-aware | ❌ Cumbersome<br>❌ Limited injection<br>❌ Not for source-to-source |
| **Rewriter** | ✅ Simple API | ❌ Text-only<br>❌ No code generation |
| **Direct C Generation (ours)** | ✅ Full control<br>✅ Clean output | ⚠️ More implementation work |

**Verdict:** Use **ASTConsumer + RecursiveASTVisitor + Direct C Generation**

---

## Final Assessment

### ASTConsumer/ASTFrontendAction for C++ to C Converter

**Strengths:**
- ✅ Standard Clang architecture
- ✅ Used by all production tools
- ✅ Well-documented with many examples
- ✅ Full access to Clang infrastructure
- ✅ Supports multi-pass analysis
- ✅ Efficient AST traversal
- ✅ Good error handling integration

**Weaknesses:**
- ⚠️ Requires LibTooling setup (acceptable)
- ⚠️ More boilerplate than simple script (acceptable)

### Recommendation: DEFINITELY USE THIS ARCHITECTURE

This is the **correct and proven way** to build Clang-based tools.

**Implementation Plan:**
1. Create `CppToCAction` inheriting from `ASTFrontendAction`
2. Create `CppToCConsumer` inheriting from `ASTConsumer`
3. Use `RecursiveASTVisitor` for AST traversal in Consumer
4. Generate C code directly (NOT via TreeTransform or Rewriter)
5. Integrate with LibTooling for command-line tool

---

## Conclusion

**ASTConsumer and ASTFrontendAction are the foundational architecture for any Clang-based tool.**

This pattern:
- Is used by clang-tidy, clang-refactor, and all major Clang tools
- Provides full access to Clang's AST and infrastructure
- Supports multi-pass analysis and generation
- Is well-documented with extensive examples
- Is the standard, proven approach

**Recommendation:** Build the C++ to C converter using this architecture with direct C code generation in the Consumer.

---

## References

1. [Clang: How to write RecursiveASTVisitor based ASTFrontendActions](https://clang.llvm.org/docs/RAVFrontendAction.html)
2. [Clang ASTFrontendAction Class Reference](https://clang.llvm.org/doxygen/classclang_1_1ASTFrontendAction.html)
3. [Daniel Beard: Clang frontend actions Part 1](https://danielbeard.io/2016/04/19/clang-frontend-action-part-1.html)
4. [Microsoft: Exploring Clang Tooling Part 1: Extending Clang-Tidy](https://devblogs.microsoft.com/cppblog/exploring-clang-tooling-part-1-extending-clang-tidy/)
5. [GitHub: eliben/llvm-clang-samples/tooling_sample.cpp](https://github.com/eliben/llvm-clang-samples/blob/master/src_clang/tooling_sample.cpp)
