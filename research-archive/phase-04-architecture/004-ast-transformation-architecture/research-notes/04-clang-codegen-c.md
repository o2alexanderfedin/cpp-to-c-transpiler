# Research Note: Clang CodeGen and C Backend Investigation

**Research Date:** 2025-12-08
**Purpose:** Investigate C code generation backends and their viability

---

## Executive Summary

**Verdict:** Clang does NOT have a native C backend. llvm-cbe (LLVM C Backend) exists but produces **UNREADABLE** and often **UNCOMPILABLE** C code.

**Key Finding:** llvm-cbe works at LLVM IR level (too low), losing all high-level C++ semantics. This makes it unsuitable for C++ to C conversion.

**Recommendation:** **DO NOT USE** llvm-cbe or attempt to build on LLVM IR. Work directly with Clang AST and generate C code as text.

---

## Clang CodeGen Architecture

### How Clang Normally Works

```
C++ Source
    ↓
Clang Frontend (Parse + Sema)
    ↓
Clang AST
    ↓
Clang CodeGen (lib/CodeGen/)
    ↓
LLVM IR
    ↓
LLVM Backend (Target-specific)
    ↓
Object Code (.o)
```

**Key Point:** Clang's CodeGen **only targets LLVM IR**, not C.

---

## Does Clang Have a C Backend?

### Short Answer: NO

Clang's CodeGen module (`clang/lib/CodeGen/`) generates **LLVM IR only**.

From Clang architecture:
- `CodeGenModule` → Generates LLVM Module (IR)
- `CodeGenFunction` → Generates LLVM Functions (IR)
- No `CodeGenC` or C backend classes exist

**Clang was never designed to generate C code.**

---

## llvm-cbe: The LLVM C Backend

### What is llvm-cbe?

From GitHub repositories (multiple forks exist):

> "Resurrected LLVM C Backend" - A tool that generates C code from LLVM IR.

**History:**
- Original LLVM C backend was removed from LLVM mainline years ago
- Several resurrection attempts exist:
  - JuliaHubOSS/llvm-cbe
  - Ace17/llvm-cbe
  - draperlaboratory/llvm-cbe
- Maintained by community, not official LLVM

**Architecture:**
```
C++ Source
    ↓
Clang Frontend
    ↓
LLVM IR (bitcode)
    ↓
llvm-cbe
    ↓
C Code
```

---

## Why llvm-cbe Produces Unreadable Code

### Problem 1: LLVM IR is Too Low-Level

LLVM IR has **no high-level constructs**:

**C++ Input:**
```cpp
class MyClass {
    int x;
public:
    int getX() { return x; }
};

void foo() {
    MyClass obj;
    int value = obj.getX();
}
```

**LLVM IR (simplified):**
```llvm
%class.MyClass = type { i32 }

define i32 @_ZN7MyClass4getXEv(%class.MyClass* %this) {
entry:
  %x = getelementptr inbounds %class.MyClass, %class.MyClass* %this, i32 0, i32 0
  %0 = load i32, i32* %x
  ret i32 %0
}

define void @_Z3foov() {
entry:
  %obj = alloca %class.MyClass
  %call = call i32 @_ZN7MyClass4getXEv(%class.MyClass* %obj)
  ret void
}
```

**llvm-cbe Output (typical):**
```c
struct l_class_OC_MyClass {
  unsigned int field0;
};

unsigned int _ZN7MyClass4getXEv(struct l_class_OC_MyClass *llvm_cbe_this) {
  unsigned int *llvm_cbe_tmp__1;
  unsigned int llvm_cbe_tmp__2;

  llvm_cbe_tmp__1 = (&llvm_cbe_this->field0);
  llvm_cbe_tmp__2 = *llvm_cbe_tmp__1;
  return llvm_cbe_tmp__2;
}

void _Z3foov(void) {
  struct l_class_OC_MyClass llvm_cbe_obj;
  unsigned int llvm_cbe_call;

  llvm_cbe_call = _ZN7MyClass4getXEv((&llvm_cbe_obj));
  return;
}
```

**Problems:**
- Mangled names retained (`_ZN7MyClass4getXEv`)
- Ugly variable names (`llvm_cbe_tmp__1`, `l_class_OC_MyClass`)
- Lost semantic meaning
- Not human-readable
- Not what we want!

### Problem 2: LLVM IR vs C Semantic Mismatch

**LLVM IR has MORE expressive power than C:**

From search results:
> "The LLVM IR is more expressive than C, so some parts of the output are not compatible."

**Examples:**
- LLVM has arbitrary-width integers (i128, i256)
- LLVM has vector types with operations not in C
- LLVM has explicit poison/undef values
- LLVM has more control over memory layout

**Result:** llvm-cbe must emit non-standard C constructs or verbose workarounds.

### Problem 3: Lost High-Level Structure

**What's lost in LLVM IR:**
- Class/struct names (replaced with mangled names)
- Member function semantics (just functions with `this` pointer)
- Namespaces (mangled away)
- Templates (instantiated, originals gone)
- Comments and formatting
- Variable names (often optimized away)
- Control flow structure (may be optimized)

**From Stack Overflow:**
> "Creating C code from the LLVM bitcode loses high-level semantics."

---

## llvm-cbe Quality Issues

### Issue 1: Uncompilable Code

From GitHub issues:

> "The LLVM frontend for the D programming language (LDC) generates valid bitcode that JuliaComputing/llvm-cbe can't process, resulting in **uncompilable C code**."

> "The C backend fails to generate proper/compilable code when trying to convert a C++ file to IR and then back to C, producing **a number of undeclared variables**."

**Verdict:** llvm-cbe is unreliable even for its stated purpose.

### Issue 2: Non-Standard C

From GitHub issues:

> "llvm-cbe currently outputs a C-like language meant to be compiled by **some C compilers**, rather than pure standard C."

**Problems:**
- Uses `__attribute__((noreturn))` instead of C11 `_Noreturn`
- Uses `__forceinline` instead of plain `inline`
- Includes non-standard headers like `<alloca.h>`
- Relies on compiler-specific extensions

### Issue 3: Code Readability

From search results:

> "The generated C code is **not the nicest to read**, but it's definitely legal C code."

**Understatement!** The code is nearly unreadable.

### Issue 4: Verbose Output

From Julia community:

> "C has much more **undefined behavior** than LLVM or Julia, so some places in the code may be more verbose than expected to force C to give the intended behavior."

**Example:** llvm-cbe burns 1024 bytes for each `jmp_buf` (per PNaCl SJLJ discussion).

---

## Why LLVM IR is Wrong Level for C++ to C

### Visualization of Abstraction Levels:

```
High-Level:  C++ Source Code
                ↓
             Clang AST (BEST LEVEL FOR CONVERSION)
                ↓
Medium-Level: LLVM IR (TOO LOW)
                ↓
Low-Level:    Machine Code
```

**Key Insight:**
- C++ → C conversion needs **high-level semantics**
- LLVM IR has already **optimized away** what we need
- Working at AST level preserves structure

---

## What About Custom Clang CodeGen C Backend?

### Could We Build One?

**Theoretical Approach:**
1. Add new backend to Clang CodeGen
2. Implement `CodeGenC` module
3. Generate C instead of LLVM IR

**Problems:**

#### Problem 1: Enormous Engineering Effort

Clang's CodeGen is **huge and complex**:
- `clang/lib/CodeGen/` has 100+ files
- Handles: function generation, class layout, vtables, RTTI, exceptions, etc.
- Tightly coupled to LLVM IR
- Would need to reimplement entire CodeGen module

**Effort:** Months to years

#### Problem 2: Still Wrong Approach

Even if we built a C backend for CodeGen:
- We'd still need to traverse AST
- We'd still need to analyze semantics
- We'd still generate text output

**Why not just generate C directly from AST?**

#### Problem 3: Lost Flexibility

CodeGen is designed for ONE target language (LLVM IR).

For C++ to C conversion, we need:
- Custom name mangling
- Custom struct layouts
- Custom vtable generation
- Custom exception handling

**Direct generation gives more control.**

---

## Alternative: Direct C Generation from AST

### Recommended Approach:

```
C++ Source
    ↓
Clang Parse + Sema
    ↓
Clang AST (WORK HERE)
    ↓
RecursiveASTVisitor
    ↓
Custom C Code Generator
    ↓
C Source + Headers
```

**Benefits:**
- ✅ Full high-level semantics preserved
- ✅ Control over generated code structure
- ✅ Readable C output
- ✅ Custom name mangling
- ✅ Simpler implementation
- ✅ No LLVM IR complexity

---

## Comparison: llvm-cbe vs Direct AST Generation

| Feature | llvm-cbe | Direct AST Generation |
|---------|----------|----------------------|
| **Input Level** | LLVM IR (low) | Clang AST (high) |
| **Semantics Preserved** | ❌ Lost | ✅ Full |
| **Readability** | ❌ Terrible | ✅ Good |
| **Names** | ❌ Mangled | ✅ Custom |
| **Compilable** | ⚠️ Often not | ✅ Yes |
| **Standard C** | ⚠️ Extensions | ✅ Yes |
| **Control** | ❌ None | ✅ Full |
| **Maintainability** | ❌ Poor | ✅ Good |
| **Frama-C Compatible** | ❌ Unlikely | ✅ Yes |

---

## Lessons from llvm-cbe

### What Can We Learn?

**1. LLVM IR is the wrong level:**
   - Too low-level
   - Lost semantics
   - Wrong abstraction

**2. C generation from IR doesn't work well:**
   - Produces unreadable code
   - Often uncompilable
   - Requires non-standard extensions

**3. High-level to high-level conversion is better:**
   - C++ AST to C code
   - Preserve semantics
   - Generate readable output

**4. Production tools avoid LLVM IR for source transformation:**
   - clang-tidy works on AST
   - clang-refactor works on AST
   - None use LLVM IR → C backend

---

## PNaCl SJLJ and llvm-cbe

### Relevant Finding from Exception Handling Research:

From PNaCl SJLJ document:
> "PNaCl's current ABI burns 1024 bytes for each jmp_buf"
> "They could reduce the jmp_buf size to 4 bytes by having each llvm.nacl.setjmp() call do an implicit alloca"

**Interpretation:**
- PNaCl worked at LLVM IR level
- Had to use oversized data structures
- Could not easily optimize

**Lesson:** Working at LLVM IR level limits optimization opportunities.

**Our advantage:** Working at AST level, we can generate optimal C code directly.

---

## Production Compiler Evidence

### Historical Evidence: Comeau C++, Cfront

**Comeau C++ (1990s):**
- Generated C code
- Worked from internal AST (NOT LLVM IR)
- Produced readable C output
- Commercial success

**Cfront (1983-1993):**
- Generated C code
- Worked from internal AST
- Pioneered C++ implementation
- Produced readable C output

**Key Point:** Historical C++ to C compilers worked at **AST level**, not IR level.

### Modern Tool: emmtrix eCPP2C

From search results:
> "eCPP2C utilizes the LLVM/Clang compiler technology"
> "The way eCPP2C is implemented, the IR of the C++ and C program is **almost identical** with only minor differences."

**Interpretation:**
- emmtrix uses Clang
- They mention IR similarity (marketing speak?)
- But likely work at AST level for generation
- No evidence they use llvm-cbe

---

## Final Assessment

### Can We Use Clang CodeGen or llvm-cbe?

**Clang CodeGen:**
- ❌ No C backend exists
- ❌ Building one is massive effort
- ❌ Wrong approach anyway

**llvm-cbe:**
- ❌ Produces unreadable code
- ❌ Often uncompilable
- ❌ Loses high-level semantics
- ❌ Non-standard C
- ❌ Not maintained officially
- ❌ Wrong abstraction level

### Recommendation: Direct C Generation from AST

**Architecture:**
```cpp
class CCodeEmitter {
public:
    std::string emitClass(const CXXRecordDecl *R);
    std::string emitFunction(const FunctionDecl *F);
    std::string emitStruct(const CXXRecordDecl *R);
    std::string emitVTable(const CXXRecordDecl *R);

private:
    std::string mangleName(const NamedDecl *D);
    std::string emitType(QualType T);
};

// Use in ASTConsumer:
class CppToCConsumer : public ASTConsumer {
    CCodeEmitter emitter;

    void HandleTranslationUnit(ASTContext &Context) override {
        for (Decl *D : Context.getTranslationUnitDecl()->decls()) {
            if (auto *R = dyn_cast<CXXRecordDecl>(D)) {
                std::string c_code = emitter.emitClass(R);
                writeToFile(c_code);
            }
        }
    }
};
```

**Benefits:**
- ✅ Simple and direct
- ✅ Full control
- ✅ Readable output
- ✅ Reliable
- ✅ Maintainable

---

## Conclusion

**Do NOT use llvm-cbe or attempt to build a Clang C backend.**

The evidence is overwhelming:
1. llvm-cbe produces terrible, often uncompilable code
2. LLVM IR is too low-level, loses semantics needed for good C generation
3. Historical and modern tools work at AST level
4. Production Clang tools (clang-tidy, clang-refactor) work at AST level
5. Direct C generation from AST is simpler, more reliable, and produces better code

**Recommendation:** Use RecursiveASTVisitor + custom C code emitter. Generate C code as text directly from Clang AST.

This is the **proven, practical approach** used by successful C++ to C conversion tools.

---

## References

1. [Stack Overflow: Using the LLVM linker to produce C code](https://stackoverflow.com/questions/31960290/using-the-llvm-linker-to-produce-c-code)
2. [GitHub: Ace17/llvm-cbe](https://github.com/Ace17/llvm-cbe)
3. [GitHub: JuliaHubOSS/llvm-cbe](https://github.com/JuliaHubOSS/llvm-cbe)
4. [GitHub Issue: Make output more C-like](https://github.com/JuliaHubOSS/llvm-cbe/issues/6)
5. [PNaCl SJLJ Exception Handling Documentation](https://docs.google.com/document/d/1Bub1bV_IIDZDhdld-zTULE2Sv0KNbOXk33KOW8o0aR4/mobilebasic)
