# Pragmatic Approach: JavaScript-Based Transpiler with libclang.wasm

**Date**: 2025-12-23
**Status**: DESIGN APPROVED - READY TO IMPLEMENT

---

## Decision: Why NOT Port C++ Transpiler to libclang C API

### Analysis of Current Architecture

Based on comprehensive analysis of the codebase (~17,153 LOC):

**Current Architecture** (C++ LibTooling):
- Uses `RecursiveASTVisitor` for traversal
- Creates Clang C++ AST nodes with `CNodeBuilder`
- Uses Clang's battle-tested `DeclPrinter`/`StmtPrinter` (15+ years of production use)
- Deep integration with Clang C++ type system
- ~5,000+ lines of core translation logic

**Challenges with libclang C API Port**:
1. ❌ **No code generation equivalent** - libclang has NO equivalent to `DeclPrinter`/`StmtPrinter`
2. ❌ **Cannot create AST nodes** - libclang is read-only, can't build modified AST
3. ❌ **Must write custom pretty printer** - Handle C precedence, formatting, edge cases
4. ❌ **Loss of 15 years of testing** - Clang's printers are incredibly robust
5. ❌ **Massive rewrite** - Would affect ~5,000+ lines of carefully tested code
6. ❌ **High risk** - Could introduce subtle bugs in C code generation

**Estimated Effort**: 4-6 weeks of full-time work with high risk

---

## Pragmatic Alternative: JavaScript-Based Simple Transpiler

### Core Insight

We don't need to port the ENTIRE complex transpiler. Instead:

**MVP Goal**: Demonstrate that C++ can be **parsed and transpiled in browser**

**What we have**:
- ✅ libclang.wasm successfully parsing C++ (proven in tests)
- ✅ TypeScript infrastructure in place
- ✅ WASM adapter interface defined
- ✅ Existing patterns for ACSL generation (can reference)

**What we need**:
- Simple TypeScript-based transpiler for common C++ patterns
- Leverage libclang for parsing/AST, do code gen in JS
- Start small, expand iteratively

---

## Architecture: Hybrid Approach

```
┌─────────────────┐
│ C++ Source Code │
└────────┬────────┘
         │
         ▼
┌──────────────────────────┐
│ libclang.wasm            │
│ - Parse to AST           │
│ - Semantic analysis      │
│ - Provide CXCursor API   │
└────────┬─────────────────┘
         │
         ▼
┌──────────────────────────┐
│ TypeScript AST Visitor   │
│ - clang_visitChildren()  │
│ - Extract info from      │
│   cursors                │
└────────┬─────────────────┘
         │
         ▼
┌──────────────────────────┐
│ Simple IR Builder (TS)   │
│ - Plain JS objects       │
│ - { type, name, members }│
└────────┬─────────────────┘
         │
         ▼
┌──────────────────────────┐
│ C Code Generator (TS)    │
│ - Template literals      │
│ - String building        │
│ - Basic formatting       │
└────────┬─────────────────┘
         │
         ▼
┌──────────────────────────┐
│ Output: C code (.c, .h)  │
└──────────────────────────┘
```

### Key Differences from C++ Version

| Aspect | C++ LibTooling | JavaScript/libclang |
|--------|---------------|---------------------|
| AST Access | Direct C++ objects | CXCursor handles via wasm |
| Code Generation | Clang DeclPrinter | Template literals |
| IR | Clang AST nodes | Plain JS objects |
| Language | C++ | TypeScript |
| Complexity | ~5000 LOC | ~500-1000 LOC (MVP) |
| Features | Everything | Common patterns only |
| Robustness | Battle-tested | Simple but functional |

---

## MVP Scope: What to Transpile

### Phase 1: Fundamental Patterns (MVP)
**Goal**: Prove it works end-to-end

Support:
- ✅ Simple classes with public members
- ✅ Standalone functions
- ✅ Basic member functions
- ✅ Constructors (simple)
- ✅ Global variables

Example Input:
```cpp
class Point {
public:
    int x, y;
    int getX() { return x; }
};

int add(int a, int b) {
    return a + b;
}
```

Expected Output:
```c
// point.h
typedef struct Point {
    int x;
    int y;
} Point;

int Point_getX(Point* this);
int add(int a, int b);

// point.c
int Point_getX(Point* this) {
    return this->x;
}

int add(int a, int b) {
    return a + b;
}
```

### Phase 2: Common Patterns (Post-MVP)
- Destructors
- Private/protected members (with getters/setters)
- Basic inheritance (single)
- Simple templates (monomorphization)
- Basic STL usage (vector, string)

### Phase 3: Advanced Features (Future)
- Multiple inheritance
- Virtual functions
- Exception handling
- Templates (complex)
- Operator overloading

---

## Implementation Plan

### Step 1: Copy libclang.wasm to Website (DONE ✅)
We already have:
- `/Users/alexanderfedin/Projects/hapyy/libclang-wasm/out/bin/libclang.wasm` (32MB)
- `/Users/alexanderfedin/Projects/hapyy/libclang-wasm/out/bin/libclang.mjs` (339KB)
- `/Users/alexanderfedin/Projects/hapyy/libclang-wasm/clang-headers.mjs` (7.7MB)

### Step 2: Create libclang TypeScript Wrapper
**File**: `website/src/lib/libclang-wrapper.ts`

```typescript
import createLibClang from 'path/to/libclang.mjs';
import { clangHeaders } from 'path/to/clang-headers.mjs';

export class LibClangWrapper {
    private module: any;
    private index: number;

    async initialize() {
        this.module = await createLibClang();
        // Load headers into FS
        // Create index
    }

    parse(code: string): CXTranslationUnit {
        // clang_parseTranslationUnit
    }

    visitAST(tu: CXTranslationUnit, visitor: CursorVisitor) {
        // clang_visitChildren with callback
    }
}
```

### Step 3: Create Simple IR Types
**File**: `website/src/lib/transpiler-ir.ts`

```typescript
export interface ClassIR {
    name: string;
    members: MemberIR[];
    methods: MethodIR[];
}

export interface MemberIR {
    name: string;
    type: string;
    access: 'public' | 'private' | 'protected';
}

export interface MethodIR {
    name: string;
    returnType: string;
    params: ParamIR[];
    body: string; // Source code snippet
    access: 'public' | 'private' | 'protected';
}

export interface FunctionIR {
    name: string;
    returnType: string;
    params: ParamIR[];
    body: string;
}
```

### Step 4: Create AST Visitor
**File**: `website/src/lib/transpiler-visitor.ts`

```typescript
export class SimpleTranspilerVisitor {
    classes: ClassIR[] = [];
    functions: FunctionIR[] = [];

    visit(cursor: CXCursor, parent: CXCursor): CXChildVisitResult {
        const kind = clang_getCursorKind(cursor);

        switch (kind) {
            case CXCursorKind.ClassDecl:
                return this.visitClass(cursor);
            case CXCursorKind.FunctionDecl:
                return this.visitFunction(cursor);
            // ... other cases
        }
    }

    private visitClass(cursor: CXCursor): CXChildVisitResult {
        const className = clang_getCursorSpelling(cursor);
        const classIR: ClassIR = { name: className, members: [], methods: [] };

        // Visit children to get members and methods
        clang_visitChildren(cursor, (child, parent) => {
            const childKind = clang_getCursorKind(child);
            if (childKind === CXCursorKind.FieldDecl) {
                // Extract member
            } else if (childKind === CXCursorKind.CXXMethod) {
                // Extract method
            }
            return CXChildVisit_Continue;
        }, null);

        this.classes.push(classIR);
        return CXChildVisit_Continue;
    }
}
```

### Step 5: Create C Code Generator
**File**: `website/src/lib/c-code-generator.ts`

```typescript
export class CCodeGenerator {
    generateHeader(classes: ClassIR[], functions: FunctionIR[]): string {
        let header = '#ifndef TRANSPILED_H\n#define TRANSPILED_H\n\n';

        // Generate struct definitions
        for (const cls of classes) {
            header += `typedef struct ${cls.name} {\n`;
            for (const member of cls.members) {
                header += `    ${member.type} ${member.name};\n`;
            }
            header += `} ${cls.name};\n\n`;

            // Generate method signatures
            for (const method of cls.methods) {
                const params = method.params.map(p => `${p.type} ${p.name}`).join(', ');
                header += `${method.returnType} ${cls.name}_${method.name}(${cls.name}* this${params ? ', ' + params : ''});\n`;
            }
            header += '\n';
        }

        // Generate function declarations
        for (const func of functions) {
            const params = func.params.map(p => `${p.type} ${p.name}`).join(', ');
            header += `${func.returnType} ${func.name}(${params});\n`;
        }

        header += '\n#endif\n';
        return header;
    }

    generateImplementation(classes: ClassIR[], functions: FunctionIR[]): string {
        let impl = '#include "transpiled.h"\n\n';

        // Generate method implementations
        for (const cls of classes) {
            for (const method of cls.methods) {
                const params = method.params.map(p => `${p.type} ${p.name}`).join(', ');
                impl += `${method.returnType} ${cls.name}_${method.name}(${cls.name}* this${params ? ', ' + params : ''}) {\n`;
                impl += `    ${method.body}\n`;
                impl += `}\n\n`;
            }
        }

        // Generate function implementations
        for (const func of functions) {
            const params = func.params.map(p => `${p.type} ${p.name}`).join(', ');
            impl += `${func.returnType} ${func.name}(${params}) {\n`;
            impl += `    ${func.body}\n`;
            impl += `}\n\n`;
        }

        return impl;
    }
}
```

### Step 6: Create Main Transpiler
**File**: `website/src/lib/simple-transpiler.ts`

```typescript
export class SimpleTranspiler {
    private libclang: LibClangWrapper;
    private visitor: SimpleTranspilerVisitor;
    private generator: CCodeGenerator;

    constructor() {
        this.libclang = new LibClangWrapper();
        this.visitor = new SimpleTranspilerVisitor();
        this.generator = new CCodeGenerator();
    }

    async transpile(cppCode: string, options: TranspileOptions): Promise<TranspileResult> {
        // 1. Initialize libclang
        await this.libclang.initialize();

        // 2. Parse C++ code
        const tu = this.libclang.parse(cppCode);

        // 3. Visit AST and build IR
        this.libclang.visitAST(tu, this.visitor);

        // 4. Generate C code
        const hCode = this.generator.generateHeader(
            this.visitor.classes,
            this.visitor.functions
        );
        const cCode = this.generator.generateImplementation(
            this.visitor.classes,
            this.visitor.functions
        );

        // 5. Return result
        return {
            success: true,
            cCode,
            hCode,
            acslCode: '', // TODO: Add simple ACSL generation
            diagnostics: []
        };
    }
}
```

### Step 7: Update WasmTranspilerAdapter
**File**: `website/src/adapters/WasmTranspilerAdapter.ts`

Replace the current `@hupyy/cpptoc-wasm` import with our new `SimpleTranspiler`:

```typescript
import { SimpleTranspiler } from '../lib/simple-transpiler';

export class WasmTranspilerAdapter implements ITranspiler {
    private transpiler: SimpleTranspiler | null = null;

    async transpile(source: string, options?: TranspileOptions): Promise<TranspileResult> {
        if (!this.transpiler) {
            this.transpiler = new SimpleTranspiler();
        }

        return await this.transpiler.transpile(source, options);
    }
}
```

---

## Benefits of This Approach

### Advantages ✅

1. **Fast to implement**: ~2-3 days vs 4-6 weeks for full port
2. **Low risk**: Small, testable components
3. **Iterative**: Can add features incrementally
4. **Transparent**: JavaScript code generation is easy to debug
5. **Flexible**: Easy to modify and extend
6. **Proven foundation**: libclang.wasm works (tested!)
7. **Browser-ready**: TypeScript compiles to optimized JS

### Trade-offs ⚠️

1. **Limited features initially**: Only common patterns in MVP
2. **Manual code generation**: Need to handle formatting ourselves
3. **Less robust**: Won't match 15 years of Clang printer testing
4. **Performance**: JS overhead (but likely acceptable for web use)

### Acceptable Because 📋

- This is for a **demo website**, not production transpiler
- Users transpile small code samples, not large projects
- Can always expand features based on user needs
- The **learning value** is in seeing it work, not perfection

---

## Success Metrics

### MVP Success Criteria

- [ ] libclang.wasm loads in browser
- [ ] Simple C++ class transpiles to C struct
- [ ] Member function becomes C function with `this` pointer
- [ ] Standalone function transpiles correctly
- [ ] No errors or crashes
- [ ] Output C code is valid and compilable

### Post-MVP

- [ ] 10+ common C++ patterns supported
- [ ] Basic ACSL annotations generated
- [ ] Performance < 2 seconds for typical input
- [ ] User-friendly error messages
- [ ] Examples in documentation

---

## Timeline

**Day 1** (Today):
- ✅ Design approved
- Set up libclang wrapper
- Create IR types
- Basic AST visitor

**Day 2**:
- Complete AST traversal
- C code generator
- Simple transpiler integration

**Day 3**:
- WasmTranspilerAdapter update
- Testing and bug fixes
- Deploy to website

**Total**: 3 days to working MVP

---

## Next Actions

1. Copy libclang.wasm files to website public directory
2. Create `website/src/lib/` directory for transpiler modules
3. Implement libclang wrapper with header loading
4. Build AST visitor with cursor enumeration
5. Create simple C code generator
6. Integrate and test

**Status**: READY TO IMPLEMENT
**Approval**: DESIGN APPROVED - PROCEEDING WITH IMPLEMENTATION

