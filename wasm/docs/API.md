# TypeScript API Reference

## Module Imports

### Full Build (Default)

```typescript
import createCppToC from '@hupyy/cpptoc-wasm/full';
// or
import createCppToC from '@hupyy/cpptoc-wasm';
```

### Minimal Build

```typescript
import createCppToC from '@hupyy/cpptoc-wasm/minimal';
```

## Core API

### `createCppToC(options?): Promise<WASMModule>`

Initializes the WASM module.

**Parameters**:
- `options?: CreateModuleOptions` - Optional configuration

**Returns**: `Promise<WASMModule>` - Initialized module with `Transpiler` constructor

**Example**:
```typescript
const module = await createCppToC({
    locateFile: (path) => `/wasm/full/${path}`,
    onRuntimeInitialized: () => console.log('WASM ready')
});
```

### `new module.Transpiler(): TranspilerInstance`

Creates a new transpiler instance.

**Returns**: `TranspilerInstance` - Transpiler object

**Example**:
```typescript
const transpiler = new module.Transpiler();
```

### `transpiler.transpile(code, options?): TranspileResult`

Transpiles C++ code to C with optional ACSL annotations.

**Parameters**:
- `code: string` - C++ source code
- `options?: TranspileOptions` - Transpilation options

**Returns**: `TranspileResult` - Transpilation result with C code, ACSL, and diagnostics

**Example**:
```typescript
const result = transpiler.transpile(`
class Point {
    int x, y;
public:
    void move(int dx, int dy) {
        x += dx;
        y += dy;
    }
};
`, {
    acsl: {
        statements: true,
        typeInvariants: true
    },
    target: 'c99'
});
```

### `transpiler.getVersion(): string`

Returns the transpiler version.

**Returns**: `string` - Version string (e.g., "1.22.0-full")

**Example**:
```typescript
console.log(transpiler.getVersion()); // "1.22.0-full"
```

### `transpiler.delete(): void`

Frees C++ memory. Call when done with transpiler instance.

**Example**:
```typescript
transpiler.delete();
```

## Type Definitions

### `ACSLOptions`

Configuration for ACSL annotation generation.

```typescript
interface ACSLOptions {
    statements?: boolean;       // Phase 1: Statement annotations, loop invariants, assertions
    typeInvariants?: boolean;   // Phase 2: Type invariants for structs/classes
    axiomatics?: boolean;       // Phase 3: Axiomatic definitions, predicates, logic functions
    ghostCode?: boolean;        // Phase 4: Ghost variable injection
    behaviors?: boolean;        // Phase 5: Function behavior annotations (requires/ensures)
}
```

### `TranspileOptions`

Configuration for transpilation.

```typescript
interface TranspileOptions {
    acsl?: ACSLOptions;         // ACSL annotation options
    target?: 'c89' | 'c99' | 'c11' | 'c17';  // Target C standard (default: 'c99')
    optimize?: boolean;         // Enable optimizations (default: false)
}
```

### `Diagnostic`

Compiler diagnostic message.

```typescript
interface Diagnostic {
    line: number;               // Line number (0 for global)
    column: number;             // Column number (0 for global)
    message: string;            // Diagnostic message
    severity: 'error' | 'warning' | 'note';  // Severity level
}
```

### `TranspileResult`

Result of transpilation.

```typescript
interface TranspileResult {
    success: boolean;           // True if transpilation succeeded
    c: string;                  // Generated C code
    acsl: string;               // Generated ACSL annotations
    diagnostics: Diagnostic[];  // List of errors, warnings, notes
}
```

## Helper Functions

### `hasErrors(result): boolean`

Checks if result contains errors.

```typescript
import { hasErrors } from '@hupyy/cpptoc-wasm';

if (hasErrors(result)) {
    console.error('Transpilation failed');
}
```

### `getErrors(result): Diagnostic[]`

Extracts only error diagnostics.

```typescript
import { getErrors } from '@hupyy/cpptoc-wasm';

const errors = getErrors(result);
errors.forEach(err => console.error(err.message));
```

### `getWarnings(result): Diagnostic[]`

Extracts only warning diagnostics.

```typescript
import { getWarnings } from '@hupyy/cpptoc-wasm';

const warnings = getWarnings(result);
warnings.forEach(warn => console.warn(warn.message));
```

### `formatDiagnostic(diagnostic): string`

Formats diagnostic for display.

```typescript
import { formatDiagnostic } from '@hupyy/cpptoc-wasm';

result.diagnostics.forEach(diag => {
    console.log(formatDiagnostic(diag));
    // Output: [ERROR] 10:5: undefined reference to 'foo'
});
```

## Constants

### `DEFAULT_ACSL_OPTIONS`

Default ACSL options for common use cases.

```typescript
import { DEFAULT_ACSL_OPTIONS } from '@hupyy/cpptoc-wasm';

const result = transpiler.transpile(code, {
    acsl: DEFAULT_ACSL_OPTIONS,  // statements, typeInvariants, behaviors enabled
    target: 'c99'
});
```

### `DEFAULT_TRANSPILE_OPTIONS`

Default transpilation options.

```typescript
import { DEFAULT_TRANSPILE_OPTIONS } from '@hupyy/cpptoc-wasm';
```

## Complete Example

```typescript
import createCppToC, {
    hasErrors,
    getErrors,
    formatDiagnostic,
    DEFAULT_ACSL_OPTIONS
} from '@hupyy/cpptoc-wasm/full';

async function transpileCppToC(cppCode: string) {
    // Initialize WASM module
    const module = await createCppToC();
    const transpiler = new module.Transpiler();

    try {
        // Transpile with full ACSL annotations
        const result = transpiler.transpile(cppCode, {
            acsl: DEFAULT_ACSL_OPTIONS,
            target: 'c99',
            optimize: false
        });

        // Check for errors
        if (hasErrors(result)) {
            const errors = getErrors(result);
            console.error('Transpilation failed:');
            errors.forEach(err => console.error(formatDiagnostic(err)));
            return null;
        }

        // Success
        console.log('C code:\n', result.c);
        console.log('ACSL annotations:\n', result.acsl);
        return result;

    } finally {
        // Always clean up
        transpiler.delete();
    }
}

// Usage
const cppCode = `
class Counter {
    int count;
public:
    Counter() : count(0) {}
    void increment() { count++; }
    int getValue() const { return count; }
};
`;

transpileCppToC(cppCode);
```

## Error Handling

### Common Errors

1. **WASM Load Failure**
   ```typescript
   try {
       const module = await createCppToC();
   } catch (error) {
       console.error('Failed to load WASM:', error);
       // Fallback: Use server-side API or show error message
   }
   ```

2. **Compilation Errors**
   ```typescript
   const result = transpiler.transpile(invalidCode);
   if (!result.success) {
       result.diagnostics.forEach(diag => {
           if (diag.severity === 'error') {
               console.error(`${diag.line}:${diag.column}: ${diag.message}`);
           }
       });
   }
   ```

3. **Out of Memory**
   ```typescript
   try {
       const result = transpiler.transpile(veryLargeCode);
   } catch (error) {
       console.error('WASM out of memory:', error);
       // Retry with smaller chunks or use server-side transpilation
   }
   ```

## Memory Management

### Best Practices

1. **Always call `delete()`**
   ```typescript
   const transpiler = new module.Transpiler();
   try {
       const result = transpiler.transpile(code);
       // Use result...
   } finally {
       transpiler.delete();  // Free C++ memory
   }
   ```

2. **Reuse instances for multiple transpilations**
   ```typescript
   const transpiler = new module.Transpiler();
   const results = files.map(file =>
       transpiler.transpile(file.content)
   );
   transpiler.delete();
   ```

3. **Don't store deleted instances**
   ```typescript
   // BAD
   let transpiler = new module.Transpiler();
   transpiler.delete();
   transpiler.transpile(code);  // ERROR: Use after delete

   // GOOD
   let transpiler = new module.Transpiler();
   const result = transpiler.transpile(code);
   transpiler.delete();
   transpiler = null;  // Prevent accidental use
   ```

## Performance Tips

1. **Preload WASM module**
   ```typescript
   // Preload on page load
   const modulePromise = createCppToC();

   // Use later without waiting
   const module = await modulePromise;
   ```

2. **Cache module instance**
   ```typescript
   let cachedModule = null;

   async function getModule() {
       if (!cachedModule) {
           cachedModule = await createCppToC();
       }
       return cachedModule;
   }
   ```

3. **Use minimal build when possible**
   ```typescript
   // For simple transpilation without ACSL
   import createCppToC from '@hupyy/cpptoc-wasm/minimal';
   // ~50% smaller, ~2x faster load
   ```

## Browser Support

Check WebAssembly support before loading:

```typescript
if (typeof WebAssembly !== 'object') {
    console.error('WebAssembly not supported');
    // Fallback to server-side API
} else {
    const module = await createCppToC();
}
```

## License

MIT License - See LICENSE file for details.
