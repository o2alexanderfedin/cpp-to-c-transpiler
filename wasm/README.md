# C++ to C Transpiler - WebAssembly Module

> WebAssembly bindings for the hupyy-cpp-to-c transpiler with ACSL formal specification annotations

## Overview

This package provides WebAssembly-compiled versions of the C++ to C transpiler, enabling browser-based and edge-deployed transpilation. Two builds are available:

- **Minimal**: Size-optimized build (~TBD MB Brotli) for Cloudflare Workers
- **Full**: Performance-optimized build with all ACSL annotation phases

## Installation

```bash
npm install @hupyy/cpptoc-wasm
```

## Quick Start

### Browser Usage (Full Build)

```typescript
import createCppToC from '@hupyy/cpptoc-wasm/full';

// Initialize WASM module
const module = await createCppToC();
const transpiler = new module.Transpiler();

// Transpile C++ code
const result = transpiler.transpile(`
class Counter {
    int value;
public:
    void increment() { value++; }
    int getValue() const { return value; }
};
`, {
    acsl: {
        statements: true,
        typeInvariants: true,
        behaviors: true
    },
    target: 'c99'
});

if (result.success) {
    console.log('C code:', result.c);
    console.log('ACSL annotations:', result.acsl);
} else {
    console.error('Errors:', result.diagnostics);
}

// Clean up
transpiler.delete();
```

### Cloudflare Workers (Minimal Build)

```typescript
import createCppToC from '@hupyy/cpptoc-wasm/minimal';

export default {
    async fetch(request: Request): Promise<Response> {
        const { code } = await request.json();

        const module = await createCppToC();
        const transpiler = new module.Transpiler();
        const result = transpiler.transpile(code, { target: 'c99' });
        transpiler.delete();

        return Response.json(result);
    }
};
```

### Node.js Usage

```javascript
import createCppToC from '@hupyy/cpptoc-wasm/full';

const module = await createCppToC();
const transpiler = new module.Transpiler();
const result = transpiler.transpile('int main() { return 0; }');
console.log(result);
transpiler.delete();
```

## API Reference

See [API.md](docs/API.md) for complete TypeScript API documentation.

### Core Types

```typescript
interface TranspileOptions {
    acsl?: {
        statements?: boolean;
        typeInvariants?: boolean;
        axiomatics?: boolean;
        ghostCode?: boolean;
        behaviors?: boolean;
    };
    target?: 'c89' | 'c99' | 'c11' | 'c17';
    optimize?: boolean;
}

interface TranspileResult {
    success: boolean;
    c: string;
    acsl: string;
    diagnostics: Diagnostic[];
}
```

## Builds

### Minimal Build

- **Purpose**: Cloudflare Workers, edge deployment
- **Size**: ~TBD MB Brotli compressed (pending actual build)
- **Features**: Core transpilation only, no ACSL phases
- **Import**: `@hupyy/cpptoc-wasm/minimal`

### Full Build

- **Purpose**: Browser applications, full-featured transpilation
- **Size**: ~TBD MB Brotli compressed (pending actual build)
- **Features**: All ACSL annotation phases (1-5)
- **Import**: `@hupyy/cpptoc-wasm/full`

## Browser Compatibility

- Chrome/Edge: 92+
- Firefox: 90+
- Safari: 15.2+
- Node.js: 18+

Requires WebAssembly support with:
- ES6 modules
- Async/await
- BigInt (for large integers)

## Deployment

### Website Integration

See [docs/WEBSITE.md](docs/WEBSITE.md) for Astro/React/Vue integration examples.

### Cloudflare Workers

See [docs/CLOUDFLARE.md](docs/CLOUDFLARE.md) for deployment guide.

**Note**: Cloudflare Workers deployment is conditional on minimal build size < 3MB Brotli compressed. Run `npm run test:size` to verify.

## Building from Source

See [docs/BUILDING.md](docs/BUILDING.md) for detailed build instructions.

```bash
# Install Emscripten SDK
git clone https://github.com/emscripten-core/emsdk.git
cd emsdk
./emsdk install latest
./emsdk activate latest
source ./emsdk_env.sh

# Build WASM modules
cd wasm
./scripts/build-minimal.sh
./scripts/build-full.sh
./scripts/size-check.sh
```

## Performance

Initial load times (estimated, pending benchmarks):
- Minimal build: ~1-2s (size-dependent)
- Full build: ~3-5s (size-dependent)

Subsequent loads: Instant (browser cache + Service Worker)

Transpilation speed: Near-native performance for small-medium files (<1000 LOC)

## License

MIT License - see LICENSE file for details

## Related

- [Main Project](https://github.com/o2alexanderfedin/hupyy-cpp-to-c)
- [Documentation Website](https://o2alexanderfedin.github.io/cpp-to-c-website)
- [Cloudflare Workers Docs](https://developers.cloudflare.com/workers/)
- [Emscripten Documentation](https://emscripten.org/)

## Version

Current version: 1.22.0

Changelog: [CHANGELOG.md](CHANGELOG.md)
