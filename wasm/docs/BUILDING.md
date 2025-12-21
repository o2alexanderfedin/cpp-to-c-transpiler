# Building from Source

This guide explains how to build the WebAssembly modules from source.

## Prerequisites

### 1. Emscripten SDK

The Emscripten SDK is required to compile C++ to WebAssembly.

```bash
# Clone Emscripten SDK
git clone https://github.com/emscripten-core/emsdk.git
cd emsdk

# Install latest version
./emsdk install latest

# Activate for current session
./emsdk activate latest

# Set up environment variables (required for each shell session)
source ./emsdk_env.sh

# Verify installation
emcc --version
```

**Add to shell profile** (optional, for permanent setup):
```bash
# Add to ~/.bashrc or ~/.zshrc
source /path/to/emsdk/emsdk_env.sh
```

### 2. CMake

CMake 3.20+ is required.

```bash
# macOS
brew install cmake

# Ubuntu/Debian
sudo apt-get install cmake

# Verify
cmake --version
```

### 3. Node.js

Node.js 18+ is required for TypeScript compilation and testing.

```bash
# macOS
brew install node

# Ubuntu/Debian
curl -fsSL https://deb.nodesource.com/setup_18.x | sudo -E bash -
sudo apt-get install -y nodejs

# Verify
node --version
npm --version
```

### 4. Clang/LLVM

Clang/LLVM 15+ is already required for the main project.

```bash
# Verify
clang --version
llvm-config --version
```

### 5. Optional: Brotli

For size compression testing.

```bash
# macOS
brew install brotli

# Ubuntu/Debian
sudo apt-get install brotli

# Verify
brotli --version
```

## Build Instructions

### Quick Build

```bash
cd wasm

# Build minimal (size-optimized)
./scripts/build-minimal.sh

# Build full (performance-optimized)
./scripts/build-full.sh

# Check sizes
./scripts/size-check.sh
```

### Manual Build

#### Minimal Build

```bash
cd wasm

# Create build directory
mkdir -p build-wasm-minimal
cd build-wasm-minimal

# Configure with Emscripten
emcmake cmake .. -DCMAKE_BUILD_TYPE=Release

# Build
emmake cmake --build . --target cpptoc-wasm-minimal

# Check output
ls -lh cpptoc-minimal.wasm cpptoc-minimal.js
```

#### Full Build

```bash
cd wasm

# Create build directory
mkdir -p build-wasm-full
cd build-wasm-full

# Configure with Emscripten
emcmake cmake .. -DCMAKE_BUILD_TYPE=Release

# Build
emmake cmake --build . --target cpptoc-wasm-full

# Check output
ls -lh cpptoc-full.wasm cpptoc-full.js
```

## Build Configuration

### CMake Variables

```bash
emcmake cmake .. \
  -DCMAKE_BUILD_TYPE=Release \
  -DENABLE_COVERAGE=OFF \
  -DENABLE_ASAN=OFF
```

### Optimization Levels

**Minimal build** uses:
- `-Oz`: Aggressive size optimization
- `--closure 1`: Google Closure Compiler on JavaScript
- `-flto`: Link-time optimization
- `-s INITIAL_MEMORY=33554432`: 32MB initial memory
- `-s MAXIMUM_MEMORY=268435456`: 256MB max memory

**Full build** uses:
- `-O3`: Performance optimization
- `-s INITIAL_MEMORY=67108864`: 64MB initial memory
- `-s MAXIMUM_MEMORY=536870912`: 512MB max memory
- `-g1`: Minimal debug info (line numbers)

## Size Validation

The `size-check.sh` script validates build sizes against thresholds:

```bash
cd wasm
./scripts/size-check.sh
```

**Thresholds**:
- Minimal uncompressed: < 25 MB
- Minimal Brotli: < 10 MB (ideally < 3 MB for Cloudflare)
- Full uncompressed: < 60 MB
- Full Brotli: < 25 MB

**Output**:
```
Minimal Build:
Uncompressed: 18.50 MB ✓
Gzip: 6.20 MB
Brotli: 5.10 MB ⚠️ EXCEEDS CLOUDFLARE LIMIT (3 MB)

Full Build:
Uncompressed: 42.30 MB ✓
Gzip: 14.80 MB
Brotli: 12.50 MB ✓
```

## Building NPM Package

```bash
cd wasm/glue

# Install dependencies
npm install

# Build TypeScript
npm run build:types

# Run tests (when implemented)
npm test

# Create package tarball
npm pack

# Test local installation
npm link
cd /path/to/test/project
npm link @hupyy/cpptoc-wasm
```

## Troubleshooting

### Emscripten Not Found

**Error**: `emcc: command not found`

**Solution**:
```bash
# Ensure Emscripten environment is activated
source /path/to/emsdk/emsdk_env.sh

# Verify
which emcc
```

### LLVM/Clang Not Found

**Error**: `Could not find LLVM/Clang`

**Solution**:
```bash
# Set LLVM_DIR environment variable
export LLVM_DIR=/path/to/llvm/lib/cmake/llvm

# Or configure CMake explicitly
emcmake cmake .. -DLLVM_DIR=/usr/local/opt/llvm/lib/cmake/llvm
```

### Out of Memory During Build

**Error**: `fatal error: killed signal terminated program cc1plus`

**Solution**:
```bash
# Limit parallel jobs
emmake cmake --build . --target cpptoc-wasm-minimal -j1

# Or increase system swap space
```

### WASM Size Too Large

**Error**: Size check fails with "EXCEEDS THRESHOLD"

**Solutions**:
1. Ensure using `-Oz` optimization for minimal build
2. Enable `--closure 1` for JavaScript minification
3. Check for debug symbols (`-g` flag) and remove if not needed
4. Review linked libraries (may be including unnecessary Clang/LLVM components)
5. Consider code splitting (advanced, requires architecture changes)

### TypeScript Compilation Errors

**Error**: TypeScript compilation fails

**Solution**:
```bash
cd wasm/glue

# Clean and rebuild
rm -rf dist node_modules
npm install
npm run build:types
```

## Advanced Configuration

### Custom Emscripten Flags

Edit `wasm/CMakeLists.txt`:

```cmake
set(WASM_COMMON_FLAGS
    "-s MODULARIZE=1"
    "-s EXPORT_ES6=1"
    # Add custom flags here
    "-s ASSERTIONS=2"  # Enable runtime assertions
)
```

### Memory Configuration

Adjust memory limits in `wasm/CMakeLists.txt`:

```cmake
# For larger C++ codebases
set_target_properties(cpptoc-wasm-full PROPERTIES
    LINK_FLAGS "${WASM_COMMON_FLAGS} -O3 -s INITIAL_MEMORY=134217728 -s MAXIMUM_MEMORY=1073741824"
)
```

### Debug Builds

Build with debug symbols:

```bash
emcmake cmake .. -DCMAKE_BUILD_TYPE=Debug
emmake cmake --build . --target cpptoc-wasm-full

# Results in larger WASM but better error messages
```

## Build Artifacts

After successful build, artifacts are located at:

```
wasm/
├── build-wasm-minimal/
│   ├── cpptoc-minimal.wasm    # WebAssembly binary
│   ├── cpptoc-minimal.js      # JavaScript glue code
│   └── cpptoc-minimal.wasm.map # Source map (if debug)
├── build-wasm-full/
│   ├── cpptoc-full.wasm
│   ├── cpptoc-full.js
│   └── cpptoc-full.wasm.map
└── glue/dist/
    ├── minimal/
    │   ├── cpptoc.js          # Copied from build-wasm-minimal
    │   ├── cpptoc.wasm
    │   └── index.d.ts         # TypeScript definitions
    └── full/
        ├── cpptoc.js
        ├── cpptoc.wasm
        └── index.d.ts
```

## Clean Build

```bash
cd wasm

# Remove all build artifacts
rm -rf build-wasm-minimal build-wasm-full glue/dist glue/node_modules

# Rebuild from scratch
./scripts/build-minimal.sh
./scripts/build-full.sh
```

## CI/CD Build

The GitHub Actions workflow (`.github/workflows/wasm-build.yml`) automates:

1. Emscripten setup
2. Dual builds (minimal + full)
3. Size validation
4. Test execution
5. Artifact upload
6. NPM publishing (on tags)

**Trigger**:
```bash
git tag v1.22.0
git push --tags

# GitHub Actions will:
# - Build WASM modules
# - Run tests
# - Publish to NPM
# - Create GitHub Release
```

## Next Steps

After successful build:

1. **Test WASM modules**
   ```bash
   node -e "import('./glue/dist/full/cpptoc.js').then(m => console.log(m))"
   ```

2. **Integrate into website**
   ```bash
   cp wasm/glue/dist/full/* ../website/public/wasm/full/
   ```

3. **Deploy Cloudflare Worker** (if size permits)
   ```bash
   cd wasm/cloudflare-worker
   npm install
   wrangler deploy
   ```

4. **Publish to NPM**
   ```bash
   cd wasm/glue
   npm publish --access public
   ```

## Support

For build issues:
- Check [TROUBLESHOOTING.md](TROUBLESHOOTING.md)
- File an issue: https://github.com/o2alexanderfedin/hupyy-cpp-to-c/issues
- Emscripten documentation: https://emscripten.org/docs/

## License

MIT License - See LICENSE file for details.
