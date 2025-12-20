#!/bin/bash
set -e

echo "========================================="
echo "Building WASM Full (Performance-Optimized)"
echo "========================================="

# Check Emscripten availability
if ! command -v emcc &> /dev/null; then
    echo "ERROR: Emscripten not found"
    echo "Please install Emscripten SDK:"
    echo "  git clone https://github.com/emscripten-core/emsdk.git"
    echo "  cd emsdk"
    echo "  ./emsdk install latest"
    echo "  ./emsdk activate latest"
    echo "  source ./emsdk_env.sh"
    exit 1
fi

# Navigate to project root
cd "$(dirname "$0")"/../..

# Create build directory
mkdir -p build-wasm-full
cd build-wasm-full

# Configure with Emscripten
echo "Configuring CMake..."
emcmake cmake ../wasm -DCMAKE_BUILD_TYPE=Release

# Build
echo "Building full WASM..."
emmake cmake --build . --target cpptoc-wasm-full

# Report size
echo ""
echo "========================================="
echo "Build Complete!"
echo "========================================="
ls -lh cpptoc-full.wasm
echo ""
echo "Compressed sizes:"
gzip -c cpptoc-full.wasm | wc -c | awk '{printf "Gzip: %.2f MB\n", $1/1024/1024}'
brotli -c cpptoc-full.wasm | wc -c | awk '{printf "Brotli: %.2f MB\n", $1/1024/1024}' || echo "Brotli not available"
echo "========================================="
