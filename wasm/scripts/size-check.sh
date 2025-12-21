#!/bin/bash
set -e

echo "========================================="
echo "WASM Size Validation"
echo "========================================="

# Thresholds (in bytes)
MINIMAL_UNCOMPRESSED_MAX=26214400  # 25 MB
MINIMAL_BROTLI_MAX=10485760        # 10 MB (ideally < 3MB for Cloudflare)
FULL_UNCOMPRESSED_MAX=62914560     # 60 MB
FULL_BROTLI_MAX=26214400           # 25 MB

EXIT_CODE=0

# Check if builds exist
if [ ! -f "build-wasm-minimal/cpptoc-minimal.wasm" ]; then
    echo "ERROR: Minimal WASM not found. Run build-minimal.sh first."
    exit 1
fi

if [ ! -f "build-wasm-full/cpptoc-full.wasm" ]; then
    echo "ERROR: Full WASM not found. Run build-full.sh first."
    exit 1
fi

# Check minimal build
echo ""
echo "Minimal Build:"
echo "-------------"
MINIMAL_UNCOMPRESSED=$(stat -f%z build-wasm-minimal/cpptoc-minimal.wasm 2>/dev/null || stat -c%s build-wasm-minimal/cpptoc-minimal.wasm)
MINIMAL_GZIP=$(gzip -c build-wasm-minimal/cpptoc-minimal.wasm | wc -c | tr -d ' ')
MINIMAL_BROTLI=0
if command -v brotli &> /dev/null; then
    MINIMAL_BROTLI=$(brotli -c build-wasm-minimal/cpptoc-minimal.wasm | wc -c | tr -d ' ')
fi

printf "Uncompressed: %.2f MB" $(echo "$MINIMAL_UNCOMPRESSED / 1024 / 1024" | bc -l)
if [ $MINIMAL_UNCOMPRESSED -gt $MINIMAL_UNCOMPRESSED_MAX ]; then
    echo " ❌ EXCEEDS THRESHOLD (25 MB)"
    EXIT_CODE=1
else
    echo " ✓"
fi

printf "Gzip: %.2f MB" $(echo "$MINIMAL_GZIP / 1024 / 1024" | bc -l)
echo ""

if [ $MINIMAL_BROTLI -gt 0 ]; then
    printf "Brotli: %.2f MB" $(echo "$MINIMAL_BROTLI / 1024 / 1024" | bc -l)
    if [ $MINIMAL_BROTLI -gt $MINIMAL_BROTLI_MAX ]; then
        echo " ❌ EXCEEDS THRESHOLD (10 MB)"
        EXIT_CODE=1
    elif [ $MINIMAL_BROTLI -gt 3145728 ]; then
        echo " ⚠️  EXCEEDS CLOUDFLARE LIMIT (3 MB)"
        echo "    Cloudflare Workers deployment NOT feasible with current build"
    else
        echo " ✓ CLOUDFLARE COMPATIBLE"
    fi
fi

# Check full build
echo ""
echo "Full Build:"
echo "----------"
FULL_UNCOMPRESSED=$(stat -f%z build-wasm-full/cpptoc-full.wasm 2>/dev/null || stat -c%s build-wasm-full/cpptoc-full.wasm)
FULL_GZIP=$(gzip -c build-wasm-full/cpptoc-full.wasm | wc -c | tr -d ' ')
FULL_BROTLI=0
if command -v brotli &> /dev/null; then
    FULL_BROTLI=$(brotli -c build-wasm-full/cpptoc-full.wasm | wc -c | tr -d ' ')
fi

printf "Uncompressed: %.2f MB" $(echo "$FULL_UNCOMPRESSED / 1024 / 1024" | bc -l)
if [ $FULL_UNCOMPRESSED -gt $FULL_UNCOMPRESSED_MAX ]; then
    echo " ❌ EXCEEDS THRESHOLD (60 MB)"
    EXIT_CODE=1
else
    echo " ✓"
fi

printf "Gzip: %.2f MB" $(echo "$FULL_GZIP / 1024 / 1024" | bc -l)
echo ""

if [ $FULL_BROTLI -gt 0 ]; then
    printf "Brotli: %.2f MB" $(echo "$FULL_BROTLI / 1024 / 1024" | bc -l)
    if [ $FULL_BROTLI -gt $FULL_BROTLI_MAX ]; then
        echo " ❌ EXCEEDS THRESHOLD (25 MB)"
        EXIT_CODE=1
    else
        echo " ✓"
    fi
fi

echo ""
echo "========================================="
if [ $EXIT_CODE -eq 0 ]; then
    echo "✓ All size checks PASSED"
else
    echo "❌ Some size checks FAILED"
fi
echo "========================================="

exit $EXIT_CODE
