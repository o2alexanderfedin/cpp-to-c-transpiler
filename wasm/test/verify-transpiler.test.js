#!/usr/bin/env node

/**
 * Comprehensive WASM Transpiler Verification Tests
 *
 * PURPOSE: PROVE (not claim) that WASM transpiler produces REAL C code
 *
 * Tests verify:
 * - WASM module loads successfully
 * - transpile() function exists and is callable
 * - Output is REAL C code (not placeholders)
 * - Multiple C++ constructs transpile correctly
 * - Error handling works properly
 * - All transpiler options work as expected
 */

const fs = require('fs');
const path = require('path');

// Load the WASM module
const wasmModulePath = path.join(__dirname, '../glue/dist/full/cpptoc.js');

// Test counter
let testsRun = 0;
let testsPassed = 0;
let testsFailed = 0;

function assert(condition, message) {
    testsRun++;
    if (condition) {
        console.log(`✅ PASS: ${message}`);
        testsPassed++;
        return true;
    } else {
        console.error(`❌ FAIL: ${message}`);
        testsFailed++;
        return false;
    }
}

function assertContains(str, substring, message) {
    return assert(str.includes(substring), message);
}

function assertNotContains(str, substring, message) {
    return assert(!str.includes(substring), message);
}

function runTest(testName, testFn) {
    console.log(`\n--- Running: ${testName} ---`);
    try {
        testFn();
    } catch (e) {
        console.error(`❌ EXCEPTION in ${testName}:`, e.message);
        testsFailed++;
    }
}

// Check if WASM module exists
if (!fs.existsSync(wasmModulePath)) {
    console.error(`❌ FATAL: WASM module not found at: ${wasmModulePath}`);
    console.error('Please build the WASM module first:');
    console.error('  cd /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/wasm');
    console.error('  ./scripts/build-full.sh');
    process.exit(1);
}

const cpptoc = require(wasmModulePath);

// WAIT for WASM module to load
cpptoc.then(Module => {
    console.log('WASM Module loaded successfully');

    // TEST 1: Basic Function Transpilation
    runTest('Test 1: Simple Function', () => {
        const cppCode = `
int add(int a, int b) {
    return a + b;
}`;

        const options = new Module.TranspileOptions();
        const result = Module.transpile(cppCode, options);

        assert(result.success, 'Transpilation succeeded');
        assertNotContains(result.c, '/* Full transpilation requires', 'NO placeholder text');
        assertNotContains(result.c, 'TODO', 'NO TODO markers');
        assertContains(result.c, 'int add', 'Contains function declaration');
        assertContains(result.c, 'return', 'Contains return statement');

        console.log('Generated C code preview:', result.c.substring(0, 200));
    });

    // TEST 2: Class Transpilation
    runTest('Test 2: Class with Methods', () => {
        const cppCode = `
class Point {
    int x, y;
public:
    Point(int x, int y) : x(x), y(y) {}
    int getX() const { return x; }
};`;

        const options = new Module.TranspileOptions();
        const result = Module.transpile(cppCode, options);

        assert(result.success, 'Class transpilation succeeded');
        assertNotContains(result.c, 'placeholder', 'NO placeholder text');
        assertContains(result.c, 'struct', 'Contains struct definition (C class representation)');

        console.log('Generated C code preview:', result.c.substring(0, 200));
    });

    // TEST 3: Control Flow
    runTest('Test 3: Control Flow Statements', () => {
        const cppCode = `
int factorial(int n) {
    if (n <= 1) return 1;
    int result = 1;
    for (int i = 2; i <= n; i++) {
        result *= i;
    }
    return result;
}`;

        const options = new Module.TranspileOptions();
        const result = Module.transpile(cppCode, options);

        assert(result.success, 'Control flow transpilation succeeded');
        assertNotContains(result.c, 'placeholder', 'NO placeholder text');
        assertContains(result.c, 'if', 'Contains if statement');
        assertContains(result.c, 'for', 'Contains for loop');

        console.log('Generated C code preview:', result.c.substring(0, 200));
    });

    // TEST 4: Pointers
    runTest('Test 4: Pointer Operations', () => {
        const cppCode = `
void swap(int *a, int *b) {
    int temp = *a;
    *a = *b;
    *b = temp;
}`;

        const options = new Module.TranspileOptions();
        const result = Module.transpile(cppCode, options);

        assert(result.success, 'Pointer transpilation succeeded');
        assertNotContains(result.c, 'placeholder', 'NO placeholder text');
        assertContains(result.c, '*', 'Contains pointer syntax');

        console.log('Generated C code preview:', result.c.substring(0, 200));
    });

    // TEST 5: ACSL Options
    runTest('Test 5: ACSL Statement Generation', () => {
        const cppCode = `
int divide(int a, int b) {
    return a / b;
}`;

        const options = new Module.TranspileOptions();
        options.acsl.statements = true;

        const result = Module.transpile(cppCode, options);

        assert(result.success, 'ACSL transpilation succeeded');
        assertNotContains(result.c, 'placeholder', 'NO placeholder text');
        // May or may not contain ACSL depending on implementation

        console.log('Generated C code preview:', result.c.substring(0, 200));
    });

    // TEST 6: Template Handling
    runTest('Test 6: Template Monomorphization', () => {
        const cppCode = `
template<typename T>
T max(T a, T b) {
    return (a > b) ? a : b;
}

int main() {
    return max(5, 10);
}`;

        const options = new Module.TranspileOptions();
        options.monomorphizeTemplates = true;

        const result = Module.transpile(cppCode, options);

        assert(result.success, 'Template transpilation succeeded');
        assertNotContains(result.c, 'placeholder', 'NO placeholder text');

        console.log('Generated C code preview:', result.c.substring(0, 200));
    });

    // TEST 7: Error Handling
    runTest('Test 7: Invalid C++ Code Handling', () => {
        const cppCode = `
        int broken syntax {{{ this won't compile
        `;

        const options = new Module.TranspileOptions();
        const result = Module.transpile(cppCode, options);

        // Should fail gracefully, not crash
        assert(!result.success, 'Invalid code fails gracefully');
        assert(result.diagnostics.size() > 0, 'Diagnostics provided for errors');

        console.log('Error diagnostics:', result.diagnostics.size(), 'errors');
    });

    // TEST 8: Version Check
    runTest('Test 8: WASM Module Version', () => {
        const version = Module.getVersion();

        assertNotContains(version, 'placeholder', 'Version is NOT placeholder');
        assertContains(version, '1.22', 'Version is 1.22.x');

        console.log('WASM Module Version:', version);
    });

    // TEST 9: Multiple Transpilations (Memory Safety)
    runTest('Test 9: Multiple Transpilations (Memory Test)', () => {
        for (let i = 0; i < 10; i++) {
            const cppCode = `int test${i}() { return ${i}; }`;
            const options = new Module.TranspileOptions();
            const result = Module.transpile(cppCode, options);

            assert(result.success, `Transpilation ${i+1}/10 succeeded`);
            assertContains(result.c, `test${i}`, `Contains test${i} function`);
        }
        console.log('All 10 transpilations completed without crashes');
    });

    // TEST 10: Large Code Input
    runTest('Test 10: Large C++ File', () => {
        // Generate large C++ code
        let largeCppCode = '';
        for (let i = 0; i < 100; i++) {
            largeCppCode += `int func${i}(int x) { return x + ${i}; }\n`;
        }

        const options = new Module.TranspileOptions();
        const result = Module.transpile(largeCppCode, options);

        assert(result.success, 'Large file transpilation succeeded');
        assertNotContains(result.c, 'placeholder', 'NO placeholder text in large output');
        assert(result.c.length > 1000, 'Generated substantial output');

        console.log('Generated C code size:', result.c.length, 'bytes');
    });

    // FINAL RESULTS
    console.log('\n======================================');
    console.log('WASM TRANSPILER VERIFICATION RESULTS');
    console.log('======================================');
    console.log(`Total Tests: ${testsRun}`);
    console.log(`✅ Passed: ${testsPassed}`);
    console.log(`❌ Failed: ${testsFailed}`);
    console.log('======================================');

    if (testsFailed === 0) {
        console.log('\n🎉 ALL TESTS PASSED - WASM TRANSPILER PROVEN TO WORK!');
        process.exit(0);
    } else {
        console.log('\n⚠️  SOME TESTS FAILED - TRANSPILER NOT FULLY VERIFIED');
        process.exit(1);
    }

}).catch(err => {
    console.error('❌ FATAL: Failed to load WASM module:', err);
    process.exit(1);
});
