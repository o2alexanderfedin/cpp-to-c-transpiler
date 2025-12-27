/**
 * @file simple_type_alias.cpp
 * @brief Phase 53 E2E Test: Simple type aliases
 *
 * Tests basic type alias translation:
 * - using IntType = int;
 * - using IntPtr = int*;
 */

// Simple type aliases
using IntType = int;
using FloatType = float;
using IntPtr = int*;

// Function using type aliases
int testTypeAliases() {
    IntType x = 42;
    FloatType y = 3.14f;
    IntPtr p = &x;

    return *p;
}

int main() {
    return testTypeAliases();
}
