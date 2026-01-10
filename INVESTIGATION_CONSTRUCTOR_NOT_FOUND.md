# Investigation: Constructor Function Not Found

**Date**: 2026-01-09
**Issue**: CompoundStmtHandler cannot find C1 constructor: `Derived__ctor__void_C1`

## Problem Statement

E2E tests crash with:
```
[CompoundStmtHandler] ERROR: Constructor function not found: Derived__ctor__void_C1
Assertion failed: (isa<T>(CanonicalType)), function castAs, file Type.h, line 9010.
```

## Observation

### Constructors Being Generated

From the logs, these constructors are generated:
- `Derived__ctor__constDerivedref_C1` - Copy constructor C1 variant
- `Derived__ctor__Derivedrref_C1` - Move constructor C1 variant
- `Derived__ctor__constDerivedref_C2` - Copy constructor C2 variant
- `Derived__ctor__Derivedrref_C2` - Move constructor C2 variant

### Constructor Being Requested

CompoundStmtHandler is looking for:
- `Derived__ctor__void_C1` - Default constructor C1 variant

**This constructor is NOT being generated!**

## Root Cause Analysis

Classes with virtual inheritance need C1/C2 constructor variants. Currently:

1. **Explicit constructors** are correctly split into C1/C2 variants by ConstructorHandler
2. **Implicit copy/move constructors** are being generated (we see them in logs)
3. **Implicit default constructor** is NOT being generated with C1/C2 variants

The issue is that when C++ generates an implicit default constructor for a class with virtual inheritance, ConstructorHandler processes it but only generates the regular (non-variant) constructor, then skips it because `needsConstructorVariants()` returns true.

Looking at ConstructorHandler lines 79-97:
```cpp
if (needsConstructorVariants(ctor)) {
    llvm::outs() << "[ConstructorHandler] Class " << className
                 << " needs C1/C2 constructor variants - skipping regular constructor\n";

    // Generate C1 (complete-object) constructor
    generateC1Constructor(ctor, cppASTContext, cASTContext, disp);

    // Generate C2 (base-subobject) constructor
    generateC2Constructor(ctor, cppASTContext, cASTContext, disp);

    return; // Skip regular constructor generation
}
```

This code correctly generates C1/C2 variants for ALL constructors that need them. So why isn't the default constructor being processed?

## Hypothesis

The implicit default constructor might be:
1. Not showing up in the AST traversal
2. Being filtered out before reaching ConstructorHandler
3. Having a different AST representation that's not matching our canHandle predicate

## Next Steps

1. Add debug logging to ConstructorHandler::canHandle to see all constructors
2. Check if implicit default constructors are being filtered out by the dispatcher
3. Verify that Clang includes implicit default constructors in the AST
4. If they're missing, we may need to explicitly request them via Clang AST options

## Temporary Workaround

None - this is a blocking issue that prevents object construction in generated C code.
