# Group 1 Task 1: Base Class Analysis - MultipleInheritanceAnalyzer

**Objective**: Create `MultipleInheritanceAnalyzer` to analyze C++ classes with multiple inheritance.

**TDD Approach**: Write failing tests first, then implement.

## Requirements

1. Analyze CXXRecordDecl to identify all polymorphic base classes
2. Determine primary base (first polymorphic base)
3. Identify non-primary bases (rest of polymorphic bases)
4. Calculate base class offsets using Clang ASTRecordLayout
5. Handle edge cases (single inheritance, no polymorphic bases, etc.)

## Files to Create

1. `include/MultipleInheritanceAnalyzer.h`
2. `src/MultipleInheritanceAnalyzer.cpp`
3. `tests/unit/MultipleInheritanceAnalyzerTest.cpp`

## Test Cases (8-10 tests)

1. `DetectMultiplePolymorphicBases` - Class with 2+ polymorphic bases
2. `IdentifyPrimaryBase` - First polymorphic base is primary
3. `IdentifyNonPrimaryBases` - Rest are non-primary
4. `CalculateBaseOffsets` - Correct offset for each base
5. `SingleInheritanceNoChange` - Single base remains primary only
6. `NonPolymorphicBasesSkipped` - Skip non-polymorphic bases
7. `MixedPolymorphicNonPolymorphic` - Handle mix correctly
8. `DeepInheritanceHierarchy` - Multi-level inheritance
9. `EmptyClassWithMultipleBases` - No fields, just bases
10. `NoBasesReturnsEmpty` - Class with no bases returns empty list

## Implementation Pattern

```cpp
class MultipleInheritanceAnalyzer {
    ASTContext& Context;

public:
    struct BaseInfo {
        const CXXRecordDecl* BaseDecl;
        bool IsPrimary;
        unsigned Offset;  // In bytes
        std::string VtblFieldName;  // "lpVtbl", "lpVtbl2", etc.
    };

    MultipleInheritanceAnalyzer(ASTContext& Ctx);

    // Get all polymorphic bases with offset info
    std::vector<BaseInfo> analyzePolymorphicBases(const CXXRecordDecl* Record);

    // Get primary base (first polymorphic base, if any)
    const CXXRecordDecl* getPrimaryBase(const CXXRecordDecl* Record);

    // Get non-primary bases
    std::vector<const CXXRecordDecl*> getNonPrimaryBases(const CXXRecordDecl* Record);

    // Calculate offset for a specific base
    unsigned calculateBaseOffset(const CXXRecordDecl* Derived,
                                  const CXXRecordDecl* Base);
};
```

## Success Criteria

- [ ] All 8-10 tests written (failing initially)
- [ ] All tests pass after implementation
- [ ] Uses Clang ASTRecordLayout for offset calculation
- [ ] Correctly identifies primary vs non-primary bases
- [ ] Handles edge cases (single inheritance, no bases, etc.)
- [ ] Code follows SOLID principles
- [ ] Well-documented with examples
