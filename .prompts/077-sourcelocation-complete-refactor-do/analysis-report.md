# SourceLocation Refactoring Analysis

## Summary
- **Total handlers analyzed**: 44
- **Handlers needing refactoring**: 44 (100%)
- **Total `clang::SourceLocation()` occurrences**: ~210+

## Critical Finding
Even **VariableHandler.cpp** (our POC) has **4 additional occurrences** beyond the ones we fixed (lines 321, 341, 352, 375). The POC only fixed the VarDecl creation at lines 222-240.

## Breakdown by Handler (sorted by occurrence count)

### High Priority (Most Occurrences)

#### 1. ConstructorHandler.cpp - **55 occurrences** ⚠️
Lines: 109, 110, 167, 168, 192, 193, 280, 283, 292, 294, 297, 350, 351, 365, 366, 380, 383, 396, 410, 431, 434, 443, 445, 448, 488, 489, 503, 504, 517, 520, 533, 546, 648, 649, 664, 665, 677, 678, 693, 696, 715, 716, 724, 735, 769, 770, 781, 784, 791
**Impact**: Highest - constructor code is critical for object initialization

#### 2. StatementHandler.cpp - **8 occurrences**
Lines: 212, 213, 215, 262, 263, 596, 627, 692, 693
**Impact**: High - affects all statement translation

#### 3. CXXMemberCallExprHandler.cpp - **5 occurrences**
Lines: 75, 78, 111, 155, 177
**Impact**: High - affects member function calls

#### 4. LiteralHandler.cpp - **5 occurrences**
Lines: 94, 114, 134, 153, 175
**Impact**: Medium - affects literal values

### Medium Priority (4 occurrences)

#### 5. VirtualMethodHandler.cpp - **4 occurrences**
Lines: 253, 254, 267, 268
**AST nodes**: FunctionDecl, ParmVarDecl

#### 6. InstanceMethodHandler.cpp - **4 occurrences**
Lines: 222, 223, 236, 237
**AST nodes**: FunctionDecl, ParmVarDecl

#### 7. VariableHandler.cpp - **4 occurrences** ⚠️
Lines: 321, 341, 352, 375
**NOTE**: Lines 222-240 already fixed in POC, these are ADDITIONAL occurrences
**AST nodes**: DeclRefExpr, other variable-related nodes

#### 8. MethodHandler.cpp - **4 occurrences**
Lines: 206, 207, 220, 221
**AST nodes**: FunctionDecl, ParmVarDecl

#### 9. CXXThisExprHandler.cpp - **4 occurrences**
Lines: 65, 66, 78, 81
**AST nodes**: VarDecl, DeclRefExpr for `this` pointer

#### 10. IfStmtHandler.cpp - **4 occurrences**
Lines: 92, 97, 98, 100
**AST nodes**: IfStmt locations

#### 11. DeclStmtHandler.cpp - **4 occurrences**
Lines: 101, 102, 113, 114
**AST nodes**: DeclStmt

#### 12. RecordHandler.cpp - **4 occurrences**
Lines: 193, 194, 286, 287
**AST nodes**: RecordDecl, FieldDecl

### Standard Priority (3 occurrences)

13. WhileStmtHandler.cpp - 3 (lines 88, 89, 90)
14. MemberExprHandler.cpp - 3 (lines 91, 93, 96)
15. UnresolvedLookupExprHandler.cpp - 3 (lines 92, 102, 105)
16. CXXTemporaryObjectExprHandler.cpp - 3 (lines 106, 108, 115)
17. CXXConstructExprHandler.cpp - 3 (lines 153, 155, 174)
18. EnumTranslator.cpp - 3 (lines 79, 80, 181)
19. CXXOperatorCallExprHandler.cpp - 3 (lines 111, 114, 138)
20. DeclRefExprHandler.cpp - 3 (lines 92, 95, 114)
21. ForStmtHandler.cpp - 3 (lines 122, 123, 124)

### Low Priority (1-2 occurrences)

22. CompoundAssignOperatorHandler.cpp - 2 (lines 146, 162)
23. CXXNewExprHandler.cpp - 2 (lines 90, 110)
24. CompoundStmtHandler.cpp - 2 (lines 135, 136)
25. ReturnStmtHandler.cpp - 2 (lines 80, 88)
26. BinaryOperatorHandler.cpp - 1 (line 95)
27. SwitchStmtHandler.cpp - 2 (lines 88, 89)
28. InitListExprHandler.cpp - 2 (lines 70, 72)
29. DestructorHandler.cpp - 2 (lines 184, 185)
30. CallExprHandler.cpp - 2 (lines 112, 129)
31. CXXStaticCastExprHandler.cpp - 2 (lines 76, 77)
32. ParenExprHandler.cpp - 2 (lines 76, 77)
33. ConditionalOperatorHandler.cpp - 2 (lines 90, 92)
34. ParameterHandler.cpp - 2 (lines 70, 71)
35. CStyleCastExprHandler.cpp - 2 (lines 75, 76)
36. CommaOperatorHandler.cpp - 1 (line 98)
37. CXXFunctionalCastExprHandler.cpp - 2 (lines 77, 78)
38. CXXTypeidExprHandler.cpp - 1 (line 190)
39. CXXDeleteExprHandler.cpp - 1 (line 78)
40. CXXDynamicCastExprHandler.cpp - 1 (line 199)
41. CXXNullPtrLiteralExprHandler.cpp - 1 (line 54)
42. RecoveryExprHandler.cpp - 1 (line 56)
43. UnaryOperatorHandler.cpp - 1 (line 78)
44. ArraySubscriptExprHandler.cpp - 1 (line 91)

## Refactoring Strategy

### Phase 1: Complete VariableHandler (POC Completion)
- Fix 4 remaining occurrences in VariableHandler.cpp
- Verify POC is truly complete

### Phase 2: High-Impact Handlers (Parallel)
Execute in parallel subtasks:
- **Group A**: ConstructorHandler (55 occurrences)
- **Group B**: StatementHandler (8 occurrences), CXXMemberCallExprHandler (5 occurrences)
- **Group C**: LiteralHandler (5 occurrences), VirtualMethodHandler (4), InstanceMethodHandler (4)
- **Group D**: MethodHandler (4), CXXThisExprHandler (4), IfStmtHandler (4)

### Phase 3: Standard Handlers (Parallel)
- **Group E**: All 3-occurrence handlers (9 handlers)
- **Group F**: All 1-2 occurrence handlers (remaining 26 handlers)

### Phase 4: Build & Test
- Full rebuild after each phase
- Run unit tests
- Run E2E tests

## Common Patterns Expected

### Pattern 1: Single Location for AST Node
```cpp
// Before
SomeDecl* decl = SomeDecl::Create(
    ctx, parent, clang::SourceLocation(), ...);

// After
std::string targetPath = disp.getCurrentTargetPath();
if (targetPath.empty()) {
    targetPath = disp.getTargetPath(cppASTContext, D);
}
SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

SomeDecl* decl = SomeDecl::Create(
    ctx, parent, targetLoc, ...);
```

### Pattern 2: Multiple Locations (Start/End)
```cpp
// Before
FunctionDecl* func = FunctionDecl::Create(
    ctx, parent,
    clang::SourceLocation(),  // StartLoc
    clang::SourceLocation(),  // NameLoc
    ...);

// After
FunctionDecl* func = FunctionDecl::Create(
    ctx, parent,
    targetLoc,  // StartLoc
    targetLoc,  // NameLoc (use same location)
    ...);
```

### Pattern 3: DeclarationNameInfo
```cpp
// Before
DeclarationNameInfo(name, clang::SourceLocation())

// After
DeclarationNameInfo(name, targetLoc)
```

### Pattern 4: Reusing targetLoc in Same Function
```cpp
// Calculate once at function start
std::string targetPath = disp.getCurrentTargetPath();
if (targetPath.empty()) {
    targetPath = disp.getTargetPath(cppASTContext, D);
}
SourceLocationMapper& locMapper = disp.getTargetContext().getLocationMapper();
clang::SourceLocation targetLoc = locMapper.getStartOfFile(targetPath);

// Reuse targetLoc for all AST nodes in same function
SomeDecl* decl1 = SomeDecl::Create(ctx, parent, targetLoc, ...);
SomeDecl* decl2 = SomeDecl::Create(ctx, parent, targetLoc, ...);
```

## Edge Cases to Watch For

1. **TypeSourceInfo creation**: Some require location parameter
   - Old: `ctx.getTrivialTypeSourceInfo(type)`
   - New: `ctx.getTrivialTypeSourceInfo(type, targetLoc)`

2. **Conditional locations**: Some use ternary with SourceLocation()
   - Example: `cppElse ? IS->getElseLoc() : clang::SourceLocation()`
   - Solution: `cppElse ? IS->getElseLoc() : targetLoc`

3. **Multiple files in same handler**: Get targetPath per-file if needed

4. **DeclarationNameInfo in complex expressions**: Ensure targetLoc is in scope

## Testing Checklist

After refactoring:
- [ ] Build succeeds with no warnings
- [ ] SourceLocationMapper tests: 15/15 passing
- [ ] Dispatcher tests: 4/4 passing
- [ ] Handler unit tests: No regressions
- [ ] E2E tests: Generated C code has valid #line directives
- [ ] Grep confirms zero `clang::SourceLocation()` in src/dispatch/

## Next Steps

1. Complete VariableHandler POC (4 remaining lines)
2. Spawn parallel subtasks for Phase 2 (high-impact handlers)
3. Execute Phases 3-4 systematically
4. Document all changes in refactoring-log.md
