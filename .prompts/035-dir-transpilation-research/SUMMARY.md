# Directory-Based Transpilation Research - Summary

## One-Liner Recommendation

**Implement opt-in directory structure preservation using `--preserve-structure` and `--source-root` flags with C++17 `<filesystem>` for relative path calculation, mirroring TypeScript/Babel behavior while maintaining backward compatibility.**

## Key Findings

1. **Current Implementation Problem**: `FileOutputManager::getBaseName()` strips ALL path information (line 30), causing flat output directory structure that leads to name collisions and loss of project organization in real-world multi-directory codebases.

2. **Industry Standard Behavior**: Both TypeScript (`rootDir`/`outDir`) and Babel (`src` → `lib`) preserve source directory structure automatically. Transpilers (unlike compilers) are expected to mirror directory hierarchies.

3. **Real-World Need Confirmed**: cpptoc's own test projects (`tests/real-world/json-parser`, `logger`, etc.) use `src/` and `tests/` subdirectories, demonstrating that real C++ projects require structure preservation to avoid name collisions and maintain logical organization.

4. **Technical Feasibility**: C++17 `<filesystem>` is already available in the codebase (used in `MultiFileTranspilationTest.cpp`), providing cross-platform path operations (`lexically_relative()`, `weakly_canonical()`, `create_directories()`).

5. **Backward Compatibility Strategy**: Implement as opt-in feature (`--preserve-structure` flag defaults to `false`) to avoid breaking existing workflows while enabling advanced directory-based transpilation.

## Decisions Needed

1. **CLI Flag Names**:
   - Proposed: `--preserve-structure` and `--source-root`
   - Alternative: `--mirror-dirs` and `--root-dir`
   - Decision: Choose final flag names

2. **Default Behavior**:
   - Proposed: `--preserve-structure` defaults to `false` (backward compatible)
   - Alternative: Auto-enable when `--source-root` is specified
   - Decision: Confirm default behavior

3. **Out-of-Tree Files**:
   - Proposed: Error if input file is outside `--source-root` (matches TypeScript)
   - Alternative: Fall back to basename with warning (more lenient)
   - Decision: Choose error handling strategy

4. **Future Enhancement Priority**:
   - Auto-detection of common parent directory (Phase 2)
   - `--source-dir` flag for recursive directory processing (Phase 3)
   - Decision: Prioritize these enhancements or defer

## Blockers

**None identified.** All technical prerequisites are met:
- C++17 `<filesystem>` available
- Cross-platform path handling already working
- Clear implementation path documented

## Next Step

**Proceed to planning phase** to:
1. Design detailed implementation plan for FileOutputManager changes
2. Define test cases for directory structure preservation
3. Specify CLI flag behavior and validation logic
4. Create implementation task breakdown

**Estimated Implementation Effort**: 4-6 hours total
- FileOutputManager modifications: ~2 hours
- CLI integration and validation: ~1 hour
- Comprehensive tests: ~2-3 hours

---

**Research Complete**: Ready for implementation planning.
**Full Research Document**: `dir-transpilation-research.md`
