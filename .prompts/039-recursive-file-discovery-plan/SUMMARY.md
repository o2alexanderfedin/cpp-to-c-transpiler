# Summary: Recursive File Discovery Implementation Plan

**Created:** 2025-12-23
**Status:** Ready for Execution

---

## One-Liner

Implement automatic recursive `.cpp` file discovery using C++17 `std::filesystem` across 4 phases: core implementation, CLI integration, comprehensive testing, and documentation.

---

## Phase Breakdown

### Phase 1: Core File Discovery (2-3 hours)
**Objective:** Implement `discoverSourceFiles()` function using `std::filesystem::recursive_directory_iterator`

**Key Tasks:**
- Create file discovery function with extension filtering (`.cpp`, `.cxx`, `.cc`)
- Implement directory exclusion logic (`.git`, `.svn`, `build*`, `cmake-build-*`, hidden dirs)
- Add robust error handling (permission denied, invalid paths, empty directories)
- Return absolute paths for consistency

**Deliverables:**
- `discoverSourceFiles()` function (~100 lines)
- Helper functions: `isCppSourceFile()`, `shouldExcludeDirectory()`
- User feedback logging (discovered file count)

---

### Phase 2: CLI Integration (1-2 hours)
**Objective:** Integrate file discovery with command-line argument parsing

**Key Tasks:**
- Modify `main()` to detect auto-discovery mode (`--source-dir` without file arguments)
- Add validation to prevent conflicting options (both `--source-dir` and file list)
- Preserve backward compatibility (legacy file list mode)
- Pass discovered files to `ClangTool`

**Deliverables:**
- Updated `main()` with auto-discovery logic
- Conflict detection error messages
- Backward compatibility verification

---

### Phase 3: Testing (3-4 hours)
**Objective:** Create comprehensive test coverage for correctness and edge cases

**Key Tasks:**
- Unit tests for `discoverSourceFiles()` (8+ test cases)
  - Multiple extensions (`.cpp`, `.cxx`, `.cc`)
  - Directory exclusion (`.git`, `build*`)
  - Empty directory, non-existent directory
  - Absolute path verification
- Integration tests (3+ end-to-end scenarios)
  - Auto-discovery mode transpilation
  - Conflict detection validation
  - Legacy mode backward compatibility
- Edge case tests (symlinks, permissions, deep nesting)

**Deliverables:**
- Unit test suite (`FileDiscoveryTest`)
- Integration test script (`test-auto-discovery.sh`)
- All tests passing in CI/CD

---

### Phase 4: Documentation (1-2 hours)
**Objective:** Update all user-facing documentation with auto-discovery feature

**Key Tasks:**
- Update `README.md` with auto-discovery section and examples
- Update `MULTI_FILE_TRANSPILATION.md` with detailed guide
- Update `--source-dir` help text in `main.cpp`
- Create example documentation
- Add `CHANGELOG.md` entry

**Deliverables:**
- Updated README.md
- Updated MULTI_FILE_TRANSPILATION.md
- Updated help text
- Example documentation

---

## Decisions Needed

**Before Implementation:**
1. **Dry-run flag:** Include `--dry-run` to preview discovered files? → **Recommendation: DEFER**
2. **Custom exclusions:** Add `--exclude-dir` option for user-defined exclusions? → **Recommendation: DEFER**
3. **Empty directory handling:** Error (exit 1) or warning (exit 0)? → **Recommendation: ERROR (exit 1)**
4. **Verbosity control:** Add `--quiet`/`--verbose` flags? → **Recommendation: DEFER**

**Open for Discussion:**
- Should symlink following be configurable via `--follow-symlinks` flag? → **Recommendation: DEFER (default is NO follow)**
- Should discovery output show per-extension breakdown? → **Recommendation: OPTIONAL (medium priority)**

---

## Blockers

**None.** All dependencies verified:
- ✅ C++17 `<filesystem>` available (already in use)
- ✅ Integration point identified (`main.cpp` after `CommonOptionsParser`)
- ✅ No external dependencies required
- ✅ Research complete with high confidence (95%)

---

## Next Step

**Execute Phase 1:** Implement core `discoverSourceFiles()` function

**Recommended Approach:**
1. Create implementation in `src/main.cpp` (inline function)
2. Manual testing with `tests/` directory
3. Verify directory exclusion and extension filtering
4. Verify absolute path output
5. Proceed to Phase 2 integration

**Estimated Time to First Working Prototype:** 2-3 hours (Phase 1 + Phase 2 = working feature)

---

## Key Advantages

1. **User Experience:** Eliminate manual file enumeration for project-level transpilation
2. **Differentiation:** Clang tools (clang-tidy, clang-format) lack this feature
3. **Low Complexity:** ~100 lines of code using mature standard library APIs
4. **Cross-Platform:** `std::filesystem` works identically on Windows, Linux, macOS
5. **Backward Compatible:** Existing usage patterns unaffected

---

## Risk Assessment

- **Implementation Risk:** LOW (straightforward std::filesystem usage)
- **Performance Risk:** LOW (one-time upfront cost, not in hot path)
- **Compatibility Risk:** NONE (explicit conflict detection, backward compatible)
- **Maintenance Risk:** LOW (minimal code, stable APIs)

**Overall Confidence:** HIGH (95%)

---

## Target Behavior

**New Auto-Discovery Mode:**
```bash
cpptoc --source-dir=src/ --output-dir=build/
# Auto-discovers all .cpp, .cxx, .cc files recursively
# Excludes .git, .svn, build*, cmake-build-*, node_modules, hidden dirs
# Preserves directory structure in output
```

**Existing Legacy Mode (Unchanged):**
```bash
cpptoc file1.cpp file2.cpp --output-dir=build/
# Works exactly as before
```

**Conflict Prevention:**
```bash
cpptoc file.cpp --source-dir=src/ --output-dir=build/
# ERROR: Cannot specify both --source-dir and individual file arguments
```

---

**Total Estimated Time:** 8-11 hours
**Ready to Begin:** Yes
**Recommended Start:** Phase 1 (Core File Discovery)
