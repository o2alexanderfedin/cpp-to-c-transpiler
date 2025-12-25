# Recursive File Discovery Research Summary

**Use `std::filesystem::recursive_directory_iterator` with `skip_permission_denied` for automatic `.cpp` file discovery when `--source-dir` specified without file arguments.**

## Key Findings

1. **C++17 API is Perfect:** `std::filesystem::recursive_directory_iterator` provides cross-platform recursive traversal with built-in options for permission handling and symlink control.

2. **Clang Tools Don't Have This:** Neither clang-tidy nor clang-format include built-in recursive file discovery - they rely on external tools. Adding this to cpptoc provides significant differentiation and user value.

3. **Implementation is Simple:** ~100 lines of code, straightforward integration point in `main()` before `ClangTool` construction. Leverage existing `--source-dir` flag semantics.

4. **Performance is Acceptable:** One-time upfront discovery cost, filesystem library is competitive with native OS APIs. Directory entry caching avoids redundant syscalls. Acceptable even for large codebases (10k+ files).

## Decisions Needed

1. **Pending:** Should `--dry-run` flag show discovered files without transpiling?
2. **Pending:** Should `--exclude-dir` allow user-defined exclusions (or just use hardcoded list)?
3. **Pending:** Warning vs error when zero files discovered in `--source-dir`?
4. **Resolved:** Do NOT follow symlinks by default (avoid circular symlink issues)
5. **Resolved:** Support `.cpp`, `.cxx`, `.cc` extensions (lowercase only, no `.C`)

## Blockers

**NONE** - All technical prerequisites verified:
- ✅ C++17 `std::filesystem` already in use
- ✅ `--source-dir` flag already exists (used for output structure preservation)
- ✅ `ClangTool` accepts file list as vector of strings
- ✅ Cross-platform compatibility confirmed
- ✅ Error handling strategies documented

## Next Step

**Create implementation plan** in `.prompts/039-recursive-file-discovery-plan/` breaking down work into 4 phases:
1. Core discovery function
2. CLI integration
3. Comprehensive testing
4. Documentation updates

---

**Research Date:** 2025-12-23
**Confidence Level:** 95% (HIGH)
**Status:** READY FOR PLANNING
