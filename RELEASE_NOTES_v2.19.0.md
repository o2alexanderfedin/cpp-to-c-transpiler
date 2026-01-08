# Release Notes v2.19.0

**Release Date**: 2026-01-08
**Type**: Minor Release (Configuration & Code Quality)
**Test Status**: ✅ 910/910 tests passing (100%)

## Summary

This release completes the PipelineConfig CLI accessor implementation, ensuring all command-line options are properly read and applied instead of using hardcoded defaults.

---

## 🔧 Configuration Improvements

### PipelineConfig CLI Accessor Completion (Major)

**Commit**: `8232d41` - refactor: complete PipelineConfig CLI accessor implementation

**Problem**: PipelineConfig.cpp had 2 TODO comments indicating missing accessors for ACSL and exception handling options. These accessors already existed in main.cpp but were not declared or used in PipelineConfig.cpp, causing the configuration to use hardcoded defaults instead of respecting user CLI flags.

**Affected Options**:
- `--acsl-level` (Basic/Full) - Ignored, always used Basic
- `--acsl-output` (Inline/Separate) - Ignored, always used Inline
- `--acsl-memory-predicates` - Ignored, always false
- `--exception-model` (sjlj/tables) - Ignored, always used sjlj

**Solution**:
- Added extern declarations for existing main.cpp accessors:
  * `getACSLLevel()` - returns `::ACSLLevel` (from ACSLGenerator.h)
  * `getACSLOutputMode()` - returns `::ACSLOutputMode` (from ACSLGenerator.h)
  * `shouldGenerateMemoryPredicates()` - returns bool
  * `getExceptionModel()` - returns std::string ("sjlj"/"tables")

- Implemented type-safe conversions in `parseCLIArgs()`:
  * `::ACSLLevel` → `pipeline::ACSLCoverageLevel`
  * `::ACSLOutputMode` → `pipeline::ACSLOutputMode`
  * `std::string` → `pipeline::ExceptionModel`

- Removed both TODO comments

**Impact**:
- ✅ CLI options now properly affect transpiler behavior
- ✅ No more hardcoded configuration defaults
- ✅ Type-safe conversion between different enum namespaces
- ✅ All 910 tests passing (100%)

**Code Changes**:
```cpp
// Added include for external enum types
#include "ACSLGenerator.h"

// Added extern declarations
extern ::ACSLLevel getACSLLevel();
extern ::ACSLOutputMode getACSLOutputMode();
extern bool shouldGenerateMemoryPredicates();
extern std::string getExceptionModel();

// Implemented conversions
::ACSLLevel acslLevel = getACSLLevel();
config.acslCoverageLevel = (acslLevel == ::ACSLLevel::Basic)
    ? ACSLCoverageLevel::Basic
    : ACSLCoverageLevel::Full;
```

---

## 📊 Codebase Health

### Technical Debt Analysis

**TODOs Resolved**: 2 (down from 29 to 27)
- ✅ PipelineConfig.cpp:37 - ACSL accessors
- ✅ PipelineConfig.cpp:48 - Exception model accessor

**Remaining TODOs**: 27 items
- **Easy**: 0 items (all easy items completed)
- **Medium**: 12 items (handler improvements, type lookup, feature implementations)
- **Complex**: 15 items (architectural changes, ACSL deep analysis)

**Code Quality Metrics**:
- **Lines Changed**: 24 insertions, 8 deletions (net +16)
- **Test Coverage**: 910/910 (100%)
- **Build Status**: Clean with no errors
- **Configuration**: Fully functional CLI option parsing

---

## 🎯 Breaking Changes

**None** - This release is fully backward compatible.

**Behavior Change** (Bug Fix):
- Users setting CLI flags for ACSL/exception options will now see those options respected
- Previously these flags were silently ignored and defaults were used
- This is a **bug fix**, not a breaking change

---

## 📦 What's Included

### Core Transpiler
- ✅ 3-stage pipeline with enforced separation
- ✅ Comprehensive handler dispatch system
- ✅ Type-safe C AST generation
- ✅ Proper SourceLocation handling
- ✅ Full CLI configuration support (NEW)

### Configuration System
- ✅ Complete ACSL option parsing (level, output mode, memory predicates)
- ✅ Complete exception handling option parsing (model selection)
- ✅ Template, RTTI, and dependency analysis options
- ✅ Type-safe conversion between different enum namespaces

### Testing
- ✅ 910 tests (100% pass rate) - Comprehensive coverage across all features
- ✅ CI/CD local parity verification
- ✅ Pre-push hook enforcement

### Documentation
- ✅ Release notes for all versions
- ✅ Architecture documentation (CLAUDE.md)
- ✅ Investigation documents for decisions

---

## 🚀 Upgrade Guide

This release is a drop-in replacement for v2.18.0:

```bash
git pull origin main
git checkout v2.19.0
./scripts/test-cicd-local-parity.sh
```

**Important for Users**:
If you've been setting ACSL or exception handling CLI flags and wondering why they weren't working, this release fixes that! Your flags will now be properly respected.

---

## 🔮 Looking Forward

### Next Release (v2.20.0) - Potential Focus Areas

**Medium Complexity TODOs**:
- Declaration ordering (DeclRefExprHandler.cpp:63)
- Range-based for loop translation (StatementHandler.cpp:411)
- Full DeclStmt translation (StatementHandler.cpp:687)
- Exception frame management (TryCatchTransformer.cpp:44,76,110)

**Implementation Focus**:
- Handler improvements for better type system integration
- Statement translation completeness
- Exception handling robustness

**Future Work** (v3.0.0):
- STL support (deferred from earlier roadmap)
- Advanced template features
- Enhanced optimization passes

---

## 🙏 Acknowledgments

**Development**: Claude Sonnet 4.5
**Architecture**: 3-stage pipeline (Clang → C++ AST → C AST → C Source)
**Testing**: 910 tests across comprehensive test suite
**Documentation**: Detailed investigation reports and release notes

---

## 📊 Detailed Changelog

### Bug Fixes
- `8232d41` refactor: complete PipelineConfig CLI accessor implementation

  **Fixed**: CLI flags for ACSL and exception handling options were being ignored

  **Impact**: Users can now control ACSL coverage level, output mode, memory predicates, and exception model via CLI flags

### Documentation
- Updated release notes
- Maintained comprehensive TODO tracking

---

## 📝 Notes

### Focus: Configuration Completeness

This release demonstrates commitment to:
- **User Control**: All CLI options now properly affect behavior
- **Type Safety**: Proper conversion between different enum namespaces
- **Code Quality**: Eliminating technical debt (2 TODOs resolved)
- **Testing**: Maintaining 100% test pass rate

### Production Ready For
- ✅ Embedded systems (STL-free C++)
- ✅ Game engine cores (custom allocators)
- ✅ Math libraries (pure computation)
- ✅ Formal verification (ACSL + Frama-C) - **Now with full CLI control!**
- ✅ Research and prototyping

### Known Limitations (Documented)
- ⚠️ **No STL Support** - std::string, std::vector, std::map not yet supported → Deferred to v4.0
- ⚠️ **Clang 18+ Recommended** - For deducing this feature (some tests disabled on Clang 17)

---

## 🔍 Technical Details

### Enum Namespace Mapping

The transpiler has two separate ACSL enum definitions:

1. **ACSLGenerator.h** (global namespace): Used by ACSL generation classes
   - `enum class ACSLLevel { Basic, Full }`
   - `enum class ACSLOutputMode { Inline, Separate }`

2. **PipelineConfig.h** (cpptoc::pipeline namespace): Used by configuration
   - `enum class ACSLCoverageLevel { Basic, Full }`
   - `enum class ACSLOutputMode { Inline, Separate }`

This separation follows good design (each component has its own types), but requires conversion when passing configuration from CLI parsing to the pipeline.

**Resolution**: Added conversion logic in `parseCLIArgs()` to map between namespaces.

---

**Full Diff**: v2.18.0...v2.19.0
**Release Type**: Minor (Configuration & Code Quality)
**Recommended**: ✅ Safe to upgrade for all users
**Priority**: 🔥 **High** - Fixes bug where CLI flags were ignored

---

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
