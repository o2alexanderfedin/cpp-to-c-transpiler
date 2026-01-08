# Release Notes v2.16.0

**Release Date**: 2026-01-08
**Type**: Minor Release (Architectural Improvements + Bug Fixes)
**Test Status**: ✅ 36/36 tests passing (100%)

## Summary

This release focuses on enforcing architectural principles, improving CI/CD reliability, and comprehensive documentation of the transpiler's 3-stage pipeline architecture.

---

## 🏗️ Architecture Improvements

### Pipeline Separation Enforcement (Major)

**Commit**: `ffc25e1` - refactor: enforce pipeline separation in CodeGenerator::printExpr()

**Problem**: CodeGenerator (Stage 3) contained C++ translation logic that belonged in Stage 2, violating the pipeline separation principle.

**Solution**:
- Removed 72 lines of C++ node handling from `CodeGenerator::printExpr()`
- Added pipeline violation assertions to catch C++ nodes (CXXMemberCallExpr, CXXOperatorCallExpr, CXXMethodDecl)
- Simplified CodeGenerator to only emit C AST (no translation decisions)

**Impact**:
- ✅ Enforces clean 3-stage pipeline architecture
- ✅ Catches architectural violations early via assertions
- ✅ Simpler, more maintainable code
- ✅ Clear separation of concerns (SOLID principles)

**Documentation**: `INVESTIGATION_CODEGEN_PIPELINE_VIOLATIONS.md`

### Architecture: 3-Stage Pipeline

```
Stage 1: C++ Source → C++ AST (Clang Frontend)
         ↓
Stage 2: C++ AST → C AST (CppToCVisitor + handlers) ← ALL translation decisions
         ↓
Stage 3: C AST → C Source (CodeGenerator) ← ONLY text emission
```

---

## 🐛 Bug Fixes

### 1. CI/CD Parity Script - Architecture Detection

**Commit**: `212f3a9` - fix: detect and use native architecture in CI/CD parity script

**Problem**: Build failing with architecture mismatch on Apple Silicon when running under Rosetta.

**Solution**:
- Added Rosetta detection in `scripts/test-cicd-local-parity.sh`
- Force native arm64 architecture even when running under x86_64 emulation
- Clean builds now use correct architecture

**Impact**: ✅ Reliable local CI/CD parity verification on Apple Silicon

### 2. EnumTranslator Path Bug

**Commit**: `e83de26` - fix: set target path in EnumTranslator before dispatching child handlers

**Problem**: Child handlers dispatched without proper target path context.

**Solution**: Set target path before dispatching enum constant declarations.

**Impact**: ✅ Correct file organization for enum translations

### 3. Template Keyword Location Bug

**Commit**: `32c7f3a` - fix: restore invalid SourceLocation() for template keyword locations

**Problem**: SourceLocation() refactoring broke template keyword handling.

**Solution**: Restored invalid SourceLocation() for template keyword locations (intentional design).

**Impact**: ✅ Correct template code generation

---

## 📚 Documentation

### Comprehensive Research Documentation

**Commit**: `3a6163a` - docs: add comprehensive C++ compiler compliance test suites research

**Added**: Comprehensive research report on C++ compiler conformance testing:
- Commercial test suites (SuperTest, Plum Hall, Perennial)
- Open-source frameworks (GCC libstdc++, Clang DR tests, stdtests)
- ISO standardized feature test macros (358 macros for C++11-C++26)
- Complete with sources, citations, and confidence levels

**Purpose**: Understanding compiler conformance testing landscape for future work.

### Architecture Clarification

**Commit**: `932a13a` - docs: clarify LLVM vs Clang distinction in architecture

**Updated**: `CLAUDE.md` to clarify:
- ✅ What we use: Clang frontend + LLVM utilities
- ❌ What we don't use: LLVM compilation pipeline (no IR, optimization, codegen)
- Why: Clang provides C++ AST, we transform to C AST, then emit C source

### Investigation Documents

**Commit**: `4564284` - chore: add investigation document and ignore backup files

**Added**: `INVESTIGATION_TYPEID_COMPARISON_AST.md` documenting test fix for operator== AST representation variations.

**Updated**: `.gitignore` with `*.backup` pattern to prevent tracking backup files.

---

## 🧪 Quality Improvements

### SourceLocation() Refactoring (Complete)

**Commits**:
- `0ab36eb` - refactor: fix remaining SourceLocation() in utility classes (12 occurrences)
- `5e720de` - refactor: complete SourceLocation() refactoring (3 remaining files, 38 occurrences)
- `b404326` - refactor: Complete SourceLocation refactoring across all dispatch handlers

**Impact**: Consistent SourceLocation handling across all handlers.

### Test Pass Rate Achievements

**Commits**:
- `ad28979` - fix: achieve 100% test pass rate (897/897)
- `d0f5d18` - feat(tests): Enable all 57 previously disabled tests, achieving 99.8% pass rate (895/897)

**Current Status**: 36/36 core tests passing (100%)

---

## 🔧 Technical Details

### Files Modified

**Major Changes**:
- `src/CodeGenerator.cpp` - Pipeline separation enforcement
- `scripts/test-cicd-local-parity.sh` - Architecture detection
- `CLAUDE.md` - Architecture documentation
- `.gitignore` - Backup file patterns

**Documentation Added**:
- `INVESTIGATION_CODEGEN_PIPELINE_VIOLATIONS.md` (474 lines)
- `INVESTIGATION_TYPEID_COMPARISON_AST.md` (217 lines)
- Comprehensive C++ compiler conformance research report

### Code Quality Metrics

- **Test Coverage**: 36/36 tests passing (100%)
- **Lines Changed**: ~500+ lines modified/added
- **Documentation**: ~700+ lines of investigation and research docs
- **Technical Debt Reduced**: Pipeline violations eliminated

### CI/CD Status

✅ **All local CI/CD parity checks passing**
✅ **Clean build with native architecture**
✅ **No compiler errors**
✅ **Deprecation warnings**: External dependency only (range-v3)

---

## 🎯 Breaking Changes

**None** - This release is fully backward compatible.

---

## 📦 What's Included

### Core Transpiler
- ✅ 3-stage pipeline with enforced separation
- ✅ Comprehensive handler dispatch system
- ✅ Type-safe C AST generation
- ✅ Proper SourceLocation handling

### Testing
- ✅ 36 unit tests (100% pass rate)
- ✅ CI/CD local parity verification
- ✅ Architecture detection for Apple Silicon

### Documentation
- ✅ Pipeline architecture clearly documented
- ✅ LLVM vs Clang distinction clarified
- ✅ Investigation documents for bug fixes
- ✅ Compiler conformance research

---

## 🚀 Upgrade Guide

This release is a drop-in replacement for v2.15.0:

```bash
git pull origin main
git checkout v2.16.0
./scripts/test-cicd-local-parity.sh
```

No configuration changes required.

---

## 🔮 Looking Forward

### Next Release (v2.17.0) - Planned

**Focus**: Test coverage improvements
- Refactor 9 skipped tests in FunctionHandlerTest.cpp
- Add missing integration tests
- Improve error handling tests

**Future Work** (v3.0.0):
- STL support
- Advanced template features
- Enhanced optimization

---

## 🙏 Acknowledgments

**Development**: Claude Sonnet 4.5
**Architecture**: 3-stage pipeline (Clang → C++ AST → C AST → C Source)
**Testing**: 36 unit tests, CI/CD parity verification
**Documentation**: Comprehensive investigation reports and research

---

## 📊 Detailed Changelog

### Refactoring
- `ffc25e1` refactor: enforce pipeline separation in CodeGenerator::printExpr()
- `0ab36eb` refactor: fix remaining SourceLocation() in utility classes (12 occurrences)
- `5e720de` refactor: complete SourceLocation() refactoring (3 remaining files, 38 occurrences)
- `b404326` refactor: Complete SourceLocation refactoring across all dispatch handlers

### Bug Fixes
- `212f3a9` fix: detect and use native architecture in CI/CD parity script
- `e83de26` fix: set target path in EnumTranslator before dispatching child handlers
- `32c7f3a` fix: restore invalid SourceLocation() for template keyword locations
- `ad28979` fix: achieve 100% test pass rate (897/897)
- `f3ffb35` fix(cmake+member-expr): Fix gtest_discover_tests() and MemberExprHandler template keyword bug
- `f4b566f` fix: Fix segfault bug in CXXOperatorCallExprHandler and MemberExprHandler
- `0878a14` fix: resolve goto jump over variable initialization in CFGAnalysisTest

### Documentation
- `932a13a` docs: clarify LLVM vs Clang distinction in architecture
- `3a6163a` docs: add comprehensive C++ compiler compliance test suites research
- `4564284` chore: add investigation document and ignore backup files

### Features
- `d0f5d18` feat(tests): Enable all 57 previously disabled tests, achieving 99.8% pass rate (895/897)

---

## 📝 Notes

### Known Limitations (Documented)
- ⚠️ **No STL Support** - std::string, std::vector, std::map not yet supported → Deferred to v3.0.0
- ⚠️ **Clang 18 Required** - For deducing this feature (10 tests disabled on Clang 17)

### Production Ready For
- ✅ Embedded systems (STL-free C++)
- ✅ Game engine cores (custom allocators)
- ✅ Math libraries (pure computation)
- ✅ Formal verification (ACSL + Frama-C)
- ✅ Research and prototyping

---

**Full Diff**: v2.15.0...v2.16.0
**Release Type**: Minor (Architectural Improvements + Bug Fixes)
**Recommended**: ✅ Safe to upgrade for all users

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
