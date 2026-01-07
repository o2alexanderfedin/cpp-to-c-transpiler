# SourceLocation Mapping Research - Complete

**One-liner**: Implemented SourceLocationMapper to create valid clang::SourceLocation objects for C AST nodes using synthetic MemoryBuffers, enabling accurate source mapping and #line directives in generated C code.

**Version**: v1
**Date**: 2026-01-06
**Status**: ✅ Complete (Implementation + Tests Passing)

---

## Key Findings

### API Research (Sections 2.1-2.3)
1. **SourceManager** is central to location management - owns MemoryBuffers, assigns FileIDs
2. **SourceLocation** is opaque 32-bit offset - cannot be directly created, must use SourceManager
3. **createFileID()** registers files with MemoryBuffer (synthetic or real)
4. **getLocForStartOfFile()** and **translateLineCol()** create SourceLocations
5. Line/column queries require buffer content (newlines for lines, characters for columns)

### Experiments (Section 3)
- **4/4 experiments successful** (100% success rate)
- **Experiment 1**: File registration with MemoryBuffer ✅
- **Experiment 2**: Creating start-of-file locations ✅
- **Experiment 3**: Line/column positions with perfect round-trip accuracy ✅
- **Experiment 4**: Multiple files with distinct FileIDs and locations ✅

### Implementation (Section 4-5)
- **Class**: `SourceLocationMapper` - manages SourceManager for C files
- **Buffer Strategy**: 80 columns × 10,000 lines of spaces (~800KB/file)
- **Caching**: FileID cache prevents re-registration
- **Unit Tests**: 15 tests, 100% passing
- **Integration**: Designed to work with existing PathMapper and TargetContext

---

## Files Created

### Production Code
1. `/include/SourceLocationMapper.h` - Public API with comprehensive documentation
2. `/src/SourceLocationMapper.cpp` - Implementation with optimized buffer creation
3. Updated `/CMakeLists.txt` - Added to cpptoc_core library and test executable

### Tests
1. `/tests/SourceLocationMapperTest.cpp` - 15 unit tests (all passing):
   - RegisterFile tests (3 tests)
   - GetStartOfFile tests (3 tests)
   - GetLocation tests (6 tests)
   - MapFromCppLocation tests (2 tests)
   - GetSourceManager test (1 test)

### Research Artifacts
1. `.prompts/076-source-location-mapping-research/source-location-mapping-research.md` - Full report
2. `.prompts/076-source-location-mapping-research/experiments.cpp` - Standalone validation
3. `.prompts/076-source-location-mapping-research/CMakeLists.txt` - Experiment build config
4. `.prompts/076-source-location-mapping-research/SUMMARY.md` - This file

---

## Decisions Made

### Technical Decisions
1. **Separate SourceManager for C files** - Keeps C++ and C locations separate, cleaner design
2. **Synthetic buffers with space content** - Supports column queries, minimal memory
3. **80 columns × 10,000 lines** - Sufficient for most files, ~800KB per file
4. **Lazy registration** - Files registered on first use, cached thereafter
5. **OwnershipSourceLocationMapper owns SourceManager** - Clear ownership, no lifetime issues

### Design Decisions
1. **Single Responsibility** - Only creates SourceLocations, doesn't emit code or transform AST
2. **Dependency Inversion** - Handlers depend on interface, not SourceManager details
3. **Integration via TargetContext** - Natural fit with existing architecture
4. **Simple API** - `getStartOfFile()` for common case, `getLocation()` for specific positions

---

## Blockers

**None** - Implementation complete and tested.

---

## Next Steps

### Immediate (POC)
1. **Add SourceLocationMapper to TargetContext**
   - Create SourceLocationMapper in TargetContext constructor
   - Provide `getLocationMapper()` accessor

2. **Refactor VariableHandler as POC**
   - Update `translateVarDecl()` to use `locationMapper.getStartOfFile()`
   - Verify C VarDecl has valid SourceLocation
   - Test that CodeGenerator can query the location

3. **Verify CodeGenerator**
   - Check if CodeGenerator can print locations
   - Validate `#line` directive emission works

### Full Rollout
4. **Write Migration Guide**
   - Pattern for updating handlers
   - Before/after examples
   - Common pitfalls

5. **Migrate All Handlers** (systematic)
   - RecordHandler
   - FunctionHandler
   - MethodHandlers
   - etc.

6. **Integration Test**
   - Create end-to-end test verifying `#line` directives in generated C code
   - Verify locations map correctly

---

## References

### Official Documentation
- [Clang SourceManager API](https://clang.llvm.org/doxygen/classclang_1_1SourceManager.html)
- [Clang SourceLocation API](https://clang.llvm.org/doxygen/classclang_1_1SourceLocation.html)
- [Working with SourceLocation and SourceManager (Packt)](https://subscription.packtpub.com/book/programming/9781838824952/8/ch08lvl1sec37/working-with-sourcelocation-and-sourcemanager)

### Code Examples
- Standalone experiments: `.prompts/076-source-location-mapping-research/experiments.cpp`
- Unit tests: `tests/SourceLocationMapperTest.cpp`
- Implementation: `src/SourceLocationMapper.cpp`

---

## Metadata

**Confidence**: High
**Test Coverage**: 15 unit tests, 100% passing
**Standalone Validation**: 4 experiments, 100% successful
**Documentation**: Comprehensive (research report + API docs + this summary)
**Ready for Integration**: Yes
