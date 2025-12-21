# Quick Wins - Phase 1 Migration Targets

These 8 files are 90%+ complete and need only 1-2 tests each to reach 100%.

## Files Ready for Completion

1. **ACSLStatementAnnotatorTest.cpp**
   - Current: 18/19 tests (95%)
   - Remaining: 1 test
   - File: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/ACSLStatementAnnotatorTest.cpp`
   - GTest: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/gtest/ACSLStatementAnnotatorTest_GTest.cpp`

2. **runtime_feature_flags_test.cpp**
   - Current: 15/16 tests (94%)
   - Remaining: 1 test
   - File: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/runtime_feature_flags_test.cpp`
   - GTest: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/gtest/RuntimeFeatureFlagsTest_GTest.cpp`

3. **CoroutineDetectorTest.cpp**
   - Current: 15/16 tests (94%)
   - Remaining: 1 test
   - File: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/CoroutineDetectorTest.cpp`
   - GTest: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/CoroutineDetectorTest_GTest.cpp`

4. **size_optimization_test.cpp**
   - Current: 14/15 tests (93%)
   - Remaining: 1 test
   - File: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/size_optimization_test.cpp`
   - GTest: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/gtest/SizeOptimizationTest_GTest.cpp`

5. **CppToCVisitorTest.cpp**
   - Current: 14/15 tests (93%)
   - Remaining: 1 test
   - File: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/CppToCVisitorTest.cpp`
   - GTest: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/CppToCVisitorTest_GTest.cpp`

6. **runtime_mode_library_test.cpp**
   - Current: 12/13 tests (92%)
   - Remaining: 1 test
   - File: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/runtime_mode_library_test.cpp`
   - GTest: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/gtest/RuntimeModeLibraryTest_GTest.cpp`

7. **runtime_mode_inline_test.cpp**
   - Current: 10/11 tests (91%)
   - Remaining: 1 test
   - File: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/runtime_mode_inline_test.cpp`
   - GTest: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/gtest/RuntimeModeInlineTest_GTest.cpp`

8. **IncludeGuardGeneratorTest.cpp**
   - Current: 9/10 tests (90%)
   - Remaining: 1 test
   - File: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/IncludeGuardGeneratorTest.cpp`
   - GTest: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/IncludeGuardGeneratorTest_GTest.cpp`

## Estimated Effort
- **Total Tests**: 8-9 tests
- **Time**: 1-2 hours
- **Impact**: 8 files reach 100% completion

## Migration Process
1. Identify the missing test in each macro-based file
2. Convert to GTest format
3. Add to corresponding GTest file
4. Verify tests pass
5. Mark original file as deprecated/migrated
