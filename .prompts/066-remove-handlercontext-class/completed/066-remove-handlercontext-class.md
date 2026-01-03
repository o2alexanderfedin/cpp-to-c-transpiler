<objective>
Delete the HandlerContext class and all related infrastructure, completing the architectural migration to the CppToCVisitorDispatcher pattern.

WHY this matters: HandlerContext is now obsolete legacy code with zero usage. Removing it eliminates technical debt, reduces codebase complexity, and prevents future developers from accidentally using the deprecated pattern.
</objective>

<context>
Project: C++ to C transpiler
Current State: All code migrated to dispatcher pattern

HandlerContext retirement status (should be verified before deletion):
- E2E tests: 100% migrated ✓
- Unit tests: 100% migrated ✓
- Integration tests: 100% migrated ✓
- Production code: 100% migrated ✓
- Active code references: 0

Files to delete:
@include/handlers/HandlerContext.h
@src/handlers/HandlerContext.cpp

Files that may reference HandlerContext (check before deletion):
@CMakeLists.txt (may have HandlerContext in build targets)
@ARCHITECTURE.md or similar docs (may reference old pattern)

Review CLAUDE.md for project conventions.
</context>

<requirements>

1. **Verify Zero Usage** (CRITICAL - do not delete if any usage found):
   ```bash
   # Comprehensive search for HandlerContext usage
   grep -r "HandlerContext" include/ src/ tests/ --include="*.cpp" --include="*.h" \
     | grep -v "DEPRECATED\|Historical\|//.*HandlerContext"

   # Should return 0 active code references
   # Comments and documentation references are OK
   ```

2. **Delete HandlerContext Files**:
   - Remove `include/handlers/HandlerContext.h`
   - Remove `src/handlers/HandlerContext.cpp`
   - Check for any HandlerContext-related helper files

3. **Update Build System**:
   - Remove HandlerContext from CMakeLists.txt build targets
   - Remove any HandlerContext-specific compilation flags
   - Verify build succeeds after removal

4. **Update Documentation**:
   - Update ARCHITECTURE.md to reflect dispatcher-only pattern
   - Remove HandlerContext from any design documents
   - Add migration notes explaining the change (historical context)

5. **Verify No Breakage**:
   - All tests must still pass
   - Build must succeed
   - No link errors or missing symbols

</requirements>

<implementation>

**Step 1: Final Verification**

Before any deletion, thoroughly verify zero usage:

```bash
# Check all code files
grep -r "HandlerContext" include/ src/ tests/ \
  --include="*.cpp" --include="*.h" --include="*.hpp"

# Check CMakeLists.txt
grep "HandlerContext" CMakeLists.txt

# Check documentation
find . -name "*.md" -exec grep -l "HandlerContext" {} \;

# Expected: Only comments or historical references, no active code
```

**Step 2: Delete Files**

```bash
# Remove header
rm include/handlers/HandlerContext.h

# Remove implementation
rm src/handlers/HandlerContext.cpp

# Remove any related files (if they exist)
rm include/handlers/HandlerContext*.h 2>/dev/null || true
rm src/handlers/HandlerContext*.cpp 2>/dev/null || true
```

**Step 3: Update CMakeLists.txt**

Search for and remove HandlerContext references:
- Remove from `add_library()` or `add_executable()` source lists
- Remove any HandlerContext-specific targets
- Remove commented-out HandlerContext code

**Step 4: Update Documentation**

In ARCHITECTURE.md or similar:
- Remove HandlerContext from architecture diagrams
- Update handler pattern documentation to show only dispatcher pattern
- Add "Migration History" section documenting the change:
  ```markdown
  ## Migration History

  ### HandlerContext Retirement (2025-12-31 to 2026-01-02)

  The legacy HandlerContext pattern was fully retired and replaced with
  the CppToCVisitorDispatcher pattern. This migration:
  - Improved separation of concerns (handlers don't manage context)
  - Enabled better testability (explicit dependencies)
  - Simplified handler implementations (static registration)

  See commits: [list relevant commits]
  ```

**Step 5: Rebuild and Test**

```bash
# Clean rebuild
cmake --build build --clean-first

# Run all tests
ctest

# Verify specific test suites
ctest -R "E2E.*Test"
ctest -R "Dispatcher.*Test"
ctest -R "Integration.*Test"
```

</implementation>

<verification>

Before declaring complete, verify:

```bash
# Files deleted
! test -f include/handlers/HandlerContext.h
! test -f src/handlers/HandlerContext.cpp

# No references in active code (ignoring comments)
! grep -r "HandlerContext" include/ src/ tests/ \
    --include="*.cpp" --include="*.h" \
    | grep -v "//\|DEPRECATED\|Historical"

# Build succeeds
cmake --build build
echo $?  # Should be 0

# All tests pass
ctest
# Should show 100% pass rate with no failures

# No undefined symbols
nm build/TranspilerAPI | grep -i handlercontext
# Should return nothing
```

Check that:
- HandlerContext files no longer exist
- Build completes successfully
- All tests pass (E2E, unit, integration)
- No link errors about missing HandlerContext symbols
- Documentation updated to reflect new architecture

</verification>

<success_criteria>

1. HandlerContext.h deleted
2. HandlerContext.cpp deleted
3. Zero references to HandlerContext in active code (comments OK)
4. CMakeLists.txt cleaned of HandlerContext references
5. Documentation updated (ARCHITECTURE.md, etc.)
6. Build succeeds: `cmake --build build --clean-first`
7. All tests pass: `ctest` shows 100% pass rate
8. No link errors or missing symbols
9. Git commit created documenting the deletion

</success_criteria>

<output>

Delete files:
- `include/handlers/HandlerContext.h`
- `src/handlers/HandlerContext.cpp`

Update files:
- `CMakeLists.txt` - Remove HandlerContext from build
- `ARCHITECTURE.md` or equivalent - Document dispatcher-only pattern

Create completion report:
```
HandlerContext Deletion Complete

Files Deleted:
- include/handlers/HandlerContext.h
- src/handlers/HandlerContext.cpp

CMakeLists.txt Updates:
- Removed HandlerContext from [specific target/library]
- Build targets updated: [list]

Documentation Updates:
- ARCHITECTURE.md: Updated to dispatcher-only pattern
- Added migration history section

Verification Results:
- Build: SUCCESS
- All tests: X/X passing (100%)
- Active code references: 0
- Link errors: 0

HandlerContext Retirement: COMPLETE

The legacy HandlerContext pattern has been fully removed from the
codebase. All code now uses the modern CppToCVisitorDispatcher pattern,
providing better separation of concerns, improved testability, and
simpler handler implementations.

Migration Timeline:
- 2025-12-31 to 2026-01-02: Full migration completed
- Prompts: 060, 061, 062, 064, 065, 066
- Total commits: [X]
```

</output>
