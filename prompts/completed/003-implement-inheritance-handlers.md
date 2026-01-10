<objective>
Implement complete multiple inheritance and virtual inheritance handler support for the C++ to C transpiler, following the gaps and recommendations identified in the audit report.

This task focuses on:
- Completing handler implementation following established patterns
- Integrating handlers into the 3-stage pipeline properly
- Ensuring proper C AST generation for virtual inheritance constructs
- Updating runtime configuration to mark feature as "implemented"

The implementation must follow TDD practices: write tests first (or in parallel), then implement to make them pass.
</objective>

<context>
Read the audit report first to understand current state and gaps:
@./audit-reports/inheritance-handlers-audit.md

Read project architecture and conventions:
@CLAUDE.md

This transpiler uses a **3-stage pipeline**:
1. C++ AST (from Clang) → 2. C AST (handler chain) → 3. C Source (code printer)

Key principles:
- **Stage 2 (handlers) make all translation decisions** - NOT stage 3
- Handlers create C AST nodes, NOT text output
- Follow SOLID principles: single responsibility per handler
- Use the established handler dispatch pattern (see existing handlers in `src/dispatch/`)
</context>

<requirements>
Based on the audit report, implement the identified gaps. This typically includes:

1. **Handler Completion**:
   - Complete virtual inheritance handler following the dispatch pattern
   - Ensure proper integration with RecordHandler for class translation
   - Implement virtual base tracking separate from direct base tracking

2. **VTable Generation**:
   - Modify VtableGenerator to include virtual base offsets
   - Generate Virtual Table Tables (VTT) for complex hierarchies
   - Ensure compatibility with existing virtual method infrastructure

3. **Constructor Handling**:
   - Emit offset adjustments in derived class constructors
   - Handle virtual base initialization properly
   - Coordinate with ConstructorSplitter if needed

4. **C AST Representation**:
   - Ensure virtual bases are properly represented in C AST
   - Create appropriate struct definitions with correct memory layout
   - Generate proper offset calculation code

5. **Runtime Configuration**:
   - Update runtime feature flags to mark virtual inheritance as "implemented"
   - Ensure runtime library has necessary support functions
   - Update documentation and configuration files
</requirements>

<implementation>
Follow TDD practices religiously:

1. **Write tests first** (or implement tests in parallel with code):
   - Unit tests for each handler component
   - Use existing test patterns (see tests/ directory)
   - Ensure tests cover edge cases (diamond inheritance, deep hierarchies)

2. **Implement incrementally**:
   - Start with simplest case (single virtual base)
   - Add complexity gradually (multiple virtual bases, diamond pattern)
   - Keep tests passing at each step

3. **Follow established patterns**:
   - Study working handlers (VirtualMethodHandler, RecordHandler)
   - Match their structure and naming conventions
   - Use the same handler registration mechanisms

4. **Integrate properly**:
   - Register handlers in the dispatch system
   - Update TranspilerAPI if needed
   - Coordinate with related handlers (don't duplicate logic)

For maximum efficiency, whenever you need to perform multiple independent operations, invoke all relevant tools simultaneously rather than sequentially.

After receiving tool results, carefully reflect on their quality and determine optimal next steps before proceeding.
</implementation>

<constraints>
- **NO text generation in handlers** - handlers create C AST nodes only
- **NO breaking existing tests** - all 41/41 current tests must continue passing
- **NO skipping tests** - comprehensive test coverage is mandatory
- **Follow existing code style** - match the project's conventions exactly
- **Update runtime configuration** - remove "not implemented" markers when done

Why these constraints matter:
- Text generation in handlers violates pipeline separation → hard to maintain
- Breaking tests indicates regression → unacceptable for production code
- Skipping tests creates technical debt → leads to bugs in production
- Inconsistent style makes code hard to read → slows down future development
- Outdated configuration misleads users → creates confusion about feature support
</constraints>

<output>
Implementation will modify/create files. The audit report specifies which files need changes.

Common files that may need updates:
- `src/dispatch/VirtualInheritanceHandler.cpp` (or similar)
- `src/VtableGenerator.cpp`
- `src/ConstructorSplitter.cpp` or `src/dispatch/ConstructorHandler.cpp`
- `include/RuntimeFeatureFlags.h`
- Handler registration code (check TranspilerAPI.cpp)

After implementation, update:
- `TO-DOS.md` - Mark virtual inheritance todo as completed
- Runtime configuration files if needed
</output>

<verification>
Before declaring implementation complete:

1. **Run all tests**:
   ```bash
   ./scripts/test-cicd-local-parity.sh
   ```
   - All existing tests must pass (41/41)
   - New tests must pass

2. **Check for compiler warnings**:
   ```bash
   cmake --build build 2>&1 | grep -i "warning:"
   ```
   - Should be zero warnings

3. **Verify handler integration**:
   - Handlers are properly registered
   - Dispatch predicates work correctly
   - No duplicate logic across handlers

4. **Test runtime configuration**:
   - Feature is marked as "implemented"
   - Runtime flags work correctly
   - Documentation is updated

5. **Manual transpilation test**:
   - Create a simple C++ file with virtual inheritance
   - Run transpiler on it
   - Verify generated C code is correct and compiles
</verification>

<success_criteria>
Implementation is complete when:

- ✅ All gaps from audit report are addressed
- ✅ All new unit tests pass
- ✅ All existing tests continue passing (41/41 or more)
- ✅ Handlers integrated into dispatch system properly
- ✅ VTable generation includes virtual base offsets
- ✅ Constructor handling emits offset adjustments
- ✅ Runtime configuration updated (no "not implemented" markers)
- ✅ Code follows established patterns and conventions
- ✅ Zero compiler warnings
- ✅ Manual transpilation test succeeds
- ✅ TO-DOS.md updated to mark completion
</success_criteria>
