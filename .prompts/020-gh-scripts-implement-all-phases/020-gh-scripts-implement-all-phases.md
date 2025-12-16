<objective>
Implement all 5 phases of the GitHub Projects scripts redesign following Test-Driven Development (TDD), Emergent Design, and Pair Programming principles.

Execute the complete implementation plan from @.prompts/019-gh-scripts-redesign-plan/gh-scripts-redesign-plan.md, creating 32 SOLID/KISS/DRY/YAGNI-compliant scripts with comprehensive test coverage.

**Critical methodologies:**
- **TDD**: Write failing tests first, minimal code to pass, then refactor
- **Emergent Design**: Let design evolve from tests, avoid over-engineering
- **Pair Programming**: Explain reasoning, review code, discuss trade-offs

**Why this matters:** Current scripts violate fundamental principles. This implementation replaces them with simple, tested, maintainable tools.
</objective>

<context>
**Foundation documents:**
- Research: @.prompts/018-gh-scripts-redesign-research/gh-scripts-redesign-research.md
- Plan: @.prompts/019-gh-scripts-redesign-plan/gh-scripts-redesign-plan.md

**Implementation scope:**
- Phase 1: Foundation (common library, config)
- Phase 2: Project CRUD (4 scripts)
- Phase 3: Epic & Story CRUD (10 scripts)
- Phase 4: Task/Spike/Bug CRUD (15 scripts)
- Phase 5: Migration (archive old, update skills, verify)

**Total deliverables:** 32 scripts + tests + migration

**Estimated effort:** 19-26 hours (with TDD overhead)
</context>

<tdd_methodology>
<principles>
**Test-Driven Development (TDD) cycle:**

1. **RED** - Write a failing test
   - Test describes desired behavior
   - Test must fail initially (proves it's testing something)
   - Keep test simple and focused

2. **GREEN** - Write minimal code to pass
   - Simplest implementation that makes test pass
   - Don't add features not tested
   - Duplication is OK at this stage

3. **REFACTOR** - Improve code while keeping tests green
   - Eliminate duplication
   - Improve names
   - Extract functions
   - Tests must still pass

**Repeat for each feature/function.**
</principles>

<test_structure>
**For each script, create test file:**
```bash
# Location: ~/.claude/skills/lib/gh-projects/tests/{script-name}_test.sh

# Test framework: Use bats (Bash Automated Testing System)
# Install if needed: brew install bats-core

# Test structure:
#!/usr/bin/env bats

setup() {
  # Setup test environment
  # Mock gh CLI if needed
  # Create temp files
}

teardown() {
  # Cleanup after tests
  # Remove temp files
}

@test "descriptive test name" {
  # Arrange: Setup test data
  # Act: Run the script/function
  # Assert: Verify expected outcome

  run command_to_test arg1 arg2
  [ "$status" -eq 0 ]
  [[ "$output" =~ "expected pattern" ]]
}
```
</test_structure>

<testing_strategy>
**Test pyramid:**
1. **Unit tests** (70%) - Test individual functions in common.sh
2. **Integration tests** (20%) - Test scripts end-to-end with mocked gh CLI
3. **Manual tests** (10%) - Test with real GitHub API (document in TESTING.md)

**Test coverage requirements:**
- All common.sh functions: 100% coverage
- All scripts: Happy path + error cases
- All exit codes: Verified
- All error messages: Verified

**Mocking strategy:**
- Create `tests/mocks/gh` script that simulates gh CLI
- Use environment variable to enable mocking
- Document mock responses for each test case
</testing_strategy>
</tdd_methodology>

<emergent_design>
<principles>
**Emergent Design:**
- Design evolves from tests and refactoring
- Don't design the whole system upfront
- Start with simplest solution that works
- Let patterns emerge naturally
- Refactor when duplication appears (Rule of Three)

**Red flags (over-engineering):**
- Creating abstractions before needed
- Designing for hypothetical future requirements
- Complex inheritance hierarchies
- More than 2 levels of indirection

**When to extract:**
- When same code appears 3 times (Rule of Three)
- When function exceeds 20 lines
- When naming becomes awkward
- When tests become difficult to write
</principles>

<refactoring_triggers>
**Common refactorings in this project:**
1. **Extract function** - When code block does one thing
2. **Extract variable** - When expression is complex
3. **Rename** - When better name emerges
4. **Consolidate duplicate code** - After 3rd repetition
5. **Simplify conditional** - When nesting > 2 levels
6. **Replace magic number with constant** - Always
</refactoring_triggers>
</emergent_design>

<pair_programming>
<technique>
**Pair Programming approach:**

**Driver role (writes code):**
- Explain what you're about to write
- Think aloud while typing
- Ask for input on unclear decisions

**Navigator role (reviews):**
- Watch for syntax errors, edge cases
- Suggest improvements
- Think strategically about design

**Since this is Claude-to-Claude:**
- Document reasoning in comments
- Explain trade-offs in commit messages
- Create DECISIONS.md for architectural choices
</technique>

<collaboration_points>
**Key collaboration moments:**
1. Before writing each script: "Here's my plan..."
2. Before refactoring: "I notice duplication in..."
3. When tests fail: "Investigating why..."
4. After completing phase: "Review before next phase..."

**Questions to ask yourself (as pair partner):**
- Is this the simplest thing that could work?
- Am I testing behavior or implementation?
- Could this be clearer?
- What edge cases am I missing?
- Is this YAGNI or actually needed?
</collaboration_points>
</pair_programming>

<implementation_phases>
<phase_1_foundation>
<name>Phase 1: Foundation</name>
<deliverables>
1. Enhanced common.sh library
2. Configuration management
3. Test framework setup
4. Mock infrastructure
</deliverables>

<tdd_approach>
**Test-first order:**

1. **Test: Configuration loading**
   ```bash
   @test "loads config from file"
   @test "environment variables override config file"
   @test "CLI flags override environment variables"
   @test "auto-detects from git remote"
   @test "auto-detects from gh auth status"
   ```

2. **Test: PATH handling**
   ```bash
   @test "gh wrapper finds gh in standard locations"
   @test "gh wrapper adds homebrew to PATH"
   @test "gh wrapper fails gracefully when gh not found"
   ```

3. **Test: Field name handling**
   ```bash
   @test "normalizes field names to lowercase"
   @test "handles Type/type correctly"
   @test "handles Status/status correctly"
   ```

4. **Test: High-level functions**
   ```bash
   @test "create_repo_issue creates issue and returns URL"
   @test "add_issue_to_project adds to project and returns item_id"
   @test "set_item_field updates field by name"
   @test "get_item_by_issue finds item from issue number"
   @test "list_items_by_type filters by Type field"
   ```

**Write each test, see it fail (RED), then implement (GREEN), then refactor.**
</tdd_approach>

<acceptance_criteria>
- [ ] All common.sh functions have unit tests
- [ ] All tests pass
- [ ] Configuration loads from all sources with correct precedence
- [ ] PATH issue resolved (gh always found)
- [ ] Mock infrastructure works for integration tests
- [ ] README.md documents testing approach
</acceptance_criteria>
</phase_1_foundation>

<phase_2_project_crud>
<name>Phase 2: Project CRUD</name>
<deliverables>
1. gh-project-create.sh + tests
2. gh-project-list.sh + tests
3. gh-project-update.sh + tests
4. gh-project-delete.sh + tests
</deliverables>

<tdd_approach>
**For each script:**

1. Write tests for happy path
2. Write tests for error cases
3. Write tests for --help
4. Implement script to pass tests
5. Refactor for clarity

**Example for gh-project-create.sh:**
```bash
@test "creates project with title"
@test "creates project with title and description"
@test "returns project number on success"
@test "fails when title is missing"
@test "fails when gh CLI not authenticated"
@test "shows help with --help flag"
@test "exits with code 0 on success"
@test "exits with code 2 when arguments invalid"
```

**Emergent design questions:**
- Do all CRUD scripts share similar structure?
- Can we extract common arg parsing?
- When does duplication warrant extraction?
</tdd_approach>

<acceptance_criteria>
- [ ] All 4 project scripts implemented with tests
- [ ] All tests pass (unit + integration)
- [ ] Help text follows standard format
- [ ] Error messages are helpful
- [ ] Exit codes follow conventions
- [ ] Scripts work with real GitHub API (manual test)
</acceptance_criteria>
</phase_2_project_crud>

<phase_3_epic_story_crud>
<name>Phase 3: Epic & Story CRUD</name>
<deliverables>
1. Epic scripts (5): create, list, update, delete, link
2. Story scripts (5): create, list, update, delete, link
3. All with comprehensive tests
</deliverables>

<tdd_approach>
**Pattern emerges:**
- Create scripts follow same pattern
- List scripts follow same pattern
- Update scripts follow same pattern
- Link scripts are unique to Epic/Story

**Emergent design:**
1. Implement gh-epic-create.sh with TDD
2. Implement gh-story-create.sh with TDD
3. **Notice duplication** - Both scripts ~80% similar
4. **Decision point:** Extract or keep separate?
   - **Keep separate** if difference matters (type-specific validation)
   - **Extract** if purely duplicated (template function)
5. Document decision in DECISIONS.md

**Parent-child relationships:**
- Story can link to Epic
- Test bidirectional linking
- Test orphan stories (no parent)
</tdd_approach>

<acceptance_criteria>
- [ ] All 10 Epic/Story scripts implemented with tests
- [ ] All tests pass
- [ ] Parent-child linking works correctly
- [ ] Pattern consistency across similar scripts
- [ ] Duplication eliminated where appropriate
- [ ] DECISIONS.md documents design choices
</acceptance_criteria>
</phase_3_epic_story_crud>

<phase_4_task_spike_bug_crud>
<name>Phase 4: Task/Spike/Bug CRUD</name>
<deliverables>
1. Task scripts (5): create, list, update, delete, link
2. Spike scripts (4): create, list, update, delete
3. Bug scripts (6): create, list, update, delete, close, reopen
4. Generic item script (1): fallback for other types
</deliverables>

<tdd_approach>
**Leverage pattern:**
- Pattern established in Phase 3
- Reuse test templates
- Faster implementation (pattern reuse)

**Bug-specific behavior:**
- close.sh sets Status to "Done" + adds close comment
- reopen.sh sets Status to "Todo" + adds reopen comment
- Test state transitions

**Generic item script:**
- Tests for unknown types
- Graceful handling
- Helpful error messages
</tdd_approach>

<acceptance_criteria>
- [ ] All 15 Task/Spike/Bug scripts implemented with tests
- [ ] All tests pass
- [ ] Bug state transitions work correctly
- [ ] Generic script handles edge cases
- [ ] Pattern consistency maintained
- [ ] No regression in earlier phases
</acceptance_criteria>
</phase_4_task_spike_bug_crud>

<phase_5_migration>
<name>Phase 5: Migration and Testing</name>
<deliverables>
1. Archive old scripts to legacy directory
2. Update 4 skills to use new scripts
3. End-to-end testing with real API
4. Migration guide documentation
5. TESTING.md with manual test procedures
</deliverables>

<tdd_approach>
**Verification tests:**
- Create tests that compare old vs new behavior
- Ensure no regressions
- Document breaking changes

**Skill updates:**
- Update execute-epic.skill.md
- Update execute-user-story.skill.md
- Update epic-to-user-stories.skill.md
- Update prd-to-epics.skill.md

**End-to-end test scenarios:**
1. Create epic → add stories → list stories by epic
2. Create bug → close bug → verify status
3. Link story to epic → verify bidirectional
4. Use all output formats (json, table, csv)
</tdd_approach>

<acceptance_criteria>
- [ ] Old scripts archived to gh-projects-legacy/
- [ ] All 4 skills updated and tested
- [ ] End-to-end scenarios pass
- [ ] Migration guide complete
- [ ] TESTING.md documents manual procedures
- [ ] No regressions from old functionality
- [ ] All scripts work with real GitHub API
</acceptance_criteria>
</phase_5_migration>
</implementation_phases>

<workflow>
**For each phase:**

1. **Planning (Pair Programming)**
   - Review phase requirements
   - List all tests to write
   - Identify potential design decisions

2. **TDD Cycle (Red-Green-Refactor)**
   - Write first test (RED)
   - Implement minimal code (GREEN)
   - Refactor if needed
   - Repeat for next test

3. **Emergent Design (Continuous)**
   - Notice patterns after 2nd repetition
   - Extract on 3rd repetition (Rule of Three)
   - Keep design simple and focused

4. **Phase Review (Pair Programming)**
   - Review all code written
   - Check for missed edge cases
   - Verify acceptance criteria
   - Document design decisions

5. **Integration**
   - Run all tests (current + previous phases)
   - Verify no regressions
   - Manual test with real API

6. **Proceed to next phase**
</workflow>

<output_organization>
**Directory structure:**
```
~/.claude/skills/lib/gh-projects/
├── lib/
│   └── common.sh                 # Enhanced common library
├── tests/
│   ├── common_test.sh            # Unit tests for common.sh
│   ├── gh-project-create_test.sh
│   ├── gh-epic-create_test.sh
│   ├── ... (all script tests)
│   └── mocks/
│       └── gh                    # Mock gh CLI
├── gh-project-create.sh
├── gh-project-list.sh
├── gh-epic-create.sh
├── ... (all 32 scripts)
├── TESTING.md                    # Testing guide
├── DECISIONS.md                  # Design decisions log
└── README.md                     # Usage guide

~/.claude/skills/lib/gh-projects-legacy/
└── ... (archived old scripts)
```
</output_organization>

<documentation_requirements>
**Create during implementation:**

1. **TESTING.md**
   - How to run tests
   - How to run specific test suites
   - Manual testing procedures
   - Mock infrastructure explanation

2. **DECISIONS.md**
   - Architectural decisions made
   - Trade-offs considered
   - Patterns that emerged
   - Refactorings performed

3. **README.md**
   - Overview of new script architecture
   - Quick start examples
   - Configuration guide
   - Migration notes

4. **MIGRATION.md**
   - Old script → new script mapping
   - Breaking changes explained
   - Update checklist
   - Rollback procedure
</documentation_requirements>

<quality_gates>
**Before proceeding to next phase:**

1. **All tests pass** - No failing tests
2. **Test coverage** - All functions covered
3. **Manual verification** - Scripts work with real API
4. **Code review** - Self-review for clarity
5. **Documentation** - Phase documented
6. **No regressions** - Previous phases still work
</quality_gates>

<success_criteria>
**Overall project success:**

- [ ] All 32 scripts implemented with TDD
- [ ] All tests pass (unit + integration)
- [ ] Test coverage >90% for common.sh
- [ ] All scripts have integration tests
- [ ] Manual tests documented and verified
- [ ] Old scripts archived
- [ ] Skills updated and tested
- [ ] Migration guide complete
- [ ] No regressions
- [ ] SOLID/KISS/DRY/YAGNI principles evident
- [ ] Design emerged naturally from tests
- [ ] All decisions documented

**Time budget:** 19-26 hours total
- Phase 1: 4-6 hours (foundation)
- Phase 2: 2-3 hours (project CRUD)
- Phase 3: 6-8 hours (epic/story)
- Phase 4: 4-5 hours (task/spike/bug)
- Phase 5: 3-4 hours (migration)
</success_criteria>

<execution_notes>
**TDD discipline:**
- Never write production code without a failing test
- Keep tests simple and focused
- One assertion per test (when possible)
- Test behavior, not implementation

**Emergent design discipline:**
- Wait for the third repetition before extracting
- Keep functions small (<20 lines)
- Rename as better names emerge
- Don't anticipate future requirements

**Pair programming discipline:**
- Explain before implementing
- Think aloud
- Ask for code review
- Document decisions

**If you get stuck:**
- Write a test for the simplest case
- Make it pass with the simplest code
- Add more tests to drive complexity
- Let design emerge

**Remember:** The goal is simple, tested, maintainable scripts. Not clever code.
</execution_notes>
