# Epic #1 Implementation: Infrastructure Setup & Clang Integration

## Objective

Systematically execute all User Stories within Epic #1, one-by-one, bit-by-bit, using Test-Driven Development (TDD) and Pair Programming practices while religiously adhering to SOLID, KISS, DRY, YAGNI, TRIZ, and Emergent Design principles.

## Source of Truth

**The GitHub Project is the ONLY source of truth for Epics and User Stories.**

- GitHub Project: https://github.com/users/o2alexanderfedin/projects/14
- Epic #1 Issue: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/1

## Your Task

You are a senior software engineer implementing Epic #1. You will work systematically through each User Story, following strict engineering discipline.

## Discovery Phase

1. **Discover Epic #1 Details**
   - Use `gh issue view 1` to get Epic #1 details
   - Identify all User Stories linked to Epic #1
   - Read each User Story issue to understand requirements

2. **Identify User Stories**
   - Use GitHub CLI to list all User Stories for Epic #1
   - They should be linked in the Epic #1 issue body or comments
   - Verify dependencies between stories

3. **Understand Current State**
   - Check repository structure
   - Identify what exists already
   - Determine starting point

## Implementation Process

### For Each User Story (In Order):

#### 1. Story Understanding
- Read the User Story issue from GitHub
- Understand acceptance criteria
- Identify dependencies (must be complete before starting)
- List deliverables

#### 2. Test-First Approach (TDD)
- **Red**: Write failing test first
  - Start with the simplest test case
  - Test should fail because feature doesn't exist yet
  - Commit: "test: add failing test for [feature]"

- **Green**: Write minimal code to pass
  - Implement ONLY what's needed to pass the test
  - No gold-plating, no future-proofing
  - Commit: "feat: implement [feature] to pass test"

- **Refactor**: Improve code quality
  - Apply SOLID principles
  - Eliminate duplication (DRY)
  - Simplify (KISS)
  - Remove unnecessary code (YAGNI)
  - Commit: "refactor: improve [feature] implementation"

#### 3. Engineering Principles

**SOLID Principles:**
- **S**ingle Responsibility: Each class/function has one reason to change
- **O**pen/Closed: Open for extension, closed for modification
- **L**iskov Substitution: Derived classes must be substitutable for base classes
- **I**nterface Segregation: Many specific interfaces > one general interface
- **D**ependency Inversion: Depend on abstractions, not concretions

**KISS (Keep It Simple, Stupid):**
- Prefer simple solutions over complex ones
- If you can't explain it simply, simplify it
- Avoid premature abstraction

**DRY (Don't Repeat Yourself):**
- Extract common functionality
- One source of truth for each piece of knowledge
- Reuse, don't duplicate

**YAGNI (You Aren't Gonna Need It):**
- Don't build features until they're actually needed
- Implement only what the current User Story requires
- Resist the urge to add "nice to have" features

**TRIZ (Theory of Inventive Problem Solving):**
- Identify contradictions in requirements
- Apply proven patterns to resolve contradictions
- Seek the "Ideal Final Result" - simplest solution possible

**Emergent Design:**
- Let design emerge from requirements
- Don't over-design upfront
- Refactor continuously as understanding grows
- Trust that good design will emerge from disciplined practice

#### 4. Pair Programming Mindset

Think aloud as if programming with a partner:
- Explain your reasoning before writing code
- Question your assumptions
- Ask yourself: "Is there a simpler way?"
- Narrate your thought process
- Consider alternative approaches

#### 5. Commit Strategy

Follow conventional commits:
- `test: [description]` - Adding tests
- `feat: [description]` - New features
- `fix: [description]` - Bug fixes
- `refactor: [description]` - Code improvements without behavior change
- `docs: [description]` - Documentation changes
- `chore: [description]` - Build system, dependencies

Each commit should:
- Be atomic (one logical change)
- Have a clear, descriptive message
- Pass all tests

#### 6. Story Completion

Before marking a story as complete:
- [ ] All acceptance criteria met
- [ ] All tests pass
- [ ] Code follows SOLID principles
- [ ] No obvious duplication (DRY)
- [ ] No unnecessary complexity (KISS, YAGNI)
- [ ] Committed with proper messages
- [ ] Update User Story issue with progress
- [ ] Move to next story in dependency order

## Implementation Order

**Epic #1 User Stories (Sequential):**

1. **Story #5**: CMake Build System Configuration (5 points)
   - No dependencies
   - Start here

2. **Story #6**: Clang LibTooling Integration (5 points)
   - Depends on: Story #5

3. **Story #7**: RecursiveASTVisitor Skeleton (3 points)
   - Depends on: Story #6

4. **Story #8**: Build Documentation (2 points)
   - Depends on: Stories #5, #6, #7

## TDD Example Workflow

```bash
# Story #5: CMake Build System
# Step 1: RED - Write failing test
cat > tests/build_test.sh << 'EOF'
#!/bin/bash
# Test: CMakeLists.txt exists
test -f CMakeLists.txt || exit 1
# Test: Can configure
cmake -B build -DCMAKE_BUILD_TYPE=Debug || exit 1
# Test: Can build
cmake --build build || exit 1
# Test: Executable exists
test -f build/cpptoc || exit 1
EOF
chmod +x tests/build_test.sh

# Run test (should fail)
./tests/build_test.sh  # FAILS - CMakeLists.txt doesn't exist yet

# Commit failing test
git add tests/build_test.sh
git commit -m "test: add build system integration test"

# Step 2: GREEN - Implement minimal solution
cat > CMakeLists.txt << 'EOF'
cmake_minimum_required(VERSION 3.20)
project(cpptoc CXX)
set(CMAKE_CXX_STANDARD 17)

find_package(Clang REQUIRED CONFIG)
find_package(LLVM REQUIRED CONFIG)

add_executable(cpptoc src/main.cpp)
target_link_libraries(cpptoc
    clangTooling
    clangFrontend
    clangAST
    clangBasic
)
EOF

mkdir -p src
cat > src/main.cpp << 'EOF'
int main() {
    return 0;
}
EOF

# Run test (should pass)
./tests/build_test.sh  # PASSES

# Commit implementation
git add CMakeLists.txt src/main.cpp
git commit -m "feat: add CMake build system with Clang/LLVM integration"

# Step 3: REFACTOR - Improve if needed
# (In this case, minimal implementation is already clean)
```

## Success Criteria

Epic #1 is complete when:
- [ ] All 4 User Stories (#5-8) marked as Done in GitHub Project
- [ ] Tool compiles and runs on both macOS and Linux
- [ ] Tool can parse simple C++ file and access AST
- [ ] All tests pass
- [ ] Code committed to develop branch
- [ ] README documents build and usage

## Important Notes

1. **Do NOT read documentation files** (USER-STORIES.md, EPICS.md, etc.) - they are for human reference only
2. **GitHub Project and Issues are the source of truth** - always check there for current status
3. **One story at a time** - don't jump ahead
4. **Test first, always** - never write implementation before tests
5. **Commit frequently** - after each TDD cycle (red, green, refactor)
6. **Update GitHub issues** - comment on progress, mark complete when done

## Getting Started

```bash
# 1. Discover Epic #1 User Stories
gh issue view 1

# 2. List all related User Stories (they should be #5, #6, #7, #8)
gh issue list --label "epic-1" --state all

# 3. Start with Story #5
gh issue view 5

# 4. Begin TDD cycle
# - Write test
# - Run (fails)
# - Implement
# - Run (passes)
# - Refactor
# - Commit

# 5. Repeat for each story in order
```

## Questions to Ask Yourself

Before writing any code:
- What is the simplest test I can write?
- What is the minimal code to pass this test?
- Am I following SOLID principles?
- Is this code simple enough? (KISS)
- Am I duplicating anything? (DRY)
- Am I building something I don't need yet? (YAGNI)
- Is there a pattern that can help? (TRIZ)

## Output Format

For each User Story, provide:
1. Story summary from GitHub issue
2. List of tests written (with pass/fail status)
3. Implementation approach (thinking aloud)
4. Code written
5. Refactoring done
6. Commits made
7. Story completion status

## Begin

Start by discovering Epic #1 details from GitHub and then systematically work through each User Story using the TDD cycle described above.

Remember: **GitHub Project is your source of truth. Test first, always. Keep it simple.**
