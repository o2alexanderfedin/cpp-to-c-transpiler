# Epic #2 Implementation: CNodeBuilder Helper Library

## Objective

Systematically execute all User Stories within Epic #2, one-by-one, bit-by-bit, using Test-Driven Development (TDD) and Pair Programming practices while religiously adhering to SOLID, KISS, DRY, YAGNI, TRIZ, and Emergent Design principles.

## Source of Truth

**The GitHub Project is the ONLY source of truth for Epics and User Stories.**

- GitHub Project: https://github.com/users/o2alexanderfedin/projects/14
- Epic #2 Issue: https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/2

## Your Task

You are a senior software engineer implementing Epic #2. You will work systematically through each User Story, following strict engineering discipline.

Epic #2 builds the CNodeBuilder helper library that encapsulates verbose Clang C node creation, enabling clean and maintainable C AST construction. The goal is to achieve **15x code reduction** (from 15+ lines to 1 line per node).

## Discovery Phase

1. **Discover Epic #2 Details**
   - Use `gh issue view 2` to get Epic #2 details
   - Identify all User Stories linked to Epic #2
   - Read each User Story issue to understand requirements

2. **Identify User Stories**
   - Use GitHub CLI to list all User Stories for Epic #2
   - They should be issues #9-14
   - Verify dependencies between stories

3. **Understand Current State**
   - Review Epic #1 deliverables (CMake, LibTooling, Visitor)
   - Check repository structure
   - Identify where CNodeBuilder will fit

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
- **S**ingle Responsibility: CNodeBuilder focused only on node creation
- **O**pen/Closed: Easy to extend with new helper methods
- **L**iskov Substitution: Proper use of Clang base classes
- **I**nterface Segregation: Focused public API
- **D**ependency Inversion: Depend on ASTContext abstraction

**KISS (Keep It Simple, Stupid):**
- Each helper method does one thing
- Clear, descriptive method names
- No complex logic - just wrap Clang API

**DRY (Don't Repeat Yourself):**
- Extract common patterns (SourceLocation, TypeSourceInfo)
- Reuse helper methods within CNodeBuilder
- One implementation per concept

**YAGNI (You Aren't Gonna Need It):**
- Only implement helpers needed for Epic #3 translation
- Don't add speculative features
- Follow User Story requirements exactly

**TRIZ (Theory of Inventive Problem Solving):**
- Contradiction: Clang API is verbose BUT necessary for correctness
- Solution: Thin wrapper layer that preserves correctness while reducing verbosity
- Ideal Final Result: 1 line of readable code = 1 AST node

**Emergent Design:**
- Start with simplest helpers (types)
- Let patterns emerge as you add more helpers
- Refactor when you see duplication
- Trust that good API will emerge from practice

#### 4. Pair Programming Mindset

Think aloud as if programming with a partner:
- "Let's start with the simplest case..."
- "What's the minimum to make this test pass?"
- "I see we're repeating this pattern - let's extract it"
- "Is there a simpler way to express this?"
- "Let's verify this works before moving on"

#### 5. Commit Strategy

Follow conventional commits:
- `test: [description]` - Adding tests
- `feat: [description]` - New features
- `fix: [description]` - Bug fixes
- `refactor: [description]` - Code improvements
- `docs: [description]` - Documentation
- `chore: [description]` - Build system, dependencies

#### 6. Story Completion

Before marking a story as complete:
- [ ] All acceptance criteria met
- [ ] All tests pass (unit + integration)
- [ ] Code follows SOLID principles
- [ ] API is simple and readable (KISS)
- [ ] No duplication (DRY)
- [ ] No unnecessary features (YAGNI)
- [ ] Committed with proper messages
- [ ] Update User Story issue
- [ ] Move to next story

## Implementation Order

**Epic #2 User Stories (Sequential with some parallelization):**

1. **Story #9**: CNodeBuilder Structure and Type Helpers (3 points)
   - Dependencies: Epic #1 complete
   - Start here - foundation for all other stories

2. **Story #10**: Variable Declaration Helpers (3 points)
   - Dependencies: Story #9
   - Can work in parallel with #13 after #9

3. **Story #11**: Expression Helpers (5 points)
   - Dependencies: Story #9, #10
   - Most complex - needs types and variables

4. **Story #12**: Statement Helpers (5 points)
   - Dependencies: Story #9, #11
   - Builds on expressions

5. **Story #13**: Declaration Helpers (5 points)
   - Dependencies: Story #9
   - Can work in parallel with #10 after #9

6. **Story #14**: CNodeBuilder Unit Tests (5 points)
   - Dependencies: Stories #9-13 (all previous)
   - Comprehensive test suite - do last

## TDD Example Workflow

```cpp
// Story #9: Type Helpers
// Step 1: RED - Write failing test
// tests/CNodeBuilderTest.cpp
TEST(CNodeBuilderTest, IntType) {
    // Test doesn't compile - CNodeBuilder doesn't exist yet
    ASTContext Context = createTestContext();
    CNodeBuilder builder(Context);
    QualType intTy = builder.intType();
    EXPECT_TRUE(intTy->isIntegerType());
}

// Compile fails - commit failing test
git add tests/CNodeBuilderTest.cpp
git commit -m "test: add failing test for CNodeBuilder::intType()"

// Step 2: GREEN - Implement minimal solution
// include/CNodeBuilder.h
class CNodeBuilder {
    ASTContext &Ctx;
public:
    explicit CNodeBuilder(ASTContext &Ctx) : Ctx(Ctx) {}
    QualType intType() { return Ctx.IntTy; }
};

// Test passes - commit implementation
git add include/CNodeBuilder.h
git commit -m "feat: implement CNodeBuilder::intType()"

// Step 3: REFACTOR - Already simple, move to next test
```

## Success Criteria

Epic #2 is complete when:
- [ ] All 6 User Stories (#9-14) marked as Done in GitHub Project
- [ ] CNodeBuilder class with 20+ helper methods
- [ ] 30+ unit tests passing
- [ ] Code quality: 15x reduction (15 lines → 1 line)
- [ ] Doxygen documentation complete
- [ ] No memory leaks (AST owned by ASTContext)
- [ ] Code committed to develop branch

## API Design Goals

**Before CNodeBuilder (verbose):**
```cpp
// 15+ lines for simple int variable
VarDecl *VD = VarDecl::Create(
    Context, DC, SourceLocation(), SourceLocation(),
    &Context.Idents.get("x"), Context.IntTy,
    Context.getTrivialTypeSourceInfo(Context.IntTy),
    SC_None
);
IntegerLiteral *IL = IntegerLiteral::Create(
    Context, llvm::APInt(32, 42), Context.IntTy, SourceLocation()
);
VD->setInit(IL);
// ... more code ...
```

**After CNodeBuilder (clean):**
```cpp
// 1 line, readable, maintainable
VarDecl *x = builder.intVar("x", 42);
```

## Important Notes

1. **Do NOT read documentation files** (USER-STORIES-EPIC-2.md, etc.) - GitHub is the source of truth
2. **Focus on API clarity** - each helper should be obvious and readable
3. **Test every helper** - no untested code
4. **One story at a time** - complete before moving to next
5. **Update GitHub issues** - comment on progress
6. **Think about Epic #3** - these helpers will be used for translation

## Getting Started

```bash
# 1. Discover Epic #2 User Stories
gh issue view 2

# 2. List all User Stories
gh issue list --search "is:issue milestone:epic-2" --state all

# 3. Start with Story #9
gh issue view 9

# 4. Create test file structure
mkdir -p tests
# Setup GoogleTest or similar

# 5. Begin TDD cycle for type helpers
# - Write test for intType()
# - Implement intType()
# - Refactor if needed
# - Commit

# 6. Continue with remaining type helpers
# - structType(), ptrType(), voidType(), charType()

# 7. Move to Story #10 (variables)
```

## Questions to Ask Yourself

Before writing any helper:
- What is the simplest API for this?
- What Clang nodes are absolutely required?
- Can I hide SourceLocation complexity?
- Am I making this too complicated?
- Does the method name clearly express intent?
- Would I want to use this API?

## Unit Test Strategy

For each helper method:
1. **Basic functionality test** - Does it create the right node?
2. **Type verification test** - Is the type correct?
3. **Property test** - Are properties set correctly?
4. **Null handling test** - How does it handle edge cases?

Example test structure:
```cpp
TEST(CNodeBuilderTest, IntVar) {
    CNodeBuilder builder(Context);
    VarDecl *x = builder.intVar("x", 42);

    // Test 1: Node created
    ASSERT_NE(x, nullptr);

    // Test 2: Name correct
    EXPECT_EQ(x->getName(), "x");

    // Test 3: Type correct
    EXPECT_TRUE(x->getType()->isIntegerType());

    // Test 4: Has initializer
    EXPECT_TRUE(x->hasInit());

    // Test 5: Initializer value correct
    auto *IL = dyn_cast<IntegerLiteral>(x->getInit());
    EXPECT_EQ(IL->getValue(), 42);
}
```

## Output Format

For each User Story, provide:
1. Story summary from GitHub issue
2. API design discussion
3. Tests written (with pass/fail status)
4. Implementation approach
5. Code written
6. Refactoring done
7. API examples
8. Commits made
9. Story completion status

## Validation

After completing all stories:
- Run all tests: `ctest --output-on-failure`
- Check API usability with real examples
- Verify 15x code reduction achieved
- Confirm no memory leaks: `valgrind --leak-check=full ./tests`
- Update Epic #2 issue with completion summary

## Begin

Start by discovering Epic #2 details from GitHub and then systematically work through each User Story using the TDD cycle.

Remember: **GitHub Project is your source of truth. Test first, always. Keep it simple. Make the API beautiful.**

The goal is not just working code - it's a **delightful API** that makes Epic #3 (translation) a joy to implement.
