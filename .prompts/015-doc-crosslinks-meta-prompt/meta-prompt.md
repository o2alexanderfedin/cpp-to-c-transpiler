# Meta-Prompt: Ensure Cross-Links Between All Markdown Documentation

## Overview

This meta-prompt implements a three-stage Claude-to-Claude pipeline to ensure comprehensive cross-linking between all Markdown documentation files across all directories and subdirectories in the codebase.

## Context

**Project:** C++ to C Transpiler
**Documentation Scope:** All `*.md` files in the repository
**Goal:** Create a comprehensive cross-linking system that enables easy navigation between related documentation

**Current State:**
- 90+ Markdown files across multiple directories
- Partial cross-linking exists in key documents (README.md, docs/INDEX.md)
- Many documentation files lack cross-references to related content
- Documentation is organized hierarchically (docs/, research-archive/, .prompts/, etc.)

## Stage 1: Research & Documentation Analysis

### Prompt for Research Agent

```xml
<task>
<role>Documentation Analyzer</role>

<objective>
Analyze all Markdown documentation files in the repository to understand their:
1. Content and purpose
2. Relationships and dependencies
3. Current cross-linking patterns
4. Missing cross-reference opportunities
5. Hierarchical organization
</objective>

<deliverable>
A comprehensive documentation map in the following format:

## Documentation Inventory

### Directory: [path]

#### [filename.md]
- **Purpose**: [1-2 sentence description]
- **Key Topics**: [bullet list]
- **Current Outbound Links**: [list of linked files]
- **Related Documents**: [list of files that should be linked but aren't]
- **Inbound Links Needed From**: [list of files that should link here]

[Repeat for all files]

## Cross-Reference Matrix

Create a table showing:
- File A → Files it should link to
- Priority (High/Medium/Low)
- Rationale for the link

## Documentation Hierarchy

Visualize the documentation structure:
```
/
├── README.md (entry point)
├── docs/
│   ├── INDEX.md (primary navigation)
│   ├── features/
│   │   └── INDEX.md (feature navigation)
│   └── architecture/
│       └── INDEX.md (architecture navigation)
├── research-archive/
│   └── INDEX.md
└── [other directories]
```

## Missing Navigation Elements

Identify:
- Files without parent/child links
- Broken link chains
- Orphaned documentation
- Missing INDEX.md files
</deliverable>

<constraints>
- Analyze ALL *.md files in all directories
- Don't modify any files (read-only analysis)
- Use Glob and Read tools extensively
- Consider semantic relationships, not just filename similarities
- Identify both explicit (direct reference) and implicit (topical) relationships
</constraints>

<tools_required>
- Glob: Find all *.md files
- Read: Read file contents
- Grep: Search for existing cross-references
</tools_required>

<success_criteria>
- All 90+ Markdown files catalogued
- Relationships mapped between documents
- Current cross-linking status documented
- Missing cross-reference opportunities identified
- Clear documentation hierarchy established
</success_criteria>
</task>
```

---

## Stage 2: Cross-Linking Strategy & Plan

### Prompt for Planning Agent

```xml
<task>
<role>Documentation Architecture Planner</role>

<context>
You will receive a documentation analysis from Stage 1 that includes:
- Complete inventory of all Markdown files
- Current cross-linking patterns
- Missing cross-reference opportunities
- Documentation hierarchy

Your task is to create a comprehensive cross-linking strategy.
</context>

<objective>
Design a systematic cross-linking strategy that:
1. Establishes clear navigation paths between related documents
2. Creates a consistent cross-reference format
3. Prioritizes high-value links
4. Maintains documentation hierarchy
5. Enables discovery of related content
</objective>

<deliverable>
## Cross-Linking Strategy Document

### 1. Navigation Principles

Define guidelines for:
- Parent/child relationships (INDEX.md files)
- Sibling relationships (related documents in same directory)
- Cross-hierarchy relationships (features ↔ architecture)
- Entry points (README.md, docs/INDEX.md)

### 2. Link Categories

**Category A: Critical Navigation Links**
- Must-have links for basic navigation
- Parent → Child, Child → Parent
- Entry points → Key documents

**Category B: Contextual Cross-References**
- Related topics and concepts
- Feature implementations ↔ Architecture decisions
- Research ↔ Final documentation

**Category C: Reference Links**
- See also references
- Further reading suggestions
- Historical context

### 3. Implementation Plan

For each file that needs updates:

#### [filename.md]
- **Priority**: High/Medium/Low
- **Links to Add**:
  1. [Link text](path/to/file.md) - Rationale
  2. [Link text](path/to/file.md) - Rationale
- **Section for Links**: Where in the document to add links
- **Estimated Effort**: Small/Medium/Large

### 4. Standard Sections

Define standard sections for different document types:

**INDEX.md files:**
```markdown
# [Directory Name]

## Quick Navigation
[Links to subdirectories]

## Documents in This Section
[Links to files in this directory]

## Related Documentation
[Links to related sections]

## Parent Documentation
[Link to parent directory]
```

**Feature/Implementation guides:**
```markdown
# [Feature Name]

[Content...]

## Related Documentation
- **Architecture**: [Links to architectural decisions]
- **Implementation**: [Links to code/user stories]
- **Research**: [Links to research archive]

## See Also
[Links to related features]
```

### 5. Validation Rules

- Every document should have at least one inbound and one outbound link
- All INDEX.md files should link to their parent INDEX.md
- No broken links (validate all paths are correct)
- Relative links preferred over absolute links
- Link text should be descriptive, not "click here"

### 6. Execution Phases

**Phase 1: Critical Navigation (Priority: High)**
- Update all INDEX.md files
- Ensure README.md links to primary navigation
- Create missing INDEX.md files

**Phase 2: Hierarchical Links (Priority: High)**
- Parent → Child links
- Child → Parent links
- Sibling relationships

**Phase 3: Cross-References (Priority: Medium)**
- Feature ↔ Architecture links
- Research ↔ Documentation links
- Related topic links

**Phase 4: Enhancement (Priority: Low)**
- See Also sections
- Further reading
- Historical context
</deliverable>

<constraints>
- Prioritize high-value links over comprehensive coverage
- Keep link text concise and descriptive
- Use relative paths for maintainability
- Don't create circular references
- Consider user navigation patterns
</constraints>

<success_criteria>
- Clear categorization of all needed links
- Prioritized implementation plan
- Standard templates for different document types
- Validation rules defined
- Execution phases with clear priorities
</success_criteria>
</task>
```

---

## Stage 3: Implementation & Execution

### Prompt for Execution Agent

```xml
<task>
<role>Documentation Cross-Linking Engineer</role>

<context>
You will receive:
1. Documentation analysis (Stage 1 output)
2. Cross-linking strategy and plan (Stage 2 output)

Your task is to implement the cross-linking strategy by editing Markdown files.
</context>

<objective>
Systematically implement cross-links across all Markdown documentation files according to the approved strategy.
</objective>

<workflow>
### Phase 1: Setup and Preparation

1. **Create TODO list** using TodoWrite tool with all files to be modified
2. **Validate paths** - Ensure all target files exist
3. **Create backup plan** - Prepare to use git for rollback if needed

### Phase 2: Critical Navigation Links (Execute First)

For each file in Priority: High category:

1. **Read the file** using Read tool
2. **Identify insertion points** for new links
3. **Add links** using Edit tool with proper formatting
4. **Mark task complete** in TodoWrite
5. **Track progress** - Report completion percentage

Standard sections to add/update:
- "Related Documentation" section
- "See Also" section
- "Parent Documentation" link
- "Navigation" sections in INDEX.md files

### Phase 3: Hierarchical Relationships

Implement parent/child/sibling links:

1. **Update INDEX.md files** in all directories
2. **Add parent links** to all documents
3. **Add sibling links** where appropriate
4. **Validate hierarchy** - Ensure complete navigation tree

### Phase 4: Cross-Hierarchy References

Add cross-references between:
- Feature guides ↔ Architecture documents
- User stories ↔ Implementation guides
- Research archive ↔ Final documentation
- Technical analysis ↔ Practical guides

### Phase 5: Validation

1. **Check for broken links** - Verify all paths are correct
2. **Ensure bidirectionality** - If A links to B, check if B should link to A
3. **Verify orphans removed** - All documents have at least one inbound link
4. **Test navigation paths** - Ensure users can navigate between related content

### Phase 6: Reporting

Generate a summary report:

## Cross-Linking Implementation Report

### Summary
- **Files Modified**: X/Y
- **Links Added**: Z
- **Broken Links Fixed**: N
- **New INDEX.md Files Created**: M

### Files Modified
[List with brief description of changes]

### Links Added by Category
- **Critical Navigation**: X links
- **Hierarchical**: Y links
- **Cross-References**: Z links

### Validation Results
- ✅ No broken links
- ✅ All files have inbound links
- ✅ All INDEX.md files updated
- ✅ Complete navigation tree

### Remaining Work
[List any files not completed with reasons]
</workflow>

<implementation_guidelines>

### Link Format

**Within same directory:**
```markdown
[Link Text](filename.md)
```

**Parent directory:**
```markdown
[Link Text](../filename.md)
```

**Subdirectory:**
```markdown
[Link Text](subdirectory/filename.md)
```

**Sibling directory:**
```markdown
[Link Text](../sibling-directory/filename.md)
```

### Standard Section Templates

**Related Documentation Section:**
```markdown
## Related Documentation

- **[Category]**: [Link text](path/to/file.md) - Brief description
- **[Category]**: [Link text](path/to/file.md) - Brief description

## See Also

- [Link text](path/to/file.md) - Additional context
- [Link text](path/to/file.md) - Related topic
```

**INDEX.md Navigation:**
```markdown
# [Section Name]

## Quick Navigation

- 📖 **[Parent Section](../INDEX.md)**
- 🏠 **[Documentation Home](../../INDEX.md)** (if deeply nested)

## Documents in This Section

1. **[Document Name](filename.md)** - Description
2. **[Document Name](filename.md)** - Description

## Subdirectories

- **[Subdirectory/](subdirectory/INDEX.md)** - Description

## Related Sections

- **[Related Section](../related-section/INDEX.md)** - Description
```

### Edit Strategy

1. **Always read the file first** before editing
2. **Preserve existing content** - Add links, don't remove content
3. **Match existing formatting** - Follow the document's style
4. **Use Edit tool for precision** - Never guess file contents
5. **Add sections if missing** - Create "Related Documentation" sections
6. **Place links logically** - At end of document or relevant sections

### Parallel Execution

- **Run independent file edits in parallel** using multiple Edit calls
- **Maximum parallelism**: Number of CPU cores
- **Use TodoWrite** to track all parallel operations
- **Report progress** after each batch

### Error Handling

If a file edit fails:
1. **Log the error** in TodoWrite
2. **Continue with other files** - Don't block on single failure
3. **Report failures** in final summary
4. **Provide fix suggestions** for manual intervention if needed
</implementation_guidelines>

<tools_required>
- Read: Read existing file contents
- Edit: Add cross-reference links
- Write: Create new INDEX.md files if needed
- TodoWrite: Track progress across 90+ files
- Glob: Validate file paths
</tools_required>

<success_criteria>
- ✅ 90%+ of Markdown files have cross-links added
- ✅ All INDEX.md files updated with navigation
- ✅ No broken links introduced
- ✅ All files reachable from README.md via link chain
- ✅ Complete validation report generated
- ✅ Changes ready for git commit
</success_criteria>

<completion_checklist>
- [ ] All Priority: High files modified
- [ ] All INDEX.md files updated
- [ ] Parent/child relationships established
- [ ] Cross-hierarchy references added
- [ ] Validation checks passed
- [ ] Summary report generated
- [ ] No broken links
- [ ] All files have inbound links
- [ ] Ready for git commit
</completion_checklist>
</task>
```

---

## Usage Instructions

### Running the Pipeline

**Sequential Execution (Recommended):**

```bash
# Stage 1: Research
claude --prompt=".prompts/015-doc-crosslinks-meta-prompt/meta-prompt.md#stage-1" > stage1-output.md

# Stage 2: Planning (provide Stage 1 output as context)
claude --prompt=".prompts/015-doc-crosslinks-meta-prompt/meta-prompt.md#stage-2" --context="stage1-output.md" > stage2-output.md

# Stage 3: Execution (provide both previous outputs)
claude --prompt=".prompts/015-doc-crosslinks-meta-prompt/meta-prompt.md#stage-3" --context="stage1-output.md,stage2-output.md"
```

**Using /taches-cc-resources:run-prompt (if available):**

```bash
# In Claude Code CLI:
/taches-cc-resources:run-prompt 015-doc-crosslinks --sequential
```

**Manual Execution:**

Copy each stage's prompt and paste into a fresh Claude conversation in sequence.

---

## Quality Standards

### Link Quality

- **Descriptive link text**: Not "click here" or "this document"
- **Correct relative paths**: Validated against actual file structure
- **Bidirectional when appropriate**: Related documents link to each other
- **Context-sensitive**: Links placed in relevant sections

### Documentation Standards

- **Consistent formatting**: Follow existing document style
- **Logical organization**: Links grouped by category
- **User-focused**: Consider navigation patterns
- **Maintainable**: Use relative paths, clear structure

### Testing Validation

After implementation:

1. **Spot check** random files for link correctness
2. **Navigate manually** through documentation hierarchy
3. **Search for orphans** - Files with no inbound links
4. **Check for broken links** - Invalid paths
5. **Verify completeness** - All high-priority files updated

---

## Expected Outcomes

### Before Cross-Linking

- Many documentation files are hard to discover
- Users must navigate via file system or search
- Related content is disconnected
- Documentation hierarchy unclear

### After Cross-Linking

- ✅ Clear navigation paths from entry points to all documents
- ✅ Related documents reference each other
- ✅ Users can discover content through natural navigation
- ✅ INDEX.md files provide directory-level navigation
- ✅ Complete documentation graph with no orphans
- ✅ Consistent cross-reference format across all files

---

## Maintenance

### Keeping Links Updated

**When adding new documentation:**

1. Add links to the new document from:
   - Parent INDEX.md
   - Related documents
   - README.md (if major document)

2. Add links from the new document to:
   - Parent INDEX.md
   - Related documents
   - Subdocuments (if creating a directory)

**When moving documentation:**

1. Update all inbound links to point to new location
2. Update relative paths in the moved document
3. Update INDEX.md files in old and new locations

**Periodic maintenance:**

- Run link checker quarterly
- Update cross-references when adding major features
- Prune dead links when removing documentation

---

## Metadata

**Created**: 2025-12-18
**Meta-Prompt Version**: 1.0
**Target Repository**: C++ to C Transpiler
**Estimated Execution Time**:
- Stage 1 (Research): 15-20 minutes
- Stage 2 (Planning): 10-15 minutes
- Stage 3 (Execution): 30-45 minutes
- **Total**: ~60-90 minutes

**Dependencies**:
- None (self-contained)

**Output Artifacts**:
- Stage 1: Documentation analysis report
- Stage 2: Cross-linking strategy document
- Stage 3: Modified Markdown files + implementation report

---

*Generated with [Claude Code](https://claude.com/claude-code)*
