# Documentation Cross-Linking Meta-Prompt

## Quick Start

This meta-prompt creates comprehensive cross-links between all Markdown documentation files in the repository using a three-stage Claude-to-Claude pipeline.

### What It Does

Transforms your documentation from isolated files into a connected knowledge graph with:
- ✅ Clear navigation paths from entry points to all documents
- ✅ Related documents cross-referencing each other
- ✅ INDEX.md files providing directory-level navigation
- ✅ No orphaned documentation
- ✅ Complete documentation hierarchy

### Before & After

**Before:**
- 90+ Markdown files scattered across directories
- Hard to discover related content
- No clear navigation structure
- Users must browse file system or search

**After:**
- Clear navigation from README.md to all documents
- Related topics link to each other
- Every directory has INDEX.md navigation
- Users can explore documentation naturally

## Files

- **[meta-prompt.md](meta-prompt.md)** - Complete three-stage pipeline prompts
- **[SUMMARY.md](SUMMARY.md)** - Overview and quick reference
- **README.md** - This file (usage instructions)

## Usage

### Option 1: Run All Stages Sequentially (Recommended)

```bash
# Stage 1: Analyze all documentation
claude --prompt=".prompts/015-doc-crosslinks-meta-prompt/meta-prompt.md#stage-1" > stage1-analysis.md

# Stage 2: Create cross-linking strategy
claude --prompt=".prompts/015-doc-crosslinks-meta-prompt/meta-prompt.md#stage-2" \
       --context="stage1-analysis.md" > stage2-strategy.md

# Stage 3: Implement cross-links
claude --prompt=".prompts/015-doc-crosslinks-meta-prompt/meta-prompt.md#stage-3" \
       --context="stage1-analysis.md,stage2-strategy.md"
```

### Option 2: Use Task Runner (if available)

```bash
# In Claude Code CLI:
/taches-cc-resources:run-prompt 015-doc-crosslinks --sequential
```

### Option 3: Manual Execution

1. Copy Stage 1 prompt from [meta-prompt.md](meta-prompt.md#stage-1-research--documentation-analysis)
2. Paste into fresh Claude conversation
3. Save the output as `stage1-analysis.md`
4. Repeat for Stages 2 and 3, providing previous outputs as context

## Three-Stage Pipeline

### Stage 1: Research & Documentation Analysis (15-20 min)

**What it does:**
- Finds all `*.md` files in the repository
- Analyzes content and purpose of each document
- Maps relationships between documents
- Identifies missing cross-references
- Visualizes documentation hierarchy

**Output:**
- Documentation inventory (all 90+ files catalogued)
- Cross-reference matrix (what should link to what)
- Current state analysis
- Missing link opportunities

### Stage 2: Cross-Linking Strategy & Plan (10-15 min)

**What it does:**
- Creates navigation principles
- Categorizes links by priority (Critical/Contextual/Reference)
- Designs standard section templates
- Prioritizes implementation phases
- Defines validation rules

**Output:**
- Comprehensive cross-linking strategy
- Implementation plan with priorities
- Standard templates for INDEX.md and feature guides
- Validation criteria

### Stage 3: Implementation & Execution (30-45 min)

**What it does:**
- Updates all INDEX.md files with navigation
- Adds parent/child/sibling links
- Implements cross-hierarchy references
- Validates all links
- Generates implementation report

**Output:**
- 70-90 modified Markdown files
- 200-300 new cross-reference links
- Validation report (no broken links)
- Complete implementation summary

## What Gets Added

### INDEX.md Files

Every directory will have (or have updated) an INDEX.md with:

```markdown
# [Section Name]

## Quick Navigation
- 📖 **[Parent Section](../INDEX.md)**
- 🏠 **[Documentation Home](../../INDEX.md)**

## Documents in This Section
1. **[Document Name](file.md)** - Brief description

## Subdirectories
- **[Subdirectory/](subdir/INDEX.md)** - Description

## Related Sections
- **[Related Section](../related/INDEX.md)** - Description
```

### Feature/Implementation Guides

Documents will gain "Related Documentation" sections:

```markdown
## Related Documentation

- **Architecture**: [Link](path/to/arch.md) - Architectural decisions
- **Implementation**: [Link](path/to/impl.md) - Implementation details
- **Research**: [Link](path/to/research.md) - Research background

## See Also

- [Related Topic](path/to/related.md) - Additional context
- [Further Reading](path/to/reading.md) - Deep dive
```

### README.md and Entry Points

Enhanced navigation from main entry points to key documentation areas.

## Link Types

### Critical Navigation Links (Added First)
- README.md → Primary documentation sections
- INDEX.md files → All directory contents
- Parent → Child directory relationships
- Entry points → Key documents

### Hierarchical Links
- Parent directories → Subdirectories
- Documents → Parent INDEX.md
- Sibling documents (related files in same directory)

### Cross-References
- Feature guides ↔ Architecture documents
- User stories ↔ Implementation guides
- Research archive ↔ Final documentation
- Technical analysis ↔ Practical guides

## Quality Standards

All added links will follow these standards:

- ✅ **Descriptive link text**: "Architecture Decision Rationale" not "click here"
- ✅ **Correct relative paths**: Validated against actual file structure
- ✅ **Bidirectional**: Related documents link to each other
- ✅ **Context-sensitive**: Links placed in relevant sections
- ✅ **Consistent formatting**: Matches existing document style

## Validation

The implementation stage includes comprehensive validation:

- ✅ No broken links (all paths verified)
- ✅ Every document has inbound and outbound links
- ✅ All INDEX.md files link to parent
- ✅ All files reachable from README.md
- ✅ Relative paths used for maintainability

## Timeline

| Stage | Duration | Description |
|-------|----------|-------------|
| Stage 1 | 15-20 min | Analyze all documentation |
| Stage 2 | 10-15 min | Plan cross-linking strategy |
| Stage 3 | 30-45 min | Implement cross-links |
| **Total** | **60-90 min** | Complete pipeline |

## Expected Results

### Files Modified
- **70-90 Markdown files** will be updated with cross-links
- **10-15 INDEX.md files** will be created or enhanced
- **README.md** will gain better navigation links

### Links Added
- **200-300 cross-reference links** across all documentation
- **50-100 critical navigation links** (high priority)
- **100-150 contextual cross-references** (medium priority)
- **50-100 enhancement links** (low priority)

### Documentation Structure
```
/
├── README.md (enhanced with navigation)
│
├── docs/
│   ├── INDEX.md (updated)
│   ├── SUMMARY.md (linked)
│   ├── ARCHITECTURE.md (cross-referenced)
│   │
│   ├── features/
│   │   ├── INDEX.md (created/updated)
│   │   ├── exceptions.md (cross-linked)
│   │   ├── rtti.md (cross-linked)
│   │   └── [other features linked]
│   │
│   └── architecture/
│       ├── INDEX.md (created/updated)
│       └── [all files cross-linked]
│
├── research-archive/
│   ├── INDEX.md (updated)
│   └── [all research linked]
│
└── [all other directories with INDEX.md and cross-links]
```

## Maintenance

### Adding New Documentation

When you add a new Markdown file:

1. **Link TO it from:**
   - Parent INDEX.md
   - Related documents
   - README.md (if major document)

2. **Link FROM it to:**
   - Parent INDEX.md
   - Related documents
   - Subdirectories (if creating a new section)

### Moving Documentation

When moving a file:

1. Update all inbound links to new location
2. Update relative paths in the moved file
3. Update INDEX.md in old and new locations

### Periodic Maintenance

- Run link checker quarterly
- Update cross-references when adding major features
- Prune dead links when removing documentation

## Troubleshooting

### Stage 1 Runs Too Long
- Reduce scope to specific directories first
- Use `head_limit` in Grep to sample files

### Stage 3 Makes Too Many Changes
- Review Stage 2 strategy before executing
- Adjust priorities in the plan
- Run in batches (high priority first)

### Broken Links After Implementation
- Check file paths are correct (relative, not absolute)
- Verify files weren't moved during implementation
- Run validation checks from Stage 3

### Git Conflicts
- Commit existing changes before running
- Review changes incrementally
- Use `git checkout` to revert if needed

## Technical Details

### Tools Used
- **Glob**: Find all `*.md` files
- **Read**: Analyze file contents
- **Grep**: Find existing cross-references
- **Edit**: Add cross-reference links (preserves content)
- **Write**: Create new INDEX.md files
- **TodoWrite**: Track progress across 90+ files

### Parallel Execution
- Stage 3 runs independent file edits in parallel
- Maximum parallelism: CPU core count
- Map/reduce pattern for large workloads
- TodoWrite tracks all parallel operations

### Error Handling
- Single file failures don't block entire pipeline
- Errors logged in TodoWrite for review
- Final report includes all failures
- Fix suggestions provided for manual intervention

## Advanced Usage

### Customize Link Categories

Edit Stage 2 prompt to adjust:
- Link priority levels
- Standard section templates
- Navigation principles
- Validation rules

### Scope to Specific Directories

Modify Stage 1 Glob patterns:
```bash
# Only docs/ directory
pattern: "docs/**/*.md"

# Only specific subdirectories
pattern: "{docs,research-archive}/**/*.md"
```

### Dry Run Mode

Add to Stage 3 prompt:
```xml
<constraint>
DO NOT modify any files. Generate the implementation report
showing what WOULD be changed, but don't execute edits.
</constraint>
```

## FAQ

**Q: Will this overwrite my existing links?**
A: No, the Edit tool preserves existing content and only adds new links.

**Q: Can I run this on a subset of files?**
A: Yes, modify the Glob patterns in Stage 1 to target specific directories.

**Q: What if I don't like the changes?**
A: All changes are tracked in git. Use `git checkout` to revert specific files or `git reset` to revert all changes.

**Q: How do I customize the link templates?**
A: Edit the "Standard Section Templates" in Stage 2 before running Stage 3.

**Q: Will this create new files?**
A: Only INDEX.md files if they're missing in directories with multiple Markdown files.

**Q: How long does it take?**
A: 60-90 minutes for the complete three-stage pipeline.

**Q: Can I pause and resume?**
A: Yes, each stage produces an output file you can save and use later.

## Version History

- **v1.0** (2025-12-18) - Initial meta-prompt creation
  - Three-stage pipeline (Research → Plan → Execute)
  - Comprehensive cross-linking for 90+ files
  - Validation and quality standards
  - Parallel execution support

## Support

For issues or questions:
- Review [SUMMARY.md](SUMMARY.md) for quick reference
- Check [meta-prompt.md](meta-prompt.md) for detailed prompts
- Consult project [CLAUDE.md](../../CLAUDE.md) for development guidelines

---

*Generated with [Claude Code](https://claude.com/claude-code)*
