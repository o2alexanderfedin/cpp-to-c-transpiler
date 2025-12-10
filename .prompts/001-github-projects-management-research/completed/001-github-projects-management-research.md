# GitHub Projects Issue Management Research

## Objective

Research and document **exhaustive** understanding of GitHub Projects v2 issue management, specifically:

1. **Draft vs Non-Draft Issues**: Complete lifecycle, creation methods, conversion workflows
2. **CRUD Operations**: Create, list, query, update, delete operations for both draft and repository issues
3. **Parent Linking**: How to link issues to epics/parent items without creating confusion
4. **Custom Fields**: Full support for Status, Priority, Type, and other custom fields
5. **Shell Script Implementation**: Patterns and best practices for robust bash scripts using `gh` CLI

**Why This Matters**: Current workflow creates confusion by mixing repository issues and project items, resulting in duplicate-looking entries. Need clean, scriptable workflow using ONLY GitHub Projects draft issues, converting to repository issues only when absolutely necessary.

## Context

**Problem Background**:
- Epic #41 had both sub-issues #70-75 AND separately mentioned stories #167-175
- This confusion stems from mixing GitHub repository issues with GitHub Projects items
- Need "Option 1" workflow: Draft issues by default, convert to repo issues only for notifications, PR linking, or sub-issues

**Reference Documentation** (from previous session):
```markdown
@/tmp/github-project-workflow.md - User's notes on draft vs repository issues distinction
```

**Current Understanding**:
- Creating items directly in GitHub Projects makes them "draft" issues
- Draft issues are project-only, lightweight
- Repository issues exist in both project AND repo
- Conversion is one-way (draft → repo issue, cannot reverse)
- Need to avoid accidental conversion

**Target Environment**:
- GitHub CLI (`gh`) version: ! Check installed version
- Project: ! Identify project number/name from current repository
- Shell: bash (macOS/Linux compatible)
- Custom fields: ! Query project to discover configured custom fields

## Requirements

### Research Scope (Deep/Exhaustive Level)

**Phase 1: GitHub Projects v2 Architecture**
1. **Draft Issues Deep Dive**:
   - Internal representation (GraphQL schema)
   - Limitations vs repository issues
   - When drafts are insufficient (blockers)
   - Storage/persistence model
   - Search/query capabilities

2. **Repository Issues Integration**:
   - How repo issues appear in projects
   - Bi-directional sync behavior
   - What triggers automatic conversion
   - Notification system differences
   - Sub-issue/parent linking requirements

3. **Conversion Workflows**:
   - All methods to convert draft → repo issue
   - Accidental conversion prevention
   - Bulk conversion patterns
   - Rollback strategies (if any workarounds exist)

**Phase 2: CLI & API Investigation**

1. **`gh project` Command Analysis**:
   ```bash
   # Document EVERY relevant command with:
   gh project --help
   gh project item-create --help
   gh project item-list --help
   gh project item-edit --help
   gh project item-delete --help
   gh project item-add --help
   gh project field-list --help
   gh project field-create --help
   ```
   - Test each command in safe environment
   - Document gotchas, edge cases, undocumented behavior
   - Performance characteristics (bulk operations)

2. **GraphQL API Comparison**:
   - When to use CLI vs raw GraphQL
   - What CLI abstracts away
   - Operations that require GraphQL directly
   - Mutation examples for complex operations

3. **Custom Fields Management**:
   - List all field types (text, number, date, single-select, iteration)
   - How to query field values
   - How to set field values
   - Field ID vs field name resolution
   - Default values and validation

**Phase 3: Parent Linking & Hierarchy**

1. **Epic/Story Relationships**:
   - How to create parent-child links
   - Sub-issue feature requirements (repo issue only?)
   - Alternative linking methods for drafts
   - Querying by parent/hierarchy
   - Display in project views

2. **Cross-Reference Management**:
   - Mention vs formal link difference
   - How mentions create "activity timeline" entries
   - Preventing unwanted cross-references
   - Cleanup of stale references

**Phase 4: Query & Filtering**

1. **Listing/Searching**:
   - Filter draft vs repo issues
   - Query by custom field values
   - Combined filters (Status=Done AND Type=Epic)
   - Pagination for large projects
   - Performance optimization

2. **JSON Output Parsing**:
   - `--format json` structure
   - `jq` patterns for common operations
   - Handling null/missing fields
   - Type coercion issues

**Phase 5: Best Practices & Patterns**

1. **Workflow Patterns**:
   - Recommended draft-first workflow
   - When to convert to repo issue
   - Bulk import strategies
   - Migration from repo-first to draft-first

2. **Error Handling**:
   - Network failures
   - Permission errors
   - Rate limiting
   - Idempotency patterns

3. **Script Architecture**:
   - Function organization
   - Configuration management
   - Dry-run mode implementation
   - Logging and debugging

### Verification Requirements

**CRITICAL**: Use actual GitHub CLI experimentation, not just documentation reading.

For each operation, you MUST:

1. **Test in Safe Environment**:
   - Use test project or create temporary project
   - Document exact commands run
   - Capture full output (success and error cases)
   - Screenshot UI behavior when relevant

2. **Verify Documentation**:
   - Official GitHub docs: https://docs.github.com/en/issues/planning-and-tracking-with-projects
   - CLI docs: `gh help project`
   - GraphQL API: https://docs.github.com/en/graphql/reference/objects#projectv2
   - Check for discrepancies between docs and actual behavior

3. **Document Edge Cases**:
   - What happens if parent doesn't exist?
   - Empty field values vs missing fields
   - Unicode in titles, special characters
   - Very long field values
   - Concurrent modifications

### Output Specification

Save comprehensive research to: `.prompts/001-github-projects-management-research/github-projects-management-research.md`

**Structure**:

```xml
<research version="1.0">

<executive_summary>
<!-- 2-3 paragraphs: Key findings, recommended approach, confidence level -->
</executive_summary>

<architecture>
<!-- Deep dive into GitHub Projects v2 internal model -->
<draft_issues>
  <!-- Complete analysis of draft issues -->
</draft_issues>
<repository_issues>
  <!-- Complete analysis of repository issues -->
</repository_issues>
<conversion_lifecycle>
  <!-- All conversion methods, prevention strategies -->
</conversion_lifecycle>
</architecture>

<cli_reference>
<!-- Exhaustive command documentation with examples -->
<create_operations>
  <!-- Draft creation, repo issue creation, conversion -->
</create_operations>
<read_operations>
  <!-- List, query, filter, JSON parsing -->
</read_operations>
<update_operations>
  <!-- Edit title, body, custom fields, parent linking -->
</update_operations>
<delete_operations>
  <!-- Delete drafts, remove from project, archive -->
</delete_operations>
<custom_fields>
  <!-- Field types, setting values, querying -->
</custom_fields>
</cli_reference>

<parent_linking>
<!-- Complete guide to hierarchical relationships -->
<formal_links>
  <!-- Sub-issue feature, requirements, limitations -->
</formal_links>
<alternative_methods>
  <!-- For draft issues, cross-references -->
</alternative_methods>
</parent_linking>

<query_patterns>
<!-- Advanced filtering and search -->
<examples>
  <!-- 10+ real-world query examples with jq -->
</examples>
</query_patterns>

<script_patterns>
<!-- Shell script implementation guidance -->
<recommended_structure>
  <!-- Function organization, error handling -->
</recommended_structure>
<code_examples>
  <!-- Reusable functions, not full scripts -->
</code_examples>
</script_patterns>

<verification>
<!-- What you tested, how, results -->
<experiments>
  <experiment name="draft-creation-methods">
    <commands><!-- Exact commands --></commands>
    <output><!-- Actual output --></output>
    <findings><!-- What you learned --></findings>
  </experiment>
  <!-- More experiments -->
</experiments>
</verification>

<metadata>
<confidence>
  <!-- HIGH/MEDIUM/LOW with justification -->
  <!-- What's verified vs documented vs assumed -->
</confidence>

<sources>
  <source type="official-docs">https://...</source>
  <source type="cli-help">gh project --help</source>
  <source type="experimentation">Test project #14</source>
</sources>

<dependencies>
  <!-- What's needed to proceed to implementation -->
  <!-- e.g., "Project #14 must have custom fields: Status, Priority, Type" -->
</dependencies>

<open_questions>
  <!-- What remains uncertain after research -->
  <!-- e.g., "Can parent links work across projects?" -->
</open_questions>

<assumptions>
  <!-- What was assumed during research -->
  <!-- e.g., "Assuming GitHub CLI >= 2.40.0" -->
</assumptions>
</metadata>

</research>
```

### Quality Controls

**Before Finalizing**:

1. **Verification Checklist**:
   - [ ] Tested draft issue creation (3+ methods if available)
   - [ ] Tested repo issue creation
   - [ ] Tested draft → repo conversion
   - [ ] Tested all custom field types in your project
   - [ ] Tested parent linking (both drafts and repo issues)
   - [ ] Tested list/query with filters
   - [ ] Tested update operations
   - [ ] Tested delete operations
   - [ ] Documented at least 5 edge cases with actual testing
   - [ ] Captured JSON output examples
   - [ ] Verified all commands against current `gh` version

2. **Quality Report**:
   - List which findings are **verified** (tested)
   - List which findings are **documented** (from official docs)
   - List which findings are **assumed** (not verified)
   - Highlight any discrepancies between docs and behavior

3. **Sources Consulted**:
   - Official GitHub documentation URLs
   - `gh` CLI help pages examined
   - GraphQL API exploration (if used)
   - Any GitHub issues or discussions referenced

4. **Pre-Submission Check**:
   - Output is valid XML (no unclosed tags)
   - All code blocks have language specified
   - All URLs are complete and accessible
   - Confidence level has clear justification
   - Open questions are answerable (not rhetorical)

### SUMMARY.md Requirement

**MUST** create: `.prompts/001-github-projects-management-research/SUMMARY.md`

**Structure**:

```markdown
# GitHub Projects Management Research Summary

**[Substantive one-liner describing key recommendation]**

## Version
v1.0 - Initial exhaustive research

## Key Findings
• [Most important discovery about draft vs repo issues]
• [Critical insight about parent linking]
• [Essential pattern for custom fields]
• [Key limitation or gotcha discovered]
• [Recommended workflow approach]

(5-7 bullet points, actionable, specific)

## Verified vs Documented
**Verified through testing**: [List operations actually tested]
**From official docs**: [List documented but not tested]
**Assumed**: [List any assumptions]

## Decisions Needed
• [Decision user must make before implementation, if any]
• [Or: "None - ready for implementation"]

## Blockers
• [External dependency blocking progress, if any]
• [Or: "None"]

## Next Step
[Concrete action - e.g., "Create implementation plan for shell scripts" or "Begin script development"]
```

**One-Liner Requirements**:
- Must be SUBSTANTIVE (not "Research completed" or "Investigation done")
- Should communicate the core recommendation
- Examples:
  - ✅ "Use `gh project item-create --draft` for all items; convert only for PR linking"
  - ✅ "Custom fields require field ID lookup; cache mapping in script config"
  - ❌ "GitHub Projects research completed"
  - ❌ "Investigated draft issues and CLI commands"

## Success Criteria

**Research is complete when**:
1. ✅ All CLI commands documented with tested examples
2. ✅ Draft vs repo issue lifecycle fully understood
3. ✅ Parent linking methods documented (both types)
4. ✅ Custom field management fully explored
5. ✅ At least 10 real commands tested with output captured
6. ✅ Edge cases documented (5+)
7. ✅ Query patterns with jq examples provided
8. ✅ Script architecture patterns recommended
9. ✅ Quality report distinguishes verified/documented/assumed
10. ✅ SUMMARY.md created with substantive one-liner
11. ✅ Confidence level justified with evidence
12. ✅ Next step is clear and actionable

**Confidence Level Should Be**:
- **HIGH**: If 90%+ of operations tested, official docs verified, no major unknowns
- **MEDIUM**: If 50-90% tested, some assumptions, minor open questions
- **LOW**: If mostly documented research, significant untested areas

Target: **HIGH confidence** (this is exhaustive research)
