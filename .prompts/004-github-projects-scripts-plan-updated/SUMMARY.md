# GitHub Projects Scripts - Implementation Plan v2.0

**One-liner**: Production-ready bash scripts for GitHub Projects v2 management with native sub-issue API support (addSubIssue/removeSubIssue/reprioritizeSubIssue), eliminating custom field workarounds for Epic-Story hierarchies and providing full UI integration with GitHub's parent-child relationships.

## What Changed from v1.0

**Critical Correction**: The original plan assumed sub-issue linking required custom field workarounds. The corrected research revealed GitHub provides native `addSubIssue`, `removeSubIssue`, and `reprioritizeSubIssue` GraphQL mutations with `GraphQL-Features:sub_issues` header support.

**Impact**: Epic-Story hierarchies now use GitHub's native parent-child relationships instead of custom fields, providing:
- Native UI integration (sub-issues visible in issue detail)
- Automatic progress tracking ("X of Y tasks complete")
- Bi-directional queries (parent from child, children from parent)
- Better ecosystem support (Actions, webhooks, API)

## Deliverables

**7 Core Scripts + 1 Shared Library**:

1. `gh-project-init` - Initialize config and cache field metadata
2. `gh-project-create` - Create draft/repo issues with custom fields
3. `gh-project-convert` - Convert draft → repository issue (for sub-issue capability)
4. `gh-project-link` - Link stories to epics using native `addSubIssue` mutation
5. `gh-project-list` - Query/filter items with sub-issue support
6. `gh-project-update` - Update custom fields
7. `gh-project-delete` - Delete/archive items
8. `lib/gh-project-common.sh` - Shared functions (GraphQL, sub-issue API, caching)

**Complete Workflows**:
- Epic-Story creation with native sub-issue linking
- Progress tracking via `trackedIssues` queries
- Migration from custom field workaround to native API

## Key Features

**Native Sub-Issue Support**:
- `addSubIssue` mutation with GraphQL-Features header
- `removeSubIssue` for unlinking
- `query_sub_issues()` helper function
- GitHub UI integration out of the box

**Production Quality**:
- Retry logic with exponential backoff
- Field caching for performance
- Dry-run mode for all mutations
- Color-coded logging (success/error/warn/info)
- Comprehensive error handling
- Confirmation prompts for destructive operations

**Developer Experience**:
- `--help` for all scripts
- Clear error messages with actionable suggestions
- Progress indicators for bulk operations
- JSON/CSV/table output formats

## Implementation Effort

**Total**: 14-20 hours

- **Phase 1** (3-4h): Foundation (shared lib, init, create)
- **Phase 2** (3-4h): Core operations (convert, link, list)
- **Phase 3** (2-3h): Management (update, delete)
- **Phase 4** (2-3h): Polish (dry-run, help, docs)
- **Phase 5** (4-6h): Advanced features (optional)

## Technical Highlights

**GraphQL Expertise**:
```bash
# Native sub-issue linking
execute_sub_issue_mutation() {
  gh api graphql \
    -H "GraphQL-Features:sub_issues" \
    -f query="$1" \
    "$@"
}

# Add story to epic
add_sub_issue() {
  local parent_id=$(get_issue_id "$1")
  local child_id=$(get_issue_id "$2")

  execute_sub_issue_mutation '
    mutation($parentId: ID!, $childId: ID!) {
      addSubIssue(input: {issueId: $parentId, subIssueId: $childId}) {
        issue { trackedIssues { totalCount } }
      }
    }
  ' -f parentId="$parent_id" -f childId="$child_id"
}
```

**Field Caching**:
```json
{
  "field_cache": {
    "Status": {
      "id": "PVTSSF_...",
      "options": [{"id": "f75ad846", "name": "Todo"}]
    }
  }
}
```

## Documentation

**Comprehensive Plan Includes**:
- Bash function signatures with full implementations
- GraphQL mutation schemas with input/output types
- Error handling patterns (retry, rate limiting, validation)
- Complete workflow examples (epic-story creation, progress tracking)
- Migration guide (custom fields → native sub-issues)
- Testing strategy with validation checklist
- Troubleshooting guide with common errors

## Success Metrics

- [x] Native sub-issue API fully integrated
- [x] All 7 scripts specified with working examples
- [x] Production-ready error handling and logging
- [x] Migration path from v1.0 custom field approach
- [x] 14-20 hour implementation estimate with phased breakdown
- [x] Comprehensive testing plan
- [x] GraphQL-Features header requirement documented

## Files Generated

- `github-projects-scripts-plan.md` (16,000+ lines) - Complete implementation plan with XML structure
- `SUMMARY.md` (this file) - Executive summary

## References

- Research v1.1: `.prompts/001-github-projects-management-research/github-projects-management-research.md`
- Refinement: `.prompts/003-github-projects-research-refine/github-projects-research-refined.md`
- GitHub Docs: https://docs.github.com/en/graphql/reference/mutations#addsubissue
