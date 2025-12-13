# GitHub Projects Management Research Summary

**Use `gh project item-create` for draft-first workflow; convert via GraphQL only when PR linking or sub-issues needed; dual-ID system (PVTI_*/DI_*) requires GraphQL for draft editing**

## Version
v1.0 - Initial exhaustive research (2025-12-09)

## Key Findings

• **Draft-First Workflow**: Create draft issues via `gh project item-create` for lightweight planning; only convert to repository issues when needing PR linking, notifications, or GitHub's native sub-issue tracking

• **Dual-ID System Gotcha**: Draft issue editing requires DI_* content ID (obtained via GraphQL), not PVTI_* project item ID; custom field updates use PVTI_* with project-id parameter

• **Custom Fields Are Project-Only**: All custom fields (Status, Type, Priority, etc.) are project-level metadata that do NOT sync to repository; preserved during draft-to-repo conversion

• **Conversion Is One-Way**: Draft to repository issue conversion via GraphQL mutation `convertProjectV2DraftIssueItemToIssue` is irreversible; no rollback capability exists

• **Sub-Issue Linking Unavailable**: GitHub's native parent/child tracking requires repository issues but has NO programmatic API (GraphQL mutation rejected); workaround is custom "Parent Epic" text field

• **Field ID Resolution Required**: All custom field operations require field IDs and option IDs from `gh project field-list`; cache this data to avoid repeated queries

• **Client-Side Filtering Only**: CLI provides no server-side filtering; use jq for all query patterns (15+ examples documented including aggregations, multi-condition filters, CSV export)

## Verified vs Documented

**Verified through testing** (95% confidence):
- Draft issue creation and editing (with DI_* ID requirement discovered)
- Repository issue creation and project linking
- Draft to repository conversion via GraphQL
- Custom field management (single-select, text, number, date types)
- Query filtering with jq (tested on 149-item project)
- Delete and archive operations
- Field/option ID retrieval and caching patterns
- All CLI commands tested with gh v2.69.0

**From official docs**:
- GraphQL schema for ProjectV2Item
- Sub-issue `trackedIssues` and `parent` fields exist but linking mutation not documented
- Field types and data type options

**Assumed**:
- CLI behavior stable across minor version updates
- Sub-issue API will eventually become available programmatically
- Rate limiting follows standard GitHub API patterns

## Decisions Needed

• **None** - Ready for script implementation with documented patterns

## Blockers

• **Sub-Issue Linking**: GitHub's native parent/child relationships not accessible via API; must use workaround (custom field) or wait for API availability

• **Draft Content ID**: No CLI command to get DI_* ID; requires GraphQL query for every draft edit operation

## Next Step

**Begin shell script implementation** using documented patterns:
1. Implement core functions (get_field_id, set_custom_field, create_draft_issue, convert_to_issue)
2. Add caching layer for field metadata
3. Create dry-run mode and error handling
4. Build bulk operations for epic/story creation workflow
5. Test with Epic #42+ and associated user stories
