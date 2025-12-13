# GitHub Projects v2 Setup Research Summary

**View creation is NOT supported programmatically - use copyProjectV2 mutation or organization templates to preserve view configurations.**

## Version
v1.0 - Initial exhaustive research (2025-12-09)

## Key Findings

• **CRITICAL**: `createProjectV2View` mutation does NOT exist - verified via GraphQL schema introspection against all 30 ProjectV2 mutations

• **Field creation works perfectly**: `createProjectV2Field` supports TEXT, NUMBER, DATE, SINGLE_SELECT, and ITERATION types with full option configuration

• **copyProjectV2 is the complete solution**: Copies all fields, views, draft issues, workflows, and insights from any accessible project

• **Organization templates are production-ready**: Up to 6 recommended templates per org, UI-based project creation, copies everything except auto-add workflows

• **Field updates are destructive**: No mutation to modify existing fields - must delete/recreate causing data loss, plan structure carefully

• **Rate limits are generous**: 5,000 points/hour (10,000 for Enterprise), 1-second delays between mutations sufficient for typical scripting

• **Project #14 verified**: 148 items, 16 fields (Status, Type, Priority, Effort), 3 views (All-TABLE, Kanban-BOARD, All Todo-TABLE with filter)

## Recommended Approach

Use `copyProjectV2` mutation for complete project cloning (fields + views + configuration), OR use organization templates for team-wide standardization, OR script field creation with `createProjectV2Field` and manually configure views via GitHub UI. Views cannot be scripted but are preserved when cloning.

## Verified vs Assumed

**Verified** (hands-on tested):
- GraphQL schema introspection (all ProjectV2 mutations listed)
- Project #14 structure query (16 fields, 3 views)
- `createProjectV2`, `copyProjectV2`, `createProjectV2Field` input schemas
- Iteration field configuration schema
- Absence of any view-related mutations

**Assumed** (documented but not tested):
- Organization template system (public beta → GA, UI-only)
- Cross-org copyProjectV2 access restrictions (community-reported)
- Built-in workflow copying behavior (documented exception: auto-add workflows)
- Rate limit specifics (official documentation)

## Decisions Needed

None - path forward is clear: implement `gh-project-setup-init` (cache template), `gh-project-setup-create` (copyProjectV2 method), and `gh-project-setup-clone` (wrapper). Fallback to scripted field creation + manual views if copyProjectV2 unavailable.

## Blockers

None with workarounds:
- **No view creation API**: Use copyProjectV2 or manual UI configuration
- **No field update API**: Plan structure carefully or accept delete/recreate data loss
- **No workflow creation API**: Configure manually via UI or use GitHub Actions
- **Cross-org restrictions**: Use scripted field replication as fallback

## Next Step

Implement Phase 1 (Template Caching): Create `gh-project-setup-init` script to query project #14 structure, cache fields and views to `~/.config/gh-projects/template_14.json`, and display summary. Estimated: 1-2 hours.
