# GitHub Projects Research Refinement - Sub-Issue API and Missed Features

## Objective

Refine and correct the GitHub Projects research to include **critical missing APIs** discovered by the user, specifically:

1. **`addSubIssue` GraphQL Mutation** - User found this exists at https://docs.github.com/en/graphql/reference/mutations#addsubissue
2. **Other Potentially Missed GraphQL APIs** - Comprehensive search for parent/child linking, project management, and related mutations
3. **Verification of Original Research Claims** - Re-examine claims about API unavailability

**Why This Matters**: The original research incorrectly stated "Sub-issue linking requires custom field workaround" when the `addSubIssue` mutation actually exists. This error could propagate to implementation plans and scripts. Need to identify and correct all such mistakes.

## Context

**Original Research**:
```
@.prompts/001-github-projects-management-research/github-projects-management-research.md
```

**Critical Error Identified by User**:
> Research stated: "Sub-Issue Linking Unavailable: GitHub's native parent/child tracking requires repository issues but has NO programmatic API (GraphQL mutation rejected)"
>
> **INCORRECT**: The `addSubIssue` mutation exists and is documented at https://docs.github.com/en/graphql/reference/mutations#addsubissue

**User's Concern**:
- "I think that you might be missing other things too"
- Research may have other gaps or incorrect conclusions
- Need to use web search, web fetch, and potentially Playwright MCP to thoroughly verify

**What Needs Fixing**:
1. Document the `addSubIssue` mutation (inputs, outputs, examples)
2. Find related mutations: `removeSubIssue`, parent issue queries, etc.
3. Search for other missed GraphQL APIs for Projects v2
4. Re-verify all "unavailable" or "not possible" claims from original research
5. Update confidence levels based on corrections

## Requirements

### Refinement Scope

**Phase 1: Correct Sub-Issue API Documentation**

1. **`addSubIssue` Mutation Deep Dive**:
   - Full GraphQL schema from https://docs.github.com/en/graphql/reference/mutations#addsubissue
   - Required inputs (issue ID, sub-issue ID, etc.)
   - Return type and fields
   - Authentication/permission requirements
   - Rate limiting considerations
   - **Test with actual GraphQL query** if possible

2. **Related Sub-Issue APIs**:
   - `removeSubIssue` mutation (if exists)
   - Query for parent issue from sub-issue
   - Query for sub-issues from parent issue
   - Batch operations for multiple sub-issues
   - Any other hierarchy-related APIs

3. **CLI Support**:
   - Does `gh` CLI expose sub-issue operations?
   - Check `gh issue --help`, `gh api --help`
   - If not in CLI, document GraphQL approach

**Phase 2: Comprehensive API Search**

Use **all available tools** (WebSearch, WebFetch, Playwright MCP) to search for:

1. **GitHub Projects v2 GraphQL Mutations**:
   - Search GitHub docs: https://docs.github.com/en/graphql/reference/mutations
   - Filter for ProjectV2, Issue, SubIssue related mutations
   - Check for recently added APIs (2024-2025)
   - Document ALL relevant mutations found

2. **GitHub Projects v2 Queries**:
   - Parent/child relationship queries
   - Project item queries beyond basic list
   - Custom field queries
   - Bulk operations
   - Advanced filtering server-side

3. **GitHub CLI Updates**:
   - Check `gh` CLI changelog for Projects features
   - Recent additions to `gh project` commands
   - Beta/experimental features

**Phase 3: Verify Original Research Claims**

Re-examine every "not available" or "not possible" claim:

1. **From Original Research**:
   - ❌ "Sub-issue linking unavailable programmatically" - **WRONG**
   - ? "Draft content editing requires DI_* GraphQL ID" - verify
   - ? "No server-side filtering" - verify
   - ? "Parent links work only for repo issues" - verify with addSubIssue
   - [List all negative claims from original research]

2. **For Each Claim**:
   - Search official docs with specific queries
   - Test with GraphQL Explorer (https://docs.github.com/en/graphql/overview/explorer)
   - Use Playwright to navigate GitHub docs if needed
   - Provide evidence (URL + quote) for correction or confirmation

**Phase 4: Impact Assessment**

1. **What Changes in Implementation Plan**:
   - Sub-issue linking can use native API, not custom fields
   - What other workarounds can be replaced?
   - What becomes simpler/better?

2. **Script Updates Needed**:
   - Which planned scripts are affected?
   - What new capabilities are unlocked?
   - What complexity is removed?

### Tool Usage Requirements

**MUST use these tools for thorough verification**:

1. **WebSearch**:
   - Search for: "GitHub GraphQL addSubIssue mutation"
   - Search for: "GitHub Projects v2 GraphQL API 2024"
   - Search for: "gh CLI sub-issue parent child"
   - Search for: "GitHub GraphQL mutations projects"

2. **WebFetch**:
   - Fetch: https://docs.github.com/en/graphql/reference/mutations#addsubissue
   - Fetch: https://docs.github.com/en/graphql/reference/mutations (full page)
   - Fetch: https://docs.github.com/en/graphql/reference/queries
   - Parse for relevant APIs

3. **Playwright MCP** (if needed):
   - Navigate GitHub GraphQL docs
   - Search/filter for Projects, Issues, SubIssues
   - Capture schema details
   - Screenshot relevant sections

4. **gh CLI Testing**:
   - Test actual commands for sub-issue operations
   - Document what works vs what requires GraphQL

### Output Specification

**Primary Output**: `.prompts/003-github-projects-research-refine/github-projects-research-refined.md`

**Do NOT create a new research document from scratch**. Instead, create a refinement document:

```xml
<refinement version="1.1" refines="github-projects-management-research.md v1.0">

<corrections>
<!-- Critical errors fixed -->
<correction severity="high">
  <original_claim>Sub-issue linking unavailable programmatically</original_claim>
  <corrected_claim>addSubIssue mutation exists and works for repository issues</corrected_claim>
  <evidence>
    <source>https://docs.github.com/en/graphql/reference/mutations#addsubissue</source>
    <quote><!-- Exact quote from docs --></quote>
  </evidence>
  <impact>
    <!-- How this changes implementation approach -->
  </impact>
</correction>
<!-- More corrections -->
</corrections>

<additions>
<!-- New findings not in original research -->
<addition category="sub-issue-api">
  <api_name>addSubIssue</api_name>
  <graphql_schema>
    <!-- Full schema -->
  </graphql_schema>
  <example_mutation>
    <!-- Working example -->
  </example_mutation>
  <cli_support><!-- Yes/No with details --></cli_support>
</addition>
<!-- More additions -->
</additions>

<verifications>
<!-- Original claims re-verified -->
<verification claim="Draft editing requires DI_* ID">
  <status>CONFIRMED / CORRECTED</status>
  <evidence><!-- Sources --></evidence>
</verification>
<!-- More verifications -->
</verifications>

<updated_patterns>
<!-- How implementation patterns change -->
<pattern name="epic-story-linking">
  <old_approach>Custom "Parent Epic" text field</old_approach>
  <new_approach>Use addSubIssue mutation for native linking</new_approach>
  <code_example><!-- GraphQL mutation --></code_example>
  <advantages>
    <!-- Why this is better -->
  </advantages>
</pattern>
<!-- More updated patterns -->
</updated_patterns>

<impact_summary>
<!-- What changes in overall approach -->
<implementation_changes>
  <!-- How scripts/plan need to adapt -->
</implementation_changes>
<confidence_adjustment>
  <!-- New confidence level with justification -->
</confidence_adjustment>
</impact_summary>

<metadata>
<research_methodology>
  <!-- What tools/methods used for verification -->
  <web_searches><!-- Queries run --></web_searches>
  <docs_fetched><!-- URLs examined --></docs_fetched>
  <playwright_sessions><!-- If used --></playwright_sessions>
  <cli_tests><!-- Commands tested --></cli_tests>
</research_methodology>

<confidence>
  <!-- Updated confidence level -->
  <!-- What's now verified vs still uncertain -->
</confidence>

<remaining_open_questions>
  <!-- What's still unknown after refinement -->
</remaining_open_questions>
</metadata>

</refinement>
```

**Secondary Output**: Update original research file

Archive old version:
```bash
cp github-projects-management-research.md \
   archive/github-projects-management-research-v1.0.md
```

Create updated v1.1 by applying corrections:
- Fix sub-issue API section
- Add addSubIssue documentation
- Update confidence levels
- Revise implementation patterns
- Add changelog at top noting v1.1 refinements

### SUMMARY.md Requirement

**MUST** create: `.prompts/003-github-projects-research-refine/SUMMARY.md`

```markdown
# GitHub Projects Research Refinement Summary

**[Substantive one-liner about key correction]**

## Version
v1.1 - Refinement correcting sub-issue API and other gaps

## Critical Corrections

• **Sub-Issue API Found**: [Description of addSubIssue mutation and how it changes approach]
• [Other high-severity corrections]

## New Discoveries

• [List of additional APIs/features found]

## Verified Claims

• [List of original claims that were confirmed accurate]

## Updated Recommendations

• [How implementation approach changes based on corrections]

## Confidence Level

**Previous**: [Original confidence]
**Updated**: [New confidence with justification]

## Impact on Implementation

• [What changes in scripts/plan]
• [What becomes simpler/better]
• [What workarounds can be removed]

## Next Step

[e.g., "Update implementation plan to use native sub-issue API" or "Proceed with corrected research"]
```

**One-Liner Requirements**:
- Must highlight the key correction
- Examples:
  - ✅ "addSubIssue mutation enables native parent/child linking; eliminates custom field workaround"
  - ✅ "Found 5 missed GraphQL APIs including sub-issue operations; confidence increased to 98%"
  - ❌ "Research refined and corrected"
  - ❌ "Updated GitHub Projects research"

## Success Criteria

**Refinement is complete when**:
1. ✅ `addSubIssue` mutation fully documented (schema, examples, testing)
2. ✅ Related sub-issue APIs found and documented
3. ✅ Comprehensive search conducted for other missed APIs
4. ✅ All original "unavailable" claims re-verified with evidence
5. ✅ Corrections documented with severity and impact
6. ✅ New implementation patterns provided (using native APIs)
7. ✅ Original research file updated to v1.1
8. ✅ Old version archived
9. ✅ SUMMARY.md created with substantive one-liner
10. ✅ Impact on implementation plan assessed
11. ✅ Confidence level updated with justification
12. ✅ Methodology documented (what tools used, how verified)

**Quality Standards**:
- Every correction must have **evidence** (URL + quote from official docs)
- Every claim must be **verified** (not assumed)
- Use **all available tools** (WebSearch, WebFetch, Playwright, gh CLI)
- **Test actual GraphQL mutations** where possible
- Distinguish **verified** vs **documented** vs **assumed**

**Target Confidence**: VERY HIGH (98%+) after corrections
