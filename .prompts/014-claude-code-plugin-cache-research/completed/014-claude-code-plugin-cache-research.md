# Claude Code Plugin Cache Research

<session_initialization>
Before beginning research, verify today's date:
!`date +%Y-%m-%d`

Use this date when searching for "current" or "latest" information.
</session_initialization>

<research_objective>
Research Claude Code's plugin cache mechanism located in `~/.claude/plugins/cache/` to understand its structure, behavior, and clearing methods.

Purpose: Understand how Claude Code caches plugin prompts and how to properly manage/clear the cache
Scope: Cache structure, caching triggers, cache invalidation, clearing procedures
Output: claude-code-plugin-cache-research.md with structured findings
</research_objective>

<research_scope>
<include>
**Cache Structure & Organization**
- File structure in `~/.claude/plugins/cache/`
- Naming conventions for cached files (*.md)
- Cache key generation mechanism
- Relationship between cache files and source plugin files

**Caching Behavior**
- When cache is created/updated
- What triggers cache invalidation
- How Claude Code determines cache freshness
- Relationship with GitHub CLI (gh) execution mentioned in user context
- Cache hit/miss logic

**Cache Clearing & Management**
- Safe methods to clear cache (manual file deletion, CLI commands)
- What happens when cache is cleared
- Impact on plugin functionality
- Cache rebuild process
- Selective cache clearing (single plugin vs. all)

**Configuration & Control**
- Environment variables affecting cache behavior
- Configuration file settings related to caching
- Programmatic cache control options
- Cache size limits and cleanup policies

**Edge Cases & Issues**
- Stale cache problems
- Cache corruption scenarios
- What happens when source plugin changes
- Debugging cache-related issues
</include>

<exclude>
- General Claude Code usage unrelated to caching
- Plugin development details (unless directly related to cache behavior)
- Network caching or HTTP caching (focus on local file cache)
</exclude>

<sources>
**Filesystem Investigation** (use Read, Glob, Bash):
- Examine `~/.claude/plugins/cache/` structure
- Check for configuration files that reference cache behavior
- Look for cache-related environment variables or settings

**Code Search** (use Grep if Claude Code source is available):
- Search for cache-related implementation
- Look for cache invalidation logic
- Find configuration options

**Documentation** (use WebSearch, WebFetch):
- "Claude Code plugin cache 2025"
- "Claude Code cache clearing"
- Official Claude Code documentation on caching
- GitHub issues related to plugin cache

**Experimentation** (use Bash):
- Examine cache file contents and structure
- Test cache clearing procedures
- Verify cache rebuild behavior
</sources>
</research_scope>

<verification_checklist>
**Cache Location & Structure**
□ Verify exact cache directory path and permissions
□ Document file naming pattern with examples
□ Identify all file types in cache directory
□ Map relationship between cache files and source plugins

**Cache Behavior**
□ Document when cache is created (with evidence/testing)
□ Identify what triggers cache updates
□ Verify cache invalidation conditions
□ Test and document GitHub CLI relationship (user's observation)

**Clearing Methods**
□ Test manual file deletion safety
□ Search for official CLI cache clearing commands
□ Document cache rebuild process with verification
□ Confirm no negative side effects from clearing

**Configuration**
□ Search for all cache-related configuration options
□ Document default vs. configurable settings
□ Verify environment variable effects (if any)
□ Check for undocumented cache controls

**Quality Assurance**
□ Verify all claims with actual filesystem inspection or official docs
□ Test clearing procedures before recommending
□ Document any assumptions clearly
□ Note if GitHub CLI caching is separate or integrated
</verification_checklist>

<research_quality_assurance>
<completeness_check>
- [ ] All cache directory contents examined and documented
- [ ] Cache clearing methods tested and verified safe
- [ ] Official documentation cited for critical claims
- [ ] User's GitHub CLI observation investigated and explained
</completeness_check>

<source_verification>
- [ ] Filesystem inspection completed with actual directory listings
- [ ] Cache file examples included in findings
- [ ] Clearing procedures tested before recommending
- [ ] Distinguish verified facts from assumptions
</source_verification>

<blind_spots_review>
Ask yourself: "What might I have missed?"
- [ ] Are there multiple cache locations beyond ~/.claude/plugins/cache/?
- [ ] Did I check for cache-related logs or debugging output?
- [ ] Did I verify behavior across different plugin types?
- [ ] Did I investigate the GitHub CLI execution observation?
</blind_spots_review>

<critical_claims_audit>
For any statement like "X is the only way" or "cache cannot be cleared while running":
- [ ] Is this verified by testing or official documentation?
- [ ] Have I checked for alternative approaches?
- [ ] Are there edge cases or exceptions?
</critical_claims_audit>
</research_quality_assurance>

<output_requirements>
Write findings incrementally to `claude-code-plugin-cache-research.md` as you discover them:

1. Create the file with this initial structure:
   ```xml
   <research>
     <summary>[Will complete at end]</summary>
     <findings></findings>
     <recommendations></recommendations>
     <code_examples></code_examples>
     <metadata></metadata>
   </research>
   ```

2. As you research each aspect, immediately append findings:
   - Examine cache directory → Write finding
   - Test clearing method → Write finding
   - Find configuration option → Write finding
   - Discover GitHub CLI relationship → Write finding

3. After all research complete:
   - Write summary (synthesize all findings)
   - Write recommendations (cache management best practices)
   - Write metadata (confidence, dependencies, open questions, quality report)

This incremental approach ensures all work is saved even if execution hits token limits. Never generate the full output in memory first.
</output_requirements>

<output_structure>
Save to: `.prompts/014-claude-code-plugin-cache-research/claude-code-plugin-cache-research.md`

Structure findings using this XML format:

```xml
<research>
  <summary>
    {2-3 paragraph executive summary of cache mechanism, structure, and clearing methods}
  </summary>

  <findings>
    <finding category="cache-structure">
      <title>{Finding title}</title>
      <detail>{Detailed explanation with examples}</detail>
      <source>{Filesystem inspection, documentation, testing}</source>
      <relevance>{Why this matters for cache management}</relevance>
    </finding>
    <!-- Additional findings for cache-behavior, clearing-methods, configuration, etc. -->
  </findings>

  <recommendations>
    <recommendation priority="high">
      <action>{How to clear cache safely}</action>
      <rationale>{Why this method is recommended}</rationale>
    </recommendation>
    <!-- Additional recommendations -->
  </recommendations>

  <code_examples>
    <example name="cache-clearing">
    ```bash
    # Safe cache clearing command
    [command here]
    ```
    </example>

    <example name="cache-inspection">
    ```bash
    # How to examine cache contents
    [command here]
    ```
    </example>
  </code_examples>

  <metadata>
    <confidence level="{high|medium|low}">
      {Why this confidence level - based on testing, documentation, or inference}
    </confidence>
    <dependencies>
      {What's needed to manage cache effectively}
    </dependencies>
    <open_questions>
      {What couldn't be determined - especially about GitHub CLI relationship}
    </open_questions>
    <assumptions>
      {What was assumed during research}
    </assumptions>

    <quality_report>
      <sources_consulted>
        {List actual directories examined, commands run, docs reviewed}
      </sources_consulted>
      <claims_verified>
        {Key findings verified through testing or official sources}
      </claims_verified>
      <claims_assumed>
        {Findings based on inference or incomplete information}
      </claims_assumed>
      <contradictions_encountered>
        {Any conflicting information found and how resolved}
      </contradictions_encountered>
      <confidence_by_finding>
        - Cache directory structure: {High|Medium|Low} (filesystem inspection)
        - Clearing methods safety: {High|Medium|Low} (tested/documented)
        - GitHub CLI relationship: {High|Medium|Low} (observed/inferred)
        - Cache invalidation triggers: {High|Medium|Low} (tested/documented)
      </confidence_by_finding>
    </quality_report>
  </metadata>
</research>
```
</output_structure>

<summary_requirements>
Create `.prompts/014-claude-code-plugin-cache-research/SUMMARY.md`

Must include:
- **One-liner**: Substantive description like "Cache located in ~/.claude/plugins/cache/, safe to delete, rebuilds automatically"
- **Key Findings**: Top 3-4 discoveries about cache structure and clearing
- **Decisions Needed**: Any confirmation needed from user (or "None")
- **Blockers**: External impediments (likely "None")
- **Next Step**: Concrete action like "Clear cache using [method]" or "Create cache management script"

Display actual findings, not generic "research completed".
</summary_requirements>

<pre_submission_checklist>
Before submitting your research report, confirm:

**Scope Coverage**
- [ ] Cache directory examined with actual file listings
- [ ] All clearing methods documented and tested
- [ ] GitHub CLI relationship investigated
- [ ] Configuration options searched thoroughly

**Claim Verification**
- [ ] Each clearing method tested or verified in official docs
- [ ] Cache structure documented with real examples
- [ ] Safety claims backed by testing or authoritative sources
- [ ] Confidence levels reflect actual verification depth

**Quality Controls**
- [ ] Blind spots review completed ("What did I miss?")
- [ ] Quality report filled out honestly
- [ ] Assumptions distinguished from verified facts
- [ ] User's GitHub CLI observation explained or flagged as open question

**Output Completeness**
- [ ] All required XML sections present
- [ ] SUMMARY.md created with substantive one-liner
- [ ] Code examples include actual working commands
- [ ] Next steps clearly identified
</pre_submission_checklist>

<success_criteria>
- Cache directory structure documented with examples
- Safe clearing methods tested and verified
- GitHub CLI relationship explained or marked as open question
- Recommendations are actionable and safe
- Quality report distinguishes verified from inferred findings
- SUMMARY.md provides quick actionable guidance
- Ready for user to manage cache effectively
</success_criteria>
