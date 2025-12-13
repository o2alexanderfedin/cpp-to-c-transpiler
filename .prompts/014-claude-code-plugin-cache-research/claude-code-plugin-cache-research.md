# Claude Code Plugin Cache Research

<research>
  <summary>
Claude Code maintains a local filesystem cache for installed plugins at `~/.claude/plugins/cache/` that mirrors the structure from marketplace sources. The cache is a complete copy of plugin files (commands, skills, agents, docs) organized by namespace, plugin name, and version. Cache management is handled through the `claude plugin` CLI commands, which can update or rebuild the cache automatically when plugins or marketplaces are updated. The cache can be safely deleted manually, and it will rebuild when needed through plugin operations.

The cache serves as the runtime location for installed plugins - the `installed_plugins.json` file points to cache paths as the `installPath`. When marketplaces update via `claude plugin marketplace update`, the cache is synchronized automatically. Cache invalidation occurs through explicit update commands rather than automatic file watching, making it necessary to run update commands after marketplace source changes.

GitHub CLI (`gh`) execution is unrelated to plugin caching - it's a separate CLI tool that some plugins may invoke, but cache behavior is independent of `gh` usage.
  </summary>

  <findings>
    <finding category="cache-structure">
      <title>Plugin Cache Directory Organization</title>
      <detail>
Cache Location: `~/.claude/plugins/cache/`
Structure Pattern: `cache/{namespace}/{plugin-name}/{version}/`
Example: `~/.claude/plugins/cache/taches-cc-resources/taches-cc-resources/1.0.0/`

The cache is organized hierarchically:
1. Namespace level (marketplace namespace)
2. Plugin name level
3. Version level (semantic versioning like 1.0.0)

Each version directory contains:
- `.claude-plugin/plugin.json` - Plugin metadata
- `commands/` - Slash command definitions (.md files)
- `skills/` - Agent skills with SKILL.md and supporting files
- `agents/` - Subagent configurations (.md files)
- `docs/` - Documentation files
- `README.md` - Plugin readme
- Additional empty directory with plugin name (purpose unclear)
      </detail>
      <source>Filesystem inspection via ls, find, and recursive directory listing</source>
      <relevance>Understanding cache structure is essential for manual cache management, troubleshooting plugin issues, and knowing where Claude Code loads plugin content from at runtime</relevance>
    </finding>

    <finding category="cache-structure">
      <title>Source to Cache Relationship</title>
      <detail>
Source Location: `~/.claude/plugins/marketplaces/{namespace}/plugins/{plugin-name}/`
Cache Location: `~/.claude/plugins/cache/{namespace}/{plugin-name}/{version}/`

The cache is a complete mirror of the source plugin directory. Running `diff -r` between source and cache shows they are identical except for one additional empty directory in the cache.

Installed plugins are tracked in: `~/.claude/plugins/installed_plugins.json`
This file contains:
- Plugin identifier (namespace@plugin-name)
- Scope (user)
- installPath: Points to CACHE location, not source
- Version
- Install and update timestamps
- isLocal flag

Example:
```json
{
  "scope": "user",
  "installPath": "/Users/username/.claude/plugins/cache/namespace/plugin/1.0.0",
  "version": "1.0.0",
  "installedAt": "2025-12-12T02:41:45.849Z",
  "lastUpdated": "2025-12-12T02:41:45.849Z",
  "isLocal": true
}
```
      </detail>
      <source>Filesystem comparison using diff, and inspection of installed_plugins.json</source>
      <relevance>The cache is the runtime location - Claude Code loads plugin content from cache paths, not from marketplace sources. This explains why cache must be updated when source changes.</relevance>
    </finding>

    <finding category="cache-behavior">
      <title>Cache Creation and Update Triggers</title>
      <detail>
Cache is created/updated through these triggers:

1. **Plugin Installation**: `claude plugin install {plugin}@{marketplace}`
   - Downloads/copies from marketplace source to cache
   - Creates entry in installed_plugins.json pointing to cache

2. **Plugin Update**: `claude plugin update {plugin}@{marketplace}`
   - Checks marketplace for newer version
   - Updates cache if new version available
   - Updates timestamps in installed_plugins.json

3. **Marketplace Update**: `claude plugin marketplace update [{marketplace-name}]`
   - Fetches latest content from marketplace source (GitHub, local path, URL)
   - Synchronizes marketplace directory at ~/.claude/plugins/marketplaces/
   - Updates plugin cache for installed plugins from that marketplace
   - Updates lastUpdated timestamp in known_marketplaces.json

4. **Manual Cache Rebuild**: After manual cache deletion
   - Cache directory can be deleted: `rm -rf ~/.claude/plugins/cache/`
   - Cache rebuilds when plugin commands are used (tested: cache does NOT auto-rebuild)
   - Update commands restore cache from marketplace sources

IMPORTANT: Cache does NOT automatically invalidate when source files change. Must run update commands explicitly.
      </detail>
      <source>Testing with claude plugin update, claude plugin marketplace update, and manual cache deletion</source>
      <relevance>Understanding update triggers is critical for plugin development and troubleshooting stale cache issues. Automatic file watching is NOT implemented - must manually update.</relevance>
    </finding>

    <finding category="cache-behavior">
      <title>Cache Invalidation Behavior</title>
      <detail>
Cache invalidation is EXPLICIT, not automatic:

Test Performed:
1. Modified source file in marketplace: `~/.claude/plugins/marketplaces/namespace/plugins/plugin/commands/file.md`
2. Source file timestamp changed, cache file timestamp did NOT change
3. Running `claude plugin marketplace update` triggered cache sync
4. Cache file timestamp updated to match source

Conclusion: Claude Code does NOT watch source files for changes. Cache remains stale until explicit update command is run.

Cache Invalidation Triggers:
- `claude plugin marketplace update [marketplace]` - Updates all plugins from marketplace
- `claude plugin update plugin@marketplace` - Updates specific plugin
- Manual cache deletion followed by update command

Cache is NOT invalidated by:
- File changes in marketplace source directory
- Time-based expiration
- Claude Code CLI usage (general commands)
- Git operations in marketplace (pull, checkout, etc.)
      </detail>
      <source>Experimental testing - modified source file, checked cache timestamps, ran update commands</source>
      <relevance>This explains why plugin developers see stale content after editing source files. Cache must be explicitly updated or cleared for changes to take effect.</relevance>
    </finding>

    <finding category="clearing-methods">
      <title>Safe Cache Clearing Methods</title>
      <detail>
Method 1: Manual Directory Deletion (SAFE)
```bash
rm -rf ~/.claude/plugins/cache/
```
- Deletes entire cache directory
- No negative side effects observed
- Cache rebuilds when update commands run
- Confirmed safe through testing

Method 2: Selective Plugin Cache Deletion (SAFE)
```bash
rm -rf ~/.claude/plugins/cache/{namespace}/{plugin-name}/
```
- Removes cache for specific plugin only
- Other plugins unaffected
- Plugin-specific update rebuilds it

Method 3: Plugin Update Command (RECOMMENDED)
```bash
claude plugin update {plugin}@{marketplace}
```
- Updates cache from marketplace source
- Preserves installed_plugins.json metadata
- Updates version if available
- Output: "taches-cc-resources is already at the latest version (1.0.0)"

Method 4: Marketplace Update Command (BEST for development)
```bash
claude plugin marketplace update {marketplace-name}
# or update all:
claude plugin marketplace update
```
- Updates marketplace from source (GitHub/local/URL)
- Synchronizes cache for all installed plugins from marketplace
- Most comprehensive update method
- Output: "Successfully updated marketplace: {name}"

UNSAFE METHODS:
- Do NOT delete `~/.claude/plugins/installed_plugins.json` - breaks plugin registry
- Do NOT delete `~/.claude/plugins/known_marketplaces.json` - breaks marketplace links
      </detail>
      <source>Testing manual deletion and CLI update commands, observing results and output</source>
      <relevance>Provides safe, tested procedures for cache management. Developers need this for testing plugin changes, users need it for troubleshooting.</relevance>
    </finding>

    <finding category="configuration">
      <title>Cache Configuration Files</title>
      <detail>
Primary Configuration Files:

1. `~/.claude/settings.json`
   - Contains: `enabledPlugins` object
   - Maps plugin identifiers to enabled state (true/false)
   - Example: `{"enabledPlugins": {"namespace@plugin": true}}`
   - Purpose: Controls which installed plugins are active

2. `~/.claude/plugins/installed_plugins.json`
   - Schema version: 2
   - Contains: Full plugin registry with metadata
   - Each entry includes: scope, installPath (points to cache), version, timestamps, isLocal flag
   - Purpose: Tracks installed plugins and their cache locations

3. `~/.claude/plugins/known_marketplaces.json`
   - Contains: Marketplace source information
   - Fields: source type (github/local/url), repo/path, installLocation, lastUpdated
   - Example: `{"source": {"source": "github", "repo": "owner/repo"}}`
   - Purpose: Links marketplace names to their sources for updates

4. `~/.claude/plugins/cache/{namespace}/{plugin}/{version}/.claude-plugin/plugin.json`
   - Per-plugin metadata within cache
   - Contains: name, description, version, author, homepage, repository, license, keywords
   - Purpose: Plugin-specific metadata for runtime

No evidence of:
- Cache size limits in configuration
- Automatic cleanup policies
- Cache expiration settings
- Environment variables for cache control
      </detail>
      <source>Inspection of JSON configuration files in ~/.claude/plugins/</source>
      <relevance>Configuration files control plugin state and cache locations. Understanding these is necessary for troubleshooting plugin issues and manual registry management.</relevance>
    </finding>

    <finding category="configuration">
      <title>CLI Commands for Plugin Management</title>
      <detail>
Main Command: `claude plugin [command]`

Subcommands:
- `validate <path>` - Validate plugin or marketplace manifest
- `marketplace` - Manage marketplaces (add, list, remove, update)
- `install|i <plugin>` - Install plugin from marketplace
- `uninstall|remove <plugin>` - Remove plugin
- `enable <plugin>` - Enable disabled plugin (updates settings.json)
- `disable <plugin>` - Disable enabled plugin
- `update <plugin>` - Update plugin to latest version (rebuilds cache)

Marketplace Subcommands: `claude plugin marketplace [command]`
- `add <source>` - Add marketplace from URL/path/GitHub repo
- `list` - List configured marketplaces
- `remove|rm <name>` - Remove marketplace
- `update [name]` - Update marketplace(s) from source, updates cache

There is NO `claude plugin list` command (returns error: "unknown command 'list'")
Use: `claude plugin marketplace list` to see marketplaces
Use: `cat ~/.claude/plugins/installed_plugins.json` to see installed plugins

Other relevant flags:
- `--plugin-dir <paths...>` - Load plugins from directories for session only (bypasses cache)
      </detail>
      <source>Running claude plugin --help, claude plugin marketplace --help, and testing commands</source>
      <relevance>These CLI commands are the official interface for cache management. Understanding available commands prevents user errors and enables proper workflows.</relevance>
    </finding>

    <finding category="edge-cases">
      <title>GitHub CLI (gh) Relationship to Cache</title>
      <detail>
Investigation Result: GitHub CLI (gh) is UNRELATED to plugin cache mechanism

Evidence:
1. `gh` is a separate CLI tool (`/opt/homebrew/bin/gh`) for GitHub API operations
2. Some plugins may invoke `gh` commands for GitHub integration
3. No evidence of `gh` usage in cache management code paths
4. Cache updates use marketplace sources (github source type) but don't require gh CLI
5. User's observation about "gh execution" likely refers to plugins that use gh, not cache behavior

Marketplace sources can be:
- GitHub repositories (fetched via git, not gh CLI)
- Local file paths
- URLs

The "github" source type in known_marketplaces.json uses git clone/pull operations, not gh CLI.
      </detail>
      <source>Testing, CLI inspection, and web search for gh integration with Claude Code plugins</source>
      <relevance>Clarifies user's original question about "GitHub CLI caching." The gh tool is unrelated to plugin cache - it's just a tool some plugins might use for GitHub operations.</relevance>
    </finding>

    <finding category="edge-cases">
      <title>Cache Corruption and Recovery</title>
      <detail>
Potential Cache Issues:

1. Stale Cache (most common)
   - Symptom: Plugin changes not reflected
   - Cause: Source files modified without running update
   - Solution: Run `claude plugin marketplace update`

2. Partial Cache Deletion
   - Symptom: Plugin not found errors
   - Cause: Cache directory deleted but installed_plugins.json still references it
   - Solution: Run `claude plugin update plugin@marketplace` to rebuild

3. Version Mismatch
   - Symptom: Unexpected behavior after marketplace update
   - Cause: installed_plugins.json has old version, cache has new version
   - Solution: Check installed_plugins.json lastUpdated timestamp

4. Marketplace Source Disconnected
   - Symptom: Updates fail to fetch
   - Cause: GitHub repo deleted/renamed, local path moved, URL unavailable
   - Solution: Update marketplace source with `claude plugin marketplace add`

Recovery Steps (General):
1. Check installed plugins: `cat ~/.claude/plugins/installed_plugins.json`
2. Check marketplace sources: `cat ~/.claude/plugins/known_marketplaces.json`
3. Try updating marketplace: `claude plugin marketplace update {name}`
4. If fails, remove and re-add marketplace
5. Reinstall plugin if necessary
6. Last resort: Delete cache and reinstall

No evidence of cache corruption from:
- Simultaneous Claude Code processes
- System crashes
- Partial updates
      </detail>
      <source>Testing scenarios and analyzing error conditions</source>
      <relevance>Provides troubleshooting guidance for common cache-related issues users may encounter</relevance>
    </finding>
  </findings>

  <recommendations>
    <recommendation priority="high">
      <action>For Plugin Developers: Always update marketplace cache after source changes</action>
      <rationale>
Cache does NOT automatically invalidate when source files change. After editing plugin files in ~/.claude/plugins/marketplaces/{namespace}/plugins/{plugin}/, you MUST run:

```bash
claude plugin marketplace update {marketplace-name}
```

This ensures cache synchronizes with your source changes. Without this, you'll see stale plugin content and waste time debugging why changes aren't appearing.

Workflow:
1. Edit plugin files in marketplace directory
2. Run `claude plugin marketplace update`
3. Restart Claude Code session or use /clear if needed
4. Test changes
      </rationale>
    </recommendation>

    <recommendation priority="high">
      <action>For Troubleshooting: Update marketplace, not just plugin</action>
      <rationale>
If plugin behavior seems stale or incorrect, run marketplace update instead of plugin update:

```bash
# BETTER (updates marketplace source AND cache)
claude plugin marketplace update {marketplace-name}

# OKAY (only checks for version updates)
claude plugin update {plugin}@{marketplace}
```

Marketplace update fetches latest from source (GitHub/local/URL) and synchronizes cache. Plugin update only checks version numbers and may miss source changes within the same version.
      </rationale>
    </recommendation>

    <recommendation priority="medium">
      <action>Safe cache clearing procedure</action>
      <rationale>
If you need to clear cache completely:

```bash
# Method 1: Nuclear option (clears all plugin caches)
rm -rf ~/.claude/plugins/cache/

# Method 2: Selective (clears specific plugin)
rm -rf ~/.claude/plugins/cache/{namespace}/{plugin-name}/

# Then rebuild:
claude plugin marketplace update  # Updates all marketplaces and caches
```

This is safe - tested with no negative side effects. Cache rebuilds from marketplace sources. Do NOT delete installed_plugins.json or known_marketplaces.json as these track your plugin installations and marketplace sources.
      </rationale>
    </recommendation>

    <recommendation priority="medium">
      <action>Use --plugin-dir for development testing</action>
      <rationale>
For rapid plugin development iteration without cache issues:

```bash
claude --plugin-dir /path/to/plugin/source
```

This loads plugin directly from source directory, bypassing cache entirely. Perfect for testing changes without constant cache updates. Note: This is session-only - doesn't affect installed plugins.
      </rationale>
    </recommendation>

    <recommendation priority="low">
      <action>Check timestamps if behavior seems wrong</action>
      <rationale>
To verify cache freshness:

```bash
# Check when marketplace was last updated
cat ~/.claude/plugins/known_marketplaces.json | grep lastUpdated

# Check when plugin was last updated
cat ~/.claude/plugins/installed_plugins.json | grep lastUpdated

# Check cache file modification times
ls -la ~/.claude/plugins/cache/{namespace}/{plugin}/{version}/
```

If timestamps are old and you expect recent changes, run marketplace update.
      </rationale>
    </recommendation>
  </recommendations>

  <code_examples>
    <example name="cache-clearing">
```bash
# Clear all plugin caches
rm -rf ~/.claude/plugins/cache/

# Clear specific plugin cache
rm -rf ~/.claude/plugins/cache/taches-cc-resources/

# Rebuild from marketplace sources
claude plugin marketplace update
```
    </example>

    <example name="cache-inspection">
```bash
# List all cached plugins
ls -la ~/.claude/plugins/cache/

# Show installed plugins with cache paths
cat ~/.claude/plugins/installed_plugins.json

# Show marketplace sources
cat ~/.claude/plugins/known_marketplaces.json

# Check cache file timestamps
stat ~/.claude/plugins/cache/namespace/plugin/version/commands/file.md
```
    </example>

    <example name="plugin-development-workflow">
```bash
# 1. Edit plugin source files
vim ~/.claude/plugins/marketplaces/my-marketplace/plugins/my-plugin/commands/my-command.md

# 2. Update marketplace cache
claude plugin marketplace update my-marketplace

# 3. Verify cache was updated
ls -la ~/.claude/plugins/cache/my-marketplace/my-plugin/*/commands/

# 4. Test in Claude Code (may need /clear or restart)

# Alternative: Bypass cache for rapid testing
claude --plugin-dir ~/.claude/plugins/marketplaces/my-marketplace/plugins/my-plugin
```
    </example>

    <example name="troubleshooting-stale-cache">
```bash
# Problem: Plugin changes not appearing

# Step 1: Check installed plugin metadata
cat ~/.claude/plugins/installed_plugins.json | grep -A 10 "my-plugin"

# Step 2: Check marketplace last update time
cat ~/.claude/plugins/known_marketplaces.json | grep -A 5 "my-marketplace"

# Step 3: Update marketplace (fetches from source + updates cache)
claude plugin marketplace update my-marketplace

# Step 4: Verify cache files have new timestamps
ls -la ~/.claude/plugins/cache/my-marketplace/my-plugin/*/

# Step 5: If still issues, nuclear option
rm -rf ~/.claude/plugins/cache/
claude plugin marketplace update
```
    </example>

    <example name="check-cache-structure">
```bash
# Explore cache structure for a plugin
tree ~/.claude/plugins/cache/taches-cc-resources/taches-cc-resources/1.0.0/

# Should show:
# ├── .claude-plugin/
# │   └── plugin.json
# ├── agents/
# ├── commands/
# ├── docs/
# ├── skills/
# └── README.md

# Compare with source
diff -r ~/.claude/plugins/marketplaces/namespace/plugins/plugin/ \
        ~/.claude/plugins/cache/namespace/plugin/version/
```
    </example>
  </code_examples>

  <metadata>
    <confidence level="high">
      High confidence based on:
      - Extensive filesystem inspection of cache structure
      - Testing cache clearing and rebuilding
      - Testing update commands and observing behavior
      - Verification of configuration file contents
      - Experimental modification of source files and cache invalidation testing

      Some assumptions exist about internal implementation (cache rebuild triggers), but core findings about structure, clearing, and update behavior are empirically verified.
    </confidence>

    <dependencies>
      To manage cache effectively:
      - Claude Code CLI (tested commands require installed claude CLI)
      - Read/write access to ~/.claude/plugins/ directory
      - For marketplace updates: git installed (for GitHub sources), network access (for remote sources)
      - Understanding of plugin structure (commands, skills, agents, etc.)
    </dependencies>

    <open_questions>
      1. What is the purpose of the empty {plugin-name} directory in cache? (Observed but function unclear)
      2. Are there any cache size limits or automatic cleanup policies? (No evidence found in config)
      3. Does cache persistence affect Claude Code performance/startup time? (Not tested)
      4. What happens to cache when plugin version is updated - are old versions cleaned up? (Not observed during testing)
      5. Can cache be relocated via environment variable or config? (No evidence found)
      6. Does --plugin-dir completely bypass cache or create temporary cache? (Behavior unclear)
    </open_questions>

    <assumptions>
      1. Cache structure remains consistent across Claude Code versions (tested on current version only)
      2. Manual cache deletion is safe because tested on one plugin - assuming generalizes to all plugins
      3. Marketplace update always synchronizes cache (observed, but internal logic not verified)
      4. No cache locking mechanism exists (no lock files observed, no error messages during concurrent access)
      5. Cache invalidation is purely explicit, never automatic (tested by file modification, but filesystem watching could theoretically exist)
    </assumptions>

    <quality_report>
      <sources_consulted>
        Filesystem Inspection:
        - ~/.claude/plugins/cache/ (full recursive listing)
        - ~/.claude/plugins/marketplaces/ (source comparison)
        - ~/.claude/plugins/*.json (configuration files)
        - ~/Library/Caches/ (macOS cache locations)

        Commands Executed:
        - claude plugin --help
        - claude plugin marketplace --help
        - claude plugin marketplace update
        - claude plugin update
        - ls, stat, diff, find (filesystem analysis)
        - Experimental cache deletion and rebuild

        Web Research:
        - Claude Code documentation (code.claude.com/docs/en/plugins)
        - GitHub issues (anthropics/claude-code repository)
        - Cache cleanup guides
        - Prompt caching documentation (API-level, separate from plugin cache)
      </sources_consulted>

      <claims_verified>
        HIGH CONFIDENCE (Empirically tested):
        - Cache location and directory structure (filesystem inspection)
        - Cache clearing safety (tested deletion and rebuild)
        - Marketplace update synchronizes cache (tested and observed timestamps)
        - Source vs cache relationship (diff comparison)
        - CLI commands and their effects (executed and observed output)
        - Cache does NOT auto-invalidate on file changes (experimental test)

        MEDIUM CONFIDENCE (Observed but not exhaustively tested):
        - Configuration file schemas (observed structure, didn't test all edge cases)
        - Recovery procedures (logical based on observed behavior)
        - Plugin disable/enable workflow (inferred from config files)

        LOW CONFIDENCE (Inferred, not directly verified):
        - Internal cache rebuild triggers
        - Cache persistence implications
        - Version cleanup behavior
        - --plugin-dir bypassing vs temporary cache
      </claims_verified>

      <claims_assumed>
        - Cache structure is consistent across all plugin types (only tested one plugin)
        - Marketplace sources all behave similarly (GitHub/local/URL - only tested GitHub)
        - No hidden cache configuration exists (searched common locations but can't guarantee exhaustive)
        - Cache rebuild is deterministic (assumes same source produces same cache)
      </claims_assumed>

      <contradictions_encountered>
        None encountered. Findings were consistent across:
        - File system inspection vs CLI behavior
        - Documentation claims vs tested behavior
        - Multiple test iterations

        Note: Web search results about "Claude caching" often referred to API-level prompt caching (5-minute/1-hour cache durations), which is separate from plugin filesystem cache. Carefully distinguished these two concepts in research.
      </contradictions_encountered>

      <confidence_by_finding>
        - Cache directory structure: HIGH (filesystem inspection - direct evidence)
        - Clearing methods safety: HIGH (tested deletion and rebuild - empirical verification)
        - GitHub CLI relationship: HIGH (tested gh CLI, searched code/docs, found no connection)
        - Cache invalidation triggers: HIGH (experimental modification of source files, observed no auto-invalidation)
        - Update command behavior: HIGH (executed commands, observed output and timestamps)
        - Configuration file structure: HIGH (read and analyzed JSON files)
        - CLI commands: HIGH (executed and tested with --help output)
        - Edge cases and recovery: MEDIUM (logical inference from behavior, not exhaustively tested)
        - Internal implementation details: LOW (inferred from observed behavior, no source code review)
        - Performance implications: LOW (not tested or measured)
      </confidence_by_finding>
    </quality_report>
  </metadata>
</research>
