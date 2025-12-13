# Claude Code Plugin Cache Research Summary

## One-Liner
Cache located in `~/.claude/plugins/cache/`, safe to delete manually, rebuilds via `claude plugin marketplace update`, does NOT auto-invalidate on source changes - explicit update required.

## Key Findings

1. **Cache Location and Structure**: `~/.claude/plugins/cache/{namespace}/{plugin-name}/{version}/` - complete mirror of marketplace source, serves as runtime location (installed_plugins.json points to cache paths)

2. **Cache Invalidation is EXPLICIT**: Source file changes do NOT automatically update cache. Must run `claude plugin marketplace update {marketplace}` to synchronize. No file watching implemented.

3. **Safe Clearing Methods**:
   - Nuclear: `rm -rf ~/.claude/plugins/cache/` (tested safe)
   - Selective: `rm -rf ~/.claude/plugins/cache/{namespace}/{plugin}/`
   - Rebuild: `claude plugin marketplace update` (fetches from source + syncs cache)

4. **GitHub CLI (gh) is UNRELATED**: Cache uses git operations for GitHub sources, not gh CLI. User's "gh execution" observation likely refers to plugins that invoke gh commands, not cache mechanism.

## Decisions Needed
None - research complete with high confidence findings.

## Blockers
None.

## Next Step
For plugin developers: Use `claude plugin marketplace update {marketplace}` after editing source files to sync cache. For rapid iteration, use `claude --plugin-dir /path/to/source` to bypass cache entirely.

## Quick Reference

### Developer Workflow
```bash
# 1. Edit plugin source
vim ~/.claude/plugins/marketplaces/my-marketplace/plugins/my-plugin/commands/file.md

# 2. Update cache (REQUIRED - no auto-invalidation)
claude plugin marketplace update my-marketplace

# 3. Test changes
```

### Troubleshooting Stale Cache
```bash
# Check timestamps
cat ~/.claude/plugins/known_marketplaces.json | grep lastUpdated
cat ~/.claude/plugins/installed_plugins.json | grep lastUpdated

# Update marketplace and cache
claude plugin marketplace update my-marketplace

# Nuclear option if needed
rm -rf ~/.claude/plugins/cache/
claude plugin marketplace update
```

### Rapid Development Testing
```bash
# Bypass cache completely for session
claude --plugin-dir ~/.claude/plugins/marketplaces/my-marketplace/plugins/my-plugin
```

## Research Confidence
**HIGH** - Findings based on:
- Extensive filesystem inspection
- Experimental testing (cache deletion, source modification, update commands)
- CLI command verification
- Configuration file analysis

See full research document for detailed findings, code examples, and quality report.
