# Auto-Configuration Implementation Summary

## Quick Reference

This document provides a high-level overview of the auto-configuration implementation plan. For full details, see `AUTO_CONFIG_IMPLEMENTATION_PLAN.md`.

## What We're Building

Add automatic project configuration detection to GitHub Projects scripts, eliminating manual setup in 90% of cases while maintaining 100% backward compatibility.

## Core Strategy

**Detection Cascade** (priority order):

1. **Environment Variable** (`GH_PROJECT_NUMBER`) - User override
2. **Repository Link** (GraphQL) - Auto-detect from repo-project link
3. **Single Project** (GraphQL) - Auto-select if user has exactly 1 project
4. **Explicit Error** - Clear message with manual fallback instructions

## Key Functions

### New Functions (6 total)

```bash
auto_init_config()                      # Main orchestration
detect_project_from_env()               # Strategy 1
detect_project_from_repo_link()         # Strategy 2
get_single_project()                    # Strategy 3
get_current_context()                   # Helper: get owner/repo
initialize_config_from_project()        # Helper: save config
```

### Modified Functions (1 total)

```bash
load_config()  # Add auto-init attempt before failing
```

## Critical Requirements

### Portability (Non-Negotiable)

- Zero hardcoded values (no specific users, repos, projects)
- Dynamic context detection (use `gh repo view`, `gh api viewer`)
- Works for ANY user, ANY repository, ANY environment
- Multi-user support (config per user in `~/.config/gh-projects/`)

### Testing

Must test ALL these scenarios:
- Different GitHub users (not just current user)
- Different repositories (not just current repo)
- Users with 0, 1, many projects
- Repos with no linked projects, 1 linked project, many linked projects
- Non-git directories (graceful failure)

### Backward Compatibility

- Existing configs: Continue working
- Manual init: Still functional
- Environment variables: Still override config
- No breaking changes: 100% guarantee

## Implementation Checklist

### Code Changes
- [ ] 6 new functions in `gh-project-common.sh`
- [ ] 1 modified function (`load_config`)
- [ ] Error message helpers (inline or functions)

### Testing
- [ ] Unit tests (test each function independently)
- [ ] Integration tests (test end-to-end scenarios)
- [ ] Portability tests (different users/repos/environments)
- [ ] Backward compatibility tests (existing workflows)

### Documentation
- [ ] Update README.md (Getting Started section)
- [ ] Add troubleshooting guide
- [ ] Function documentation (inline comments)

## Success Criteria

- Auto-init succeeds in ≥90% of test cases
- Zero breaking changes
- API calls ≤3 per auto-init attempt
- Initialization time <5 seconds
- Test coverage: 100% of new functions
- Clear, actionable error messages

## Error Messages

All error messages must:
- Explain what went wrong
- Provide 2-3 specific solutions
- Include example commands
- Be helpful, not technical

Example:
```
✗ Could not auto-initialize configuration.

Multiple projects found. Cannot auto-select.

Specify which project to use:
  1. Set environment variable: export GH_PROJECT_NUMBER=14
  2. Run manual init: gh-project-init --project 14
  3. Link repository: gh-project-link-repo --project 14

List your projects:
  gh-project-list
```

## Rollback Plan

**Risk Level: LOW** (changes isolated to single file)

**Rollback Options:**
1. **Full revert**: `git revert <commit>`
2. **Partial revert**: Revert only `load_config()` modification
3. **User workaround**: Manual init still works

**Rollback Criteria:**
- Failures in >10% of cases
- Confusing error messages
- Performance degradation (>2s delay)
- Breaks existing functionality

## Timeline

- **Phase 1**: Core implementation (2-3 hours)
- **Phase 2**: Testing (2-3 hours)
- **Phase 3**: Documentation (1 hour)
- **Phase 4**: Validation (1 hour)

**Total: 6-8 hours**

## Key Design Decisions

### ✅ Included

- Environment variable override (explicit user control)
- Repository-link detection (verified working)
- Single project fallback (simple, unambiguous)
- Graceful error messages (clear next steps)

### ❌ Excluded

- Fuzzy name matching (too unreliable)
- Project name guessing (error-prone)
- Interactive prompts (breaks scripting)
- Global config (not user-specific)

## File Changes

**Modified:**
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/scripts/gh-projects/lib/gh-project-common.sh`
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/scripts/gh-projects/README.md`

**New:**
- `tests/test-auto-init.sh` (unit tests)
- `tests/test-integration.sh` (integration tests)
- `tests/test-portability.sh` (portability tests)

## GraphQL Queries

**Repo-Project Link:**
```graphql
query($owner: String!, $name: String!) {
  repository(owner: $owner, name: $name) {
    projectsV2(first: 10) {
      nodes { number, title, closed }
    }
  }
}
```

**User Projects:**
```graphql
query {
  viewer {
    projectsV2(first: 100) {
      nodes { number, closed }
      totalCount
    }
  }
}
```

## Next Steps

1. Review this plan and `AUTO_CONFIG_IMPLEMENTATION_PLAN.md`
2. Approve implementation approach
3. Begin Phase 1: Core implementation
4. Execute testing phases with different users/repos
5. Update documentation
6. Deploy and monitor

## Questions to Resolve

- [ ] Should we cache detection results to avoid repeated API calls?
- [ ] Should we add telemetry to track auto-init success rate?
- [ ] Should we add `--no-auto-init` flag for explicit manual mode?
- [ ] Should we create a migration guide for existing users?

All questions have reasonable defaults if not answered (no caching, no telemetry, no flag, no migration guide needed).
