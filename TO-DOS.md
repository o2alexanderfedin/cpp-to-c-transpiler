# TO-DOS

## ✅ COMPLETED: GitHub Projects Setup & Templating - 2025-12-09

**Status:** COMPLETED - All setup scripts implemented, tested, and documented

**Implementation:** Created 3 additional scripts for project templating and replication:

1. **gh-project-setup-init** - Export project structure as reusable template
2. **gh-project-setup-clone** - Clone complete project using copyProjectV2 mutation
3. **gh-project-setup-apply** - Apply field structure from template to existing project

**Location:** `scripts/gh-projects/`

**Features:**
- ✅ Template export with field definitions, options, and view metadata
- ✅ Complete project cloning with views, workflows, and fields (copyProjectV2)
- ✅ Field-only replication for existing projects
- ✅ Dry-run mode for all operations
- ✅ Comprehensive documentation and examples

**Key Findings:**
- GitHub's `copyProjectV2` mutation is the ONLY way to programmatically create views
- `createProjectV2View` mutation does NOT exist (verified via GraphQL schema introspection)
- Views must be created manually in UI or cloned via copyProjectV2

**Documentation:**
- Implementation: `scripts/gh-projects/gh-project-setup-*`
- README: `scripts/gh-projects/README.md` (updated with new section)
- Research: `.prompts/011-github-projects-setup-research/github-projects-setup-research.md`
- Template: `~/.config/gh-projects/templates/project-14.json`

## ✅ COMPLETED: GitHub Projects-Only Workflow Migration - 2025-12-09

**Status:** COMPLETED - All scripts implemented and tested

**Implementation:** Created 7 production-ready bash scripts with native sub-issue API support:

1. **gh-project-init** - Initialize configuration and cache field metadata
2. **gh-project-create** - Create draft/repo issues with custom fields
3. **gh-project-convert** - Convert draft → repository issue (irreversible)
4. **gh-project-link** - Link stories to epics using native GitHub `addSubIssue` mutation
5. **gh-project-list** - Query/filter items with advanced filtering
6. **gh-project-update** - Update custom fields
7. **gh-project-delete** - Delete drafts or remove repo issues from project

**Location:** `scripts/gh-projects/`

**Features:**
- ✅ Native sub-issue API support (addSubIssue/removeSubIssue/reprioritizeSubIssue)
- ✅ Draft-first workflow (create drafts by default, convert only when needed)
- ✅ Custom fields with automatic caching (Status, Type, Priority)
- ✅ Production quality (retry logic, error handling, dry-run mode)
- ✅ Color-coded output and comprehensive help
- ✅ Full documentation in README.md

**Key Discovery:** Research revealed native GitHub sub-issue API (initially missed), enabling Epic-Story hierarchies without custom field workarounds. This provides UI integration, progress tracking, and ecosystem support.

**Documentation:**
- Implementation plan: `.prompts/004-github-projects-scripts-plan-updated/github-projects-scripts-plan.md`
- Research (corrected): `.prompts/003-github-projects-research-refine/github-projects-research-refined.md`
- README: `scripts/gh-projects/README.md`

## ✅ COMPLETED: Repository Licensing and Visibility - 2025-12-10 18:30

**Status:** COMPLETED - Released as v0.3.5

**Implementation:** Dual licensing structure with CC BY-NC-ND 4.0 and commercial options

**Changes:**
- ✅ **Made repository private** - Changed visibility from PUBLIC to PRIVATE
- ✅ **Added CC BY-NC-ND 4.0 license** - Created LICENSE file (403 lines)
- ✅ **Implemented dual licensing** - Added LICENSE-COMMERCIAL.md with three tiers
  - Individual/Startup tier
  - Enterprise tier
  - OEM/Redistribution tier
- ✅ **Updated documentation** - README.md with dual licensing section and badges

**Release:** v0.3.5 - https://github.com/o2alexanderfedin/cpp-to-c-transpiler/releases/tag/v0.3.5

**Files:**
- `LICENSE` (403 lines) - CC BY-NC-ND 4.0 International
- `LICENSE-COMMERCIAL.md` (146 lines) - Commercial licensing terms
- `README.md` - Dual licensing section and badges
- `TO-DOS.md` - Documentation

## ✅ COMPLETED: Repository Collaborator Access - 2025-12-10 19:04

**Status:** COMPLETED - Invitation sent to EitanNahmias

**Implementation:** Added EitanNahmias as write (push) collaborator

**Details:**
- ✅ **Found Eitan's GitHub username** - EitanNahmias (Company: Hupyy)
- ✅ **Sent write permission invitation** - Created 2025-12-11 03:17:04 UTC
- ⏳ **Pending acceptance** - Awaiting EitanNahmias to accept invitation
- 🔄 **Permission downgraded** - Changed from admin to write (push access)

**Permissions (write level):**
- ✅ Read and clone repository
- ✅ Push commits and branches
- ✅ Create and manage issues/PRs
- ❌ No repository settings access
- ❌ No collaborator management

**Command used:**
```bash
# Deleted admin invitation (ID 301595748)
gh api -X DELETE repos/o2alexanderfedin/cpp-to-c-transpiler/invitations/301595748

# Created new write permission invitation
gh api repos/o2alexanderfedin/cpp-to-c-transpiler/collaborators/EitanNahmias -X PUT -f permission=push
```

**Note:** "maintain" permission level is only available for organization repositories. For personal repositories, available levels are: pull (read), push (write), admin.

**Invitation URL:** https://github.com/o2alexanderfedin/cpp-to-c-transpiler/invitations

## GitHub Pages Public Landing - 2025-12-10 19:20

- **Setup GitHub Pages with CI/CD** - Create public landing page for project documentation and progress. **Problem:** Repository is private, but need to share progress updates and architecture documentation with public audience without granting repository access. **Files:** `.github/workflows/pages.yml` (new), `docs/index.html` or `docs/index.md` (new), `README.md` (source for landing), `docs/` directory (architecture docs). **Solution:** Configure GitHub Pages to publish from `docs/` branch or directory, create GitHub Actions workflow to build and deploy on push to main, include project overview, progress tracking, architecture diagrams, and documentation links while keeping source code private.

