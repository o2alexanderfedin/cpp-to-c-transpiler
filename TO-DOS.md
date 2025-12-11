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

## Repository Licensing and Visibility - 2025-12-10 18:30

- **Make repository private** - Change repository visibility from public to private. **Problem:** Repository is currently public (visibility: PUBLIC), needs to be private to restrict access. **Files:** Repository settings (via `gh repo edit`). **Solution:** Use `gh repo edit o2alexanderfedin/cpp-to-c-transpiler --visibility private`.

- **Add CC BY-NC-ND main license** - Create LICENSE file with Creative Commons Attribution-NonCommercial-NoDerivatives 4.0 International. **Problem:** No LICENSE file exists in repository, need to establish clear licensing terms for non-commercial, no-derivatives use. **Files:** `LICENSE` (new file at repository root). **Solution:** Use official CC BY-NC-ND 4.0 license text from creativecommons.org.

- **Make license dual** - Implement dual licensing structure. **Problem:** Need both restrictive default license (CC BY-NC-ND) and alternative commercial licensing option. **Files:** `LICENSE` (main license), `LICENSE-COMMERCIAL.md` (new, commercial terms), `README.md` (licensing section explaining dual structure). **Solution:** Add commercial licensing terms file, update README with clear explanation of dual licensing options and how to obtain commercial license.

