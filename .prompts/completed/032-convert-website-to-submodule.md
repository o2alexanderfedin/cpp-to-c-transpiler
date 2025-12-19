# Convert Website to Git Submodule

<objective>
Convert the existing `website/` directory from a monorepo structure to a git submodule, creating a new public GitHub repository named `cpp-to-c-website` while preserving the existing git history.

**Purpose**: Separate the presentation website into its own repository for independent versioning, deployment, and collaboration while maintaining it as a submodule in the main transpiler repository.

**End Goal**: The website lives in its own GitHub repository and is referenced as a git submodule in the main `cpp-to-c-transpiler` repository.
</objective>

<context>
**Current State**:
- The `website/` directory is currently tracked as a regular directory in the main repository
- Located at: `./website/`
- Contains complete Astro 4.x site with React integration
- Has recent commits in the develop branch (786e49e, 01f0fb2)
- Files are directly tracked in the main repo (not a submodule)

**Main Repository**:
- Name: `cpp-to-c-transpiler` (or `hupyy-cpp-to-c`)
- Owner: Check with `gh repo view` or git remote
- Current branch: `develop`

**New Submodule Repository**:
- Name: `cpp-to-c-website`
- Visibility: Public
- Should preserve existing website commits from main repo
</context>

<requirements>

**Functional Requirements**:
1. **Create New Repository**
   - Create public GitHub repository named `cpp-to-c-website`
   - Add description: "Astro-based presentation website for C++ to C transpiler with WebAssembly playground"
   - Initialize with README explaining it's a submodule of the main transpiler

2. **Preserve Git History**
   - Extract `website/` directory history from main repository
   - Use `git filter-branch` or `git subtree split` to create clean history
   - Push extracted history to new `cpp-to-c-website` repository
   - Ensure all commits related to website/ are preserved with original timestamps and authors

3. **Remove from Main Repository**
   - Remove `website/` directory from main repository tracking
   - Clean up git history to remove website files (optional, can be left for historical reference)
   - Update `.gitignore` if needed

4. **Add as Submodule**
   - Add `cpp-to-c-website` repository as submodule at `website/` path
   - Configure submodule in `.gitmodules`
   - Initialize and update submodule
   - Commit the submodule reference to main repository

5. **Update Documentation**
   - Update main repository README to document the submodule
   - Add section on how to clone with submodules: `git clone --recursive`
   - Document submodule update workflow: `git submodule update --remote`
   - Create or update CONTRIBUTING.md with submodule development workflow

6. **Verify Setup**
   - Test fresh clone with `--recursive` flag
   - Verify website content is accessible
   - Ensure submodule tracks correct branch (typically `main` or `develop`)
   - Confirm submodule can be updated independently

**Quality Requirements**:
- Git history must be preserved accurately (authors, dates, messages)
- Submodule must be properly initialized and tracked
- Documentation must be clear for contributors unfamiliar with submodules
- Fresh clone must work without manual intervention (via `--recursive`)

**Constraints**:
- Must use GitHub CLI (`gh`) for repository creation if available, otherwise document manual steps
- Must not lose any existing website commits
- Must maintain working state of both repositories at each step
- Should push to `develop` branch in main repo after submodule setup
</requirements>

<implementation>

**Step-by-Step Process**:

1. **Preparation**
   ```bash
   # Ensure we're on develop branch and up to date
   git checkout develop
   git pull origin develop

   # Create backup branch (safety measure)
   git branch backup-before-submodule
   ```

2. **Extract Website History**
   ```bash
   # Use git subtree split to extract website/ history
   git subtree split --prefix=website --branch website-history

   # This creates a new branch 'website-history' with only website/ commits
   ```

3. **Create New Repository**
   ```bash
   # Use GitHub CLI to create repository
   gh repo create cpp-to-c-website --public --description "Astro-based presentation website for C++ to C transpiler with WebAssembly playground"

   # If gh CLI not available, create manually on GitHub and document URL
   ```

4. **Push Website History to New Repository**
   ```bash
   # Add new repository as remote
   git remote add website-origin https://github.com/[USERNAME]/cpp-to-c-website.git

   # Push the extracted history
   git push website-origin website-history:main

   # Clean up temporary remote and branch
   git remote remove website-origin
   git branch -D website-history
   ```

5. **Remove Website from Main Repository**
   ```bash
   # Remove website directory from tracking
   git rm -r website

   # Commit the removal
   git commit -m "refactor: remove website directory in preparation for submodule conversion"
   ```

6. **Add Website as Submodule**
   ```bash
   # Add submodule at website/ path
   git submodule add https://github.com/[USERNAME]/cpp-to-c-website.git website

   # Initialize and update
   git submodule update --init --recursive

   # Commit the submodule addition
   git commit -m "feat: add website as git submodule

   Converted website/ from monorepo directory to git submodule.

   Repository: https://github.com/[USERNAME]/cpp-to-c-website
   - Preserves all existing git history
   - Enables independent versioning and deployment
   - Simplifies website-specific collaboration

   Clone with: git clone --recursive [main-repo-url]
   Update with: git submodule update --remote website

   🤖 Generated with [Claude Code](https://claude.com/claude-code)

   Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>"
   ```

7. **Push to GitHub**
   ```bash
   git push origin develop
   ```

**Avoid**:
- Don't use `git filter-branch` (deprecated, use `git subtree split` instead)
- Don't skip the backup branch (critical safety measure)
- Don't lose website commits (verify history with `git log` before and after)
- Don't hardcode username in documentation (use placeholder or detect dynamically)

**Verification at Each Step**:
- After extraction: `git log website-history` should show only website commits
- After new repo creation: Repository should be visible on GitHub
- After submodule add: `.gitmodules` file should exist with correct path
- After push: `git submodule status` should show correct commit hash
</implementation>

<output>

**Files Created/Modified**:

1. **New Repository**: `cpp-to-c-website` on GitHub
   - Contains all website history
   - README.md explaining it's a submodule
   - All existing website files

2. **Main Repository Modifications**:
   - `.gitmodules` - Submodule configuration
   - `README.md` - Add submodule documentation section
   - `CONTRIBUTING.md` - Add or update with submodule workflow (if exists)
   - `website/` - Now points to submodule instead of direct files

**Documentation to Add to README.md**:

```markdown
## Website Submodule

The presentation website is maintained as a separate repository: [cpp-to-c-website](https://github.com/[USERNAME]/cpp-to-c-website)

### Cloning with Submodules

```bash
# Clone with submodules initialized
git clone --recursive https://github.com/[USERNAME]/cpp-to-c-transpiler.git

# Or if already cloned, initialize submodules
git submodule update --init --recursive
```

### Updating the Website Submodule

```bash
# Update to latest website commit
cd website
git pull origin main
cd ..
git add website
git commit -m "chore: update website submodule"
git push
```

### Working on the Website

```bash
# Make changes in website directory
cd website
git checkout -b feature/my-changes
# ... make changes ...
git commit -am "feat: add new feature"
git push origin feature/my-changes

# Update main repo to reference new commit
cd ..
git add website
git commit -m "chore: update website submodule to include new feature"
git push
```
```
</output>

<verification>

**Before Declaring Complete**:

1. **Verify New Repository**
   ```bash
   # Check repository exists and is accessible
   gh repo view cpp-to-c-website

   # Or visit https://github.com/[USERNAME]/cpp-to-c-website
   ```

2. **Verify Git History Preserved**
   ```bash
   # In new repository, verify commits exist
   cd website
   git log --oneline | head -10
   # Should show original commits (786e49e, 01f0fb2, etc.)
   ```

3. **Verify Submodule Configuration**
   ```bash
   # Check .gitmodules file exists
   cat .gitmodules
   # Should contain [submodule "website"] with correct URL

   # Check submodule status
   git submodule status
   # Should show commit hash without '-' prefix (initialized)
   ```

4. **Test Fresh Clone**
   ```bash
   # In a temporary directory
   cd /tmp
   git clone --recursive https://github.com/[USERNAME]/cpp-to-c-transpiler.git test-clone
   cd test-clone/website
   ls -la
   # Should show all website files

   # Clean up
   cd /tmp && rm -rf test-clone
   ```

5. **Verify Build Still Works**
   ```bash
   cd website
   npm install
   npm run build
   # Should complete without errors
   ```

6. **Verify Both Repositories on GitHub**
   - Main repository shows submodule folder with link icon
   - Website repository is accessible and public
   - Both repositories have recent commits

**Edge Cases to Test**:
- Submodule works after fresh clone with `--recursive`
- Submodule can be updated with `git submodule update --remote`
- Changes in submodule can be committed and pushed
- Main repo correctly tracks submodule commit references
</verification>

<success_criteria>
- ✅ New public repository `cpp-to-c-website` created on GitHub
- ✅ All website git history preserved in new repository (verify commits 786e49e, 01f0fb2 present)
- ✅ Website removed from main repository direct tracking
- ✅ Website added as submodule at `website/` path
- ✅ `.gitmodules` file created and configured correctly
- ✅ Submodule initialized and tracking correct commit
- ✅ Documentation added to README.md for submodule usage
- ✅ Fresh clone with `--recursive` flag works
- ✅ Both repositories visible on GitHub
- ✅ Changes pushed to `develop` branch in main repository
- ✅ Website build still works (`npm run build` succeeds)

**Critical Success Indicator**:
Fresh clone test passes:
```bash
git clone --recursive [main-repo-url] && cd [repo]/website && ls
# Must show all website files without errors
```
</success_criteria>

<troubleshooting>

**Common Issues**:

1. **`git subtree split` fails or is slow**
   - Alternative: Use `git filter-repo` (install separately)
   - Or manually copy files and recreate commits (loses history but cleaner)

2. **Submodule shows as modified after clone**
   - Run: `git submodule update --init --recursive`
   - Ensure correct branch is tracked in `.gitmodules`

3. **GitHub CLI not available**
   - Create repository manually on GitHub
   - Document the URL and continue with manual remote setup

4. **Permission errors when pushing**
   - Ensure GitHub authentication is configured (`gh auth login`)
   - Check repository ownership and permissions

5. **Lost commits in history extraction**
   - Restore from backup branch: `git checkout backup-before-submodule`
   - Re-attempt extraction with verbose output to debug
</troubleshooting>

<notes>
**Why Git Submodules**:
While the monorepo approach was initially chosen for simplicity, submodules offer:
- Independent versioning for website and transpiler
- Separate deployment workflows
- Cleaner separation of concerns
- Ability to share website code across multiple projects
- Independent contributor permissions

**Trade-offs**:
- Slightly more complex workflow (requires `--recursive` flag)
- Two repositories to manage instead of one
- Submodule updates require explicit commits in main repo

**Alternative Considered**: Git subtree (simpler but less clean separation)
</notes>
