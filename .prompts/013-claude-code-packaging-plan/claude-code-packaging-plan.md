# Claude Code Configuration Packaging Implementation Roadmap

<plan_metadata>
<date>2025-12-10</date>
<version>v1.0</version>
<purpose>3-phase implementation plan for packaging claude-config as distributable Claude Code plugin</purpose>
<repository>https://github.com/o2alexanderfedin/claude-config</repository>
<current_version>v0.1.0</current_version>
<target_versions>v0.2.0, v0.3.0, v0.4.0</target_versions>
</plan_metadata>

---

## Executive Summary

This roadmap transforms the claude-config repository into a professionally distributable Claude Code plugin with three incremental, independently valuable phases:

**Phase 1 (v0.2.0):** Plugin conversion - Minimal effort, maximum impact
**Phase 2 (v0.3.0):** Bootstrap installer - Automated deployment for teams
**Phase 3 (v0.4.0):** Container images - Enterprise-ready containerized distribution

Each phase is non-breaking to existing git-flow workflows and adds tangible value independently.

### Current State Analysis

**Repository:** https://github.com/o2alexanderfedin/claude-config v0.1.0

**Current Contents:**
- `scripts/gh-projects/` - 11 GitHub Projects management scripts (gh-project-init, gh-project-create, etc.)
  - Production-ready bash scripts with native sub-issue API support
  - Shared library: `lib/gh-project-common.sh`
  - Templates: `templates/cpp-transpiler.json`
- `.claude/skills/` - Empty (skills not yet migrated to repository)
- `.claude/commands/` - Empty (commands not yet migrated to repository)

**Distribution Method:** Manual git clone
**Installation:** Manual copy to `~/.claude/`
**Updates:** Manual git pull

### Key Research Findings

Based on comprehensive research (see `.prompts/012-claude-code-packaging-research/`):

1. **Plugin system is production-ready** (Oct 2025 public beta)
   - 185+ skills and 255+ plugins in ecosystem
   - Simple structure: `.claude-plugin/plugin.json` + existing directories
   - One-command install: `/plugin install user/repo`

2. **Official Docker support exists**
   - `docker/sandbox-templates:claude-code` official image
   - Persistent credential management
   - DevContainer integration

3. **GitHub Actions integration** (Sep 2025 release)
   - `anthropics/claude-code-action@v1` official action
   - CI/CD automation workflows

4. **Git workflow remains central**
   - Version control and branching still best practices
   - Plugin system complements, not replaces git-flow
   - Non-breaking to existing development processes

---

## Phase 1: Plugin Conversion (v0.2.0)

**Timeline:** 1-2 hours
**Impact:** HIGH - Enables native installation ecosystem
**Effort:** LOW - Minimal code changes
**Value:** Immediate discoverability and professional distribution

### Objectives

Transform claude-config into an official Claude Code plugin while maintaining backward compatibility with manual installation methods.

### Tasks

#### 1.1 Create Plugin Manifest (30 minutes)

**File:** `.claude-plugin/plugin.json`

```json
{
  "name": "claude-config",
  "version": "0.2.0",
  "description": "GitHub Projects management scripts and workflows for SCRUM/Kanban development with Claude Code. Includes 11 production-ready scripts for epics, user stories, and native sub-issue linking.",
  "author": {
    "name": "Alexander Fedin",
    "email": "[email protected]"
  },
  "repository": "https://github.com/o2alexanderfedin/claude-config",
  "license": "MIT",
  "keywords": [
    "github-projects",
    "scrum",
    "kanban",
    "project-management",
    "git-flow",
    "epic",
    "user-story",
    "gh-cli",
    "scripts"
  ],
  "engines": {
    "claude-code": ">=2.0.0"
  },
  "dependencies": {
    "system": [
      "gh",
      "git",
      "jq"
    ],
    "optional": [
      "git-flow"
    ]
  }
}
```

**Validation:**
- JSON syntax valid
- Version matches git tag plan
- Keywords optimize discovery
- Dependencies documented

#### 1.2 Create Marketplace Manifest (15 minutes)

**File:** `.claude-plugin/marketplace.json`

```json
{
  "name": "o2alexanderfedin-tools",
  "owner": {
    "name": "Alexander Fedin",
    "email": "[email protected]"
  },
  "plugins": [
    {
      "name": "claude-config",
      "source": "./",
      "description": "GitHub Projects management scripts and workflows for SCRUM/Kanban development",
      "version": "0.2.0"
    }
  ]
}
```

#### 1.3 Update Directory Structure (30 minutes)

**Current Issue:** Skills and commands are in `.claude/` but should be in repository root for plugin distribution.

**Migration:**

```bash
# Create repository-level directories
mkdir -p skills
mkdir -p commands
mkdir -p bin

# Move GitHub Projects scripts to bin
mv scripts/gh-projects/* bin/gh-projects/

# Note: Skills and commands directories will be empty initially
# They will be populated in future development
```

**Target Structure:**
```
claude-config/
├── .claude-plugin/
│   ├── plugin.json
│   └── marketplace.json
├── skills/                    # Future: epic-to-user-stories, ensure-git-repo-setup
│   └── .gitkeep
├── commands/                  # Future: slash commands
│   └── .gitkeep
├── bin/
│   └── gh-projects/          # Existing 11 scripts
│       ├── gh-project-init
│       ├── gh-project-create
│       ├── gh-project-link
│       ├── gh-project-link-repo
│       ├── gh-project-list
│       ├── gh-project-update
│       ├── gh-project-delete
│       ├── gh-project-convert
│       ├── gh-project-setup-init
│       ├── gh-project-setup-clone
│       ├── gh-project-setup-apply
│       ├── lib/
│       │   └── gh-project-common.sh
│       └── templates/
│           └── cpp-transpiler.json
├── scripts/                   # Keep old location for backward compatibility
│   └── gh-projects -> ../bin/gh-projects  # Symlink
├── .gitignore
├── README.md
└── LICENSE
```

**Backward Compatibility:** Create symlink from `scripts/gh-projects` to `bin/gh-projects` to maintain existing documentation links.

#### 1.4 Update README.md (45 minutes)

**Sections to Add:**

1. **Installation Methods** (multi-option approach)
   ```markdown
   ## Installation

   ### Method 1: Plugin Installation (Recommended)

   Install directly from Claude Code:

   ```bash
   /plugin install o2alexanderfedin/claude-config
   ```

   Scripts will be available at: `~/.claude/plugins/cache/o2alexanderfedin/claude-config/*/bin/gh-projects/`

   ### Method 2: Manual Installation

   Clone and copy to your Claude Code configuration:

   ```bash
   git clone https://github.com/o2alexanderfedin/claude-config.git
   cd claude-config

   # Copy scripts
   cp -r bin/gh-projects ~/.claude/bin/
   chmod +x ~/.claude/bin/gh-projects/*

   # Add to PATH
   echo 'export PATH="$PATH:$HOME/.claude/bin/gh-projects"' >> ~/.zshrc
   source ~/.zshrc
   ```

   ### Method 3: Direct Repository Use

   Use scripts directly from the repository:

   ```bash
   git clone https://github.com/o2alexanderfedin/claude-config.git
   cd claude-config

   # Add to PATH
   echo 'export PATH="$PATH:$(pwd)/bin/gh-projects"' >> ~/.zshrc
   source ~/.zshrc
   ```
   ```

2. **Plugin Features Section**
   - Automatic updates (when available)
   - Version management
   - Integration with Claude Code ecosystem

3. **Prerequisites**
   - System dependencies (gh, git, jq)
   - Optional dependencies (git-flow)
   - GitHub CLI authentication

#### 1.5 Add .gitignore Rules (5 minutes)

```gitignore
# Existing rules
...

# Plugin cache (development)
.claude-plugin/cache/

# User templates (local customizations)
templates/user/

# Secrets and credentials
.env
.env.*
*.key
*.pem
secrets.json
```

#### 1.6 Create LICENSE File (10 minutes)

**File:** `LICENSE`

```
MIT License

Copyright (c) 2025 Alexander Fedin

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
```

#### 1.7 Create GitHub Release Automation (30 minutes)

**File:** `.github/workflows/release.yml`

```yaml
name: Release Plugin

on:
  push:
    tags:
      - 'v*'

permissions:
  contents: write

jobs:
  release:
    runs-on: ubuntu-latest

    steps:
      - name: Checkout code
        uses: actions/checkout@v4

      - name: Validate plugin structure
        run: |
          # Check required files
          test -f .claude-plugin/plugin.json || {
            echo "ERROR: Missing .claude-plugin/plugin.json"
            exit 1
          }

          test -d bin/gh-projects || {
            echo "ERROR: Missing bin/gh-projects directory"
            exit 1
          }

          # Validate plugin.json syntax
          jq empty .claude-plugin/plugin.json || {
            echo "ERROR: Invalid plugin.json syntax"
            exit 1
          }

          echo "✓ Plugin structure validated"

      - name: Extract and validate version
        id: version
        run: |
          # Extract version from tag
          TAG_VERSION=${GITHUB_REF#refs/tags/v}
          echo "tag_version=$TAG_VERSION" >> $GITHUB_OUTPUT

          # Extract version from plugin.json
          PLUGIN_VERSION=$(jq -r '.version' .claude-plugin/plugin.json)
          echo "plugin_version=$PLUGIN_VERSION" >> $GITHUB_OUTPUT

          # Validate versions match
          if [ "$TAG_VERSION" != "$PLUGIN_VERSION" ]; then
            echo "ERROR: Tag version ($TAG_VERSION) doesn't match plugin.json version ($PLUGIN_VERSION)"
            exit 1
          fi

          echo "✓ Version $TAG_VERSION validated"

      - name: Count assets
        id: assets
        run: |
          SCRIPT_COUNT=$(find bin/gh-projects -type f -executable | wc -l | tr -d ' ')
          echo "script_count=$SCRIPT_COUNT" >> $GITHUB_OUTPUT

          echo "✓ Found $SCRIPT_COUNT executable scripts"

      - name: Create release archive
        run: |
          tar -czf claude-config-${{ steps.version.outputs.tag_version }}.tar.gz \
            .claude-plugin/ \
            bin/ \
            skills/ \
            commands/ \
            README.md \
            LICENSE

          echo "✓ Created release archive"

      - name: Generate release notes
        id: release_notes
        run: |
          cat > RELEASE_NOTES.md <<'EOF'
          ## Claude Code Configuration v${{ steps.version.outputs.tag_version }}

          GitHub Projects management plugin for Claude Code with production-ready SCRUM/Kanban workflows.

          ### Installation

          **Via Claude Code Plugin System (Recommended):**
          ```bash
          /plugin install o2alexanderfedin/claude-config
          ```

          **Manual Installation:**
          ```bash
          curl -fsSL https://github.com/o2alexanderfedin/claude-config/archive/v${{ steps.version.outputs.tag_version }}.tar.gz | tar -xz
          cd claude-config-${{ steps.version.outputs.tag_version }}
          cp -r bin/gh-projects ~/.claude/bin/
          chmod +x ~/.claude/bin/gh-projects/*
          ```

          ### What's Included

          **Scripts:** ${{ steps.assets.script_count }} executable scripts
          - `gh-project-init` - Initialize configuration and cache
          - `gh-project-create` - Create repository issues with custom fields
          - `gh-project-link` - Link stories to epics (native sub-issue API)
          - `gh-project-link-repo` - Link project to repository
          - `gh-project-list` - Query and filter items
          - `gh-project-update` - Update custom fields
          - `gh-project-delete` - Remove items from project
          - `gh-project-convert` - Convert drafts to repository issues
          - `gh-project-setup-init` - Export project templates
          - `gh-project-setup-clone` - Clone complete projects
          - `gh-project-setup-apply` - Apply field configurations

          **Features:**
          - ✅ Native GitHub sub-issue API support
          - ✅ Atomic draft→convert workflow
          - ✅ Custom fields (Status, Type, Priority)
          - ✅ Project templating and cloning
          - ✅ Production-quality error handling

          ### Prerequisites

          - [GitHub CLI](https://cli.github.com/) (gh) - authenticated
          - [jq](https://stedolan.github.io/jq/) - JSON processor
          - Git (for repository operations)
          - Git-flow (optional, for release workflows)

          ### Quick Start

          ```bash
          # Initialize configuration
          gh-project-init --project YOUR_PROJECT_NUMBER

          # Link project to repository
          gh-project-link-repo --project YOUR_PROJECT_NUMBER

          # Create an epic
          gh-project-create --title "Epic: My Feature" --type epic

          # Create stories
          gh-project-create --title "Story: Implement X" --type story

          # Link story to epic
          gh-project-link --parent EPIC_NUM --child STORY_NUM
          ```

          ### Documentation

          - [Full README](https://github.com/o2alexanderfedin/claude-config/blob/v${{ steps.version.outputs.tag_version }}/README.md)
          - [Scripts Documentation](https://github.com/o2alexanderfedin/claude-config/blob/v${{ steps.version.outputs.tag_version }}/bin/gh-projects/README.md)

          ### Changelog

          See [CHANGELOG.md](https://github.com/o2alexanderfedin/claude-config/blob/v${{ steps.version.outputs.tag_version }}/CHANGELOG.md) for detailed changes.
          EOF

      - name: Create GitHub Release
        uses: softprops/action-gh-release@v2
        with:
          body_path: RELEASE_NOTES.md
          files: |
            claude-config-${{ steps.version.outputs.tag_version }}.tar.gz
          draft: false
          prerelease: false
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}

      - name: Notify success
        run: |
          echo "✓ Release v${{ steps.version.outputs.tag_version }} published successfully!"
          echo "Installation: /plugin install o2alexanderfedin/claude-config"
```

#### 1.8 Create CHANGELOG.md (15 minutes)

**File:** `CHANGELOG.md`

```markdown
# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [0.2.0] - 2025-12-XX

### Added
- Plugin system support via `.claude-plugin/plugin.json`
- Marketplace manifest for plugin discovery
- GitHub Actions release automation
- Comprehensive installation documentation
- MIT License
- CHANGELOG.md for version tracking

### Changed
- Reorganized directory structure for plugin distribution
- Moved scripts from `scripts/gh-projects/` to `bin/gh-projects/`
- Updated README with multiple installation methods
- Enhanced documentation with plugin-specific instructions

### Fixed
- N/A

### Migration Guide
- Existing manual installations continue to work
- Plugin installation now recommended: `/plugin install o2alexanderfedin/claude-config`
- Scripts remain backward compatible

## [0.1.0] - 2025-12-XX

### Added
- Initial release with 11 GitHub Projects management scripts
- Native sub-issue API support
- Atomic draft→convert workflow
- Project templating and cloning capabilities
- Production-quality error handling and retry logic
- Comprehensive documentation

[0.2.0]: https://github.com/o2alexanderfedin/claude-config/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/o2alexanderfedin/claude-config/releases/tag/v0.1.0
```

### Testing Strategy - Phase 1

#### 1.9 Local Plugin Testing (30 minutes)

**Test Plan:**

1. **Validate Plugin Structure**
   ```bash
   # Validate JSON syntax
   jq empty .claude-plugin/plugin.json
   jq empty .claude-plugin/marketplace.json

   # Check required directories
   test -d bin/gh-projects || echo "ERROR: Missing bin/gh-projects"
   test -f bin/gh-projects/gh-project-init || echo "ERROR: Missing scripts"
   ```

2. **Test Local Plugin Installation**
   ```bash
   # Install from local path
   /plugin install /path/to/claude-config

   # Verify installation
   ls -la ~/.claude/plugins/cache/

   # Test script execution
   gh-project-init --help
   ```

3. **Test GitHub Installation** (after push to GitHub)
   ```bash
   # Uninstall local version
   /plugin uninstall claude-config

   # Install from GitHub
   /plugin install o2alexanderfedin/claude-config

   # Verify
   gh-project-init --help
   ```

4. **Test Backward Compatibility**
   ```bash
   # Manual installation still works
   git clone https://github.com/o2alexanderfedin/claude-config.git
   cp -r claude-config/bin/gh-projects ~/.claude/bin/

   # Scripts executable
   ~/.claude/bin/gh-projects/gh-project-init --help
   ```

#### 1.10 Integration Testing (15 minutes)

**Test Scenarios:**

1. **Fresh installation workflow**
   - Install plugin
   - Initialize configuration
   - Create test epic
   - Verify all scripts accessible

2. **Upgrade from manual installation**
   - Existing manual install in place
   - Install plugin
   - Verify no conflicts

3. **Cross-platform compatibility**
   - Test on macOS (primary)
   - Document Linux/WSL compatibility
   - Note Windows PowerShell considerations

### Security Considerations - Phase 1

#### 1.11 Security Audit (15 minutes)

**Checklist:**

- [ ] No API keys or credentials in repository
- [ ] .gitignore includes all sensitive patterns
- [ ] Scripts do not hardcode secrets
- [ ] GitHub Actions use secrets properly
- [ ] File permissions appropriate (scripts executable only)
- [ ] No arbitrary code execution vulnerabilities

**Actions:**

1. **Scan for secrets**
   ```bash
   # Use git-secrets or similar
   git secrets --scan

   # Manual grep for common patterns
   grep -r "ANTHROPIC_API_KEY" .
   grep -r "GITHUB_TOKEN" .
   ```

2. **Review .gitignore**
   - Ensure `.env`, `.env.*`, `*.key`, `*.pem` excluded
   - Add `secrets.json`, `credentials.*`

3. **Script security**
   - All scripts use `set -e` for error handling
   - Input validation on user-provided values
   - No eval of user input

### Rollout Strategy - Phase 1

#### 1.12 Release Execution (30 minutes)

**Steps:**

1. **Prepare release branch**
   ```bash
   git flow release start 0.2.0
   ```

2. **Complete all tasks**
   - Create all files listed above
   - Update README
   - Test locally
   - Security audit

3. **Update version references**
   ```bash
   # Ensure plugin.json version is 0.2.0
   jq '.version = "0.2.0"' .claude-plugin/plugin.json > tmp.json
   mv tmp.json .claude-plugin/plugin.json
   ```

4. **Commit and finish release**
   ```bash
   git add .
   git commit -m "feat: add plugin system support for v0.2.0

- Add .claude-plugin/plugin.json manifest
- Add .claude-plugin/marketplace.json
- Reorganize directory structure (scripts -> bin)
- Add GitHub Actions release automation
- Update README with installation methods
- Add LICENSE (MIT)
- Add CHANGELOG.md"

   git flow release finish 0.2.0
   ```

5. **Push and trigger release**
   ```bash
   git push origin develop
   git push origin main
   git push origin --tags

   # GitHub Actions will automatically:
   # - Validate plugin structure
   # - Create release archive
   # - Generate release notes
   # - Publish release
   ```

6. **Verify release**
   - Check GitHub Releases page
   - Test plugin installation: `/plugin install o2alexanderfedin/claude-config`
   - Verify scripts work

7. **Announce**
   - Update repository description
   - Share in Claude Code community
   - Document in project wiki

### Success Criteria - Phase 1

**Must Have:**
- [ ] Plugin installs successfully via `/plugin install o2alexanderfedin/claude-config`
- [ ] All 11 scripts accessible and functional
- [ ] Backward compatibility maintained (manual install still works)
- [ ] README includes all installation methods
- [ ] GitHub release automated and successful
- [ ] No security issues identified

**Nice to Have:**
- [ ] Marketplace listing prepared (submission in future phase)
- [ ] Community feedback gathered
- [ ] Usage analytics implemented

### Dependencies - Phase 1

**Required:**
- Git repository access
- GitHub account with push permissions
- Local Claude Code installation for testing

**Optional:**
- Claude Code community access for announcement
- Multiple test environments (macOS, Linux)

### Risks and Mitigation - Phase 1

| Risk | Impact | Probability | Mitigation |
|------|--------|-------------|------------|
| Plugin system API changes | High | Low | Monitor Claude Code releases, maintain manual install option |
| Version mismatch between tag and plugin.json | Medium | Medium | Automated validation in GitHub Actions |
| Breaking changes to existing users | High | Low | Maintain backward compatibility, symlinks |
| Installation conflicts | Medium | Low | Comprehensive testing, clear documentation |

---

## Phase 2: Bootstrap Installer (v0.3.0)

**Timeline:** 4-6 hours
**Impact:** MEDIUM - Simplifies team onboarding and CI/CD
**Effort:** MEDIUM - Requires cross-platform testing
**Value:** Automated deployment, zero-knowledge installation

### Objectives

Create a production-quality bootstrap installer that handles:
- Prerequisites checking and installation
- Multi-method installation (plugin, manual, hybrid)
- Version selection and updates
- Cross-platform compatibility
- Team onboarding automation

### Tasks

#### 2.1 Create Bootstrap Installer Script (2 hours)

**File:** `install.sh`

```bash
#!/bin/bash
# Claude Code Configuration Installer
# Version: 0.3.0
# Usage: curl -fsSL https://raw.githubusercontent.com/o2alexanderfedin/claude-config/main/install.sh | bash
#        Or: ./install.sh [version]

set -e

# Configuration
REPO_URL="https://github.com/o2alexanderfedin/claude-config.git"
INSTALL_DIR="$HOME/.claude-config-source"
VERSION="${1:-latest}"
INSTALL_METHOD="${INSTALL_METHOD:-auto}"  # auto, plugin, manual

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Logging functions
info() { echo -e "${GREEN}[INFO]${NC} $1"; }
warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
error() { echo -e "${RED}[ERROR]${NC} $1"; }
debug() { [ "${DEBUG:-0}" = "1" ] && echo -e "${BLUE}[DEBUG]${NC} $1" || true; }

# Platform detection
detect_platform() {
    case "$(uname -s)" in
        Darwin*)
            PLATFORM="macos"
            SHELL_RC="$HOME/.zshrc"
            ;;
        Linux*)
            PLATFORM="linux"
            if [ -f "$HOME/.bashrc" ]; then
                SHELL_RC="$HOME/.bashrc"
            elif [ -f "$HOME/.zshrc" ]; then
                SHELL_RC="$HOME/.zshrc"
            else
                SHELL_RC="$HOME/.profile"
            fi
            ;;
        MINGW*|MSYS*|CYGWIN*)
            PLATFORM="windows"
            SHELL_RC="$HOME/.bashrc"  # Git Bash
            ;;
        *)
            PLATFORM="unknown"
            warn "Unknown platform: $(uname -s)"
            SHELL_RC="$HOME/.profile"
            ;;
    esac

    info "Detected platform: $PLATFORM"
    debug "Shell RC: $SHELL_RC"
}

# Check if command exists
command_exists() {
    command -v "$1" >/dev/null 2>&1
}

# Check prerequisites
check_prerequisites() {
    info "Checking prerequisites..."

    local missing_required=()
    local missing_optional=()

    # Required
    if ! command_exists git; then
        missing_required+=("git")
    fi

    if ! command_exists jq; then
        missing_required+=("jq")
    fi

    # Optional
    if ! command_exists gh; then
        missing_optional+=("gh (GitHub CLI - required for gh-projects scripts)")
    fi

    if ! command_exists git-flow; then
        missing_optional+=("git-flow (optional, for release workflows)")
    fi

    # Report missing required dependencies
    if [ ${#missing_required[@]} -gt 0 ]; then
        error "Missing required dependencies: ${missing_required[*]}"
        echo ""
        echo "Installation instructions:"

        case $PLATFORM in
            macos)
                echo "  brew install git jq"
                ;;
            linux)
                echo "  sudo apt-get install git jq  # Debian/Ubuntu"
                echo "  sudo yum install git jq      # RHEL/CentOS"
                ;;
            windows)
                echo "  Use Git Bash or WSL"
                echo "  Install jq from https://stedolan.github.io/jq/"
                ;;
        esac

        exit 1
    fi

    # Report missing optional dependencies
    if [ ${#missing_optional[@]} -gt 0 ]; then
        warn "Missing optional dependencies: ${missing_optional[*]}"
        echo ""
        echo "Installation instructions:"

        case $PLATFORM in
            macos)
                echo "  brew install gh git-flow"
                ;;
            linux)
                echo "  # GitHub CLI"
                echo "  curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg | sudo dd of=/usr/share/keyrings/githubcli-archive-keyring.gpg"
                echo "  echo 'deb [signed-by=/usr/share/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main' | sudo tee /etc/apt/sources.list.d/github-cli.list"
                echo "  sudo apt update && sudo apt install gh"
                echo ""
                echo "  # git-flow"
                echo "  sudo apt-get install git-flow  # Debian/Ubuntu"
                ;;
            windows)
                echo "  # Install GitHub CLI from https://cli.github.com/"
                echo "  # git-flow available via Git Bash package managers"
                ;;
        esac

        echo ""
        read -p "Continue without optional dependencies? [y/N] " -n 1 -r
        echo
        if [[ ! $REPLY =~ ^[Yy]$ ]]; then
            exit 1
        fi
    fi

    info "Prerequisites check complete"
}

# Detect Claude Code installation
detect_claude_code() {
    if [ -d "$HOME/.claude" ]; then
        info "Claude Code installation detected: $HOME/.claude"
        CLAUDE_INSTALLED=1

        # Check if plugin system available
        if [ -d "$HOME/.claude/plugins" ]; then
            info "Plugin system available"
            PLUGIN_AVAILABLE=1
        else
            warn "Plugin system not available (may need Claude Code update)"
            PLUGIN_AVAILABLE=0
        fi
    else
        warn "Claude Code installation not found at $HOME/.claude"
        warn "You can still install scripts for future use"
        CLAUDE_INSTALLED=0
        PLUGIN_AVAILABLE=0
    fi
}

# Determine installation method
determine_install_method() {
    if [ "$INSTALL_METHOD" != "auto" ]; then
        info "Installation method specified: $INSTALL_METHOD"
        return
    fi

    if [ $PLUGIN_AVAILABLE -eq 1 ]; then
        INSTALL_METHOD="plugin"
        info "Using plugin installation (recommended)"
    else
        INSTALL_METHOD="manual"
        info "Using manual installation (plugin system not available)"
    fi
}

# Backup existing configuration
backup_existing() {
    local backup_needed=0

    if [ -d "$HOME/.claude/bin/gh-projects" ]; then
        backup_needed=1
    fi

    if [ $backup_needed -eq 1 ]; then
        BACKUP_DIR="$HOME/.claude.backup.$(date +%Y%m%d_%H%M%S)"
        info "Backing up existing configuration to $BACKUP_DIR"
        mkdir -p "$BACKUP_DIR"

        [ -d "$HOME/.claude/bin" ] && cp -r "$HOME/.claude/bin" "$BACKUP_DIR/"

        info "Backup complete"
    fi
}

# Clone or update repository
setup_repository() {
    info "Setting up repository..."

    if [ -d "$INSTALL_DIR" ]; then
        info "Updating existing repository at $INSTALL_DIR"
        cd "$INSTALL_DIR"
        git fetch origin

        if [ "$VERSION" = "latest" ]; then
            git checkout main
            git pull origin main
        else
            git checkout "$VERSION"
        fi
    else
        info "Cloning repository to $INSTALL_DIR"
        git clone "$REPO_URL" "$INSTALL_DIR"
        cd "$INSTALL_DIR"

        if [ "$VERSION" != "latest" ]; then
            git checkout "$VERSION"
        fi
    fi

    ACTUAL_VERSION=$(git describe --tags --always)
    info "Repository version: $ACTUAL_VERSION"
}

# Install via plugin system
install_plugin() {
    info "Installing via Claude Code plugin system..."

    # Note: This would require Claude Code CLI to be invoked
    # For now, provide instructions

    echo ""
    echo "To install as a plugin, run this command in Claude Code:"
    echo ""
    echo "  /plugin install o2alexanderfedin/claude-config"
    echo ""

    read -p "Press Enter after installing plugin, or Ctrl+C to exit..."
}

# Install manually
install_manual() {
    info "Installing manually to $HOME/.claude/..."

    # Create directories
    mkdir -p "$HOME/.claude/bin"

    # Install scripts
    if [ -d "$INSTALL_DIR/bin/gh-projects" ]; then
        info "Installing GitHub Projects scripts..."
        cp -r "$INSTALL_DIR/bin/gh-projects" "$HOME/.claude/bin/"

        # Make executable
        find "$HOME/.claude/bin/gh-projects" -type f -exec chmod +x {} \;

        info "Scripts installed to $HOME/.claude/bin/gh-projects"
    fi

    # Install skills (when available)
    if [ -d "$INSTALL_DIR/skills" ] && [ -n "$(ls -A "$INSTALL_DIR/skills")" ]; then
        mkdir -p "$HOME/.claude/skills"
        cp -r "$INSTALL_DIR/skills"/* "$HOME/.claude/skills/"
        info "Skills installed to $HOME/.claude/skills"
    fi

    # Install commands (when available)
    if [ -d "$INSTALL_DIR/commands" ] && [ -n "$(ls -A "$INSTALL_DIR/commands")" ]; then
        mkdir -p "$HOME/.claude/commands"
        cp -r "$INSTALL_DIR/commands"/* "$HOME/.claude/commands/"
        info "Commands installed to $HOME/.claude/commands"
    fi
}

# Update PATH
update_path() {
    if ! grep -q ".claude/bin/gh-projects" "$SHELL_RC" 2>/dev/null; then
        info "Adding scripts to PATH in $SHELL_RC"

        echo "" >> "$SHELL_RC"
        echo "# Claude Code GitHub Projects scripts" >> "$SHELL_RC"
        echo 'export PATH="$PATH:$HOME/.claude/bin/gh-projects"' >> "$SHELL_RC"

        info "PATH updated. Run: source $SHELL_RC"
    else
        debug "PATH already includes .claude/bin/gh-projects"
    fi
}

# Verify installation
verify_installation() {
    info "Verifying installation..."

    local errors=0

    # Check scripts
    if [ "$INSTALL_METHOD" = "manual" ]; then
        if [ ! -f "$HOME/.claude/bin/gh-projects/gh-project-init" ]; then
            error "Script not found: gh-project-init"
            ((errors++))
        fi

        if [ ! -x "$HOME/.claude/bin/gh-projects/gh-project-init" ]; then
            error "Script not executable: gh-project-init"
            ((errors++))
        fi
    fi

    if [ $errors -eq 0 ]; then
        info "Installation verified successfully"
    else
        error "Installation verification failed with $errors errors"
        return 1
    fi
}

# Print next steps
print_next_steps() {
    echo ""
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    info "Installation Complete!"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo ""

    if [ "$INSTALL_METHOD" = "manual" ]; then
        echo "Next steps:"
        echo ""
        echo "  1. Reload your shell:"
        echo "     source $SHELL_RC"
        echo ""
        echo "  2. Verify installation:"
        echo "     gh-project-init --help"
        echo ""
    fi

    echo "  3. Initialize configuration:"
    echo "     gh-project-init --project YOUR_PROJECT_NUMBER"
    echo ""
    echo "  4. Link project to repository:"
    echo "     gh-project-link-repo --project YOUR_PROJECT_NUMBER"
    echo ""
    echo "  5. Read the documentation:"
    echo "     $HOME/.claude/bin/gh-projects/README.md"
    echo ""
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
}

# Main installation process
main() {
    echo ""
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    info "Claude Code Configuration Installer v0.3.0"
    echo "━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━"
    echo ""

    detect_platform
    check_prerequisites
    detect_claude_code
    determine_install_method
    backup_existing
    setup_repository

    case $INSTALL_METHOD in
        plugin)
            install_plugin
            ;;
        manual)
            install_manual
            update_path
            ;;
        *)
            error "Unknown installation method: $INSTALL_METHOD"
            exit 1
            ;;
    esac

    verify_installation
    print_next_steps
}

# Run installation
main "$@"
```

#### 2.2 Create Uninstaller Script (30 minutes)

**File:** `uninstall.sh`

```bash
#!/bin/bash
# Claude Code Configuration Uninstaller
# Version: 0.3.0

set -e

# Colors
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

info() { echo -e "${GREEN}[INFO]${NC} $1"; }
warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
error() { echo -e "${RED}[ERROR]${NC} $1"; }

# Confirm uninstallation
confirm_uninstall() {
    echo ""
    warn "This will remove Claude Code configuration:"
    echo "  - $HOME/.claude/bin/gh-projects/"
    echo "  - $HOME/.claude/skills/* (if from this plugin)"
    echo "  - $HOME/.claude/commands/* (if from this plugin)"
    echo ""

    read -p "Are you sure you want to uninstall? [y/N] " -n 1 -r
    echo

    if [[ ! $REPLY =~ ^[Yy]$ ]]; then
        info "Uninstall cancelled"
        exit 0
    fi
}

# Remove files
remove_files() {
    info "Removing installed files..."

    if [ -d "$HOME/.claude/bin/gh-projects" ]; then
        rm -rf "$HOME/.claude/bin/gh-projects"
        info "Removed $HOME/.claude/bin/gh-projects"
    fi

    # Note: Only remove skills/commands if they're from this plugin
    # For now, leave them (safer)

    info "Files removed"
}

# Clean PATH
clean_path() {
    for rc in "$HOME/.zshrc" "$HOME/.bashrc" "$HOME/.profile"; do
        if [ -f "$rc" ]; then
            if grep -q ".claude/bin/gh-projects" "$rc"; then
                info "Cleaning PATH from $rc"

                # Create backup
                cp "$rc" "$rc.backup.$(date +%Y%m%d_%H%M%S)"

                # Remove line
                grep -v ".claude/bin/gh-projects" "$rc" > "$rc.tmp"
                mv "$rc.tmp" "$rc"
            fi
        fi
    done
}

# Main
main() {
    confirm_uninstall
    remove_files
    clean_path

    echo ""
    info "Uninstallation complete!"
    echo "Reload your shell: source ~/.zshrc (or ~/.bashrc)"
}

main "$@"
```

#### 2.3 Create Update Script (30 minutes)

**File:** `update.sh`

```bash
#!/bin/bash
# Claude Code Configuration Updater
# Version: 0.3.0

set -e

INSTALL_DIR="$HOME/.claude-config-source"

# Colors
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

info() { echo -e "${GREEN}[INFO]${NC} $1"; }
warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }

# Check if installed
if [ ! -d "$INSTALL_DIR" ]; then
    warn "Configuration not found at $INSTALL_DIR"
    echo "Run install.sh first"
    exit 1
fi

# Update repository
info "Updating repository..."
cd "$INSTALL_DIR"
git fetch origin
git pull origin main

# Get version
VERSION=$(git describe --tags --always)
info "Updated to version: $VERSION"

# Re-install
info "Re-installing..."
./install.sh latest

info "Update complete!"
```

#### 2.4 Add Installation Tests (1 hour)

**File:** `tests/test-install.sh`

```bash
#!/bin/bash
# Installation test suite

set -e

# Test functions
test_prerequisites() {
    echo "Testing prerequisites check..."
    # TODO: Mock missing dependencies
}

test_platform_detection() {
    echo "Testing platform detection..."
    # TODO: Verify platform detected correctly
}

test_manual_install() {
    echo "Testing manual installation..."
    # TODO: Install to temp directory, verify files
}

test_update() {
    echo "Testing update process..."
    # TODO: Install old version, update, verify
}

test_uninstall() {
    echo "Testing uninstall..."
    # TODO: Install, uninstall, verify cleanup
}

# Run all tests
main() {
    echo "Running installation tests..."

    test_prerequisites
    test_platform_detection
    test_manual_install
    test_update
    test_uninstall

    echo "All tests passed!"
}

main "$@"
```

#### 2.5 Update README with Bootstrap Instructions (30 minutes)

Add to README.md:

```markdown
## Quick Installation

### One-Command Install (Recommended)

```bash
curl -fsSL https://raw.githubusercontent.com/o2alexanderfedin/claude-config/main/install.sh | bash
```

This installer will:
- Check prerequisites (git, jq, gh)
- Detect your platform (macOS, Linux, Windows)
- Choose optimal installation method (plugin or manual)
- Install scripts to `~/.claude/bin/gh-projects/`
- Update your PATH automatically

### Installation Options

```bash
# Install specific version
curl -fsSL https://raw.githubusercontent.com/o2alexanderfedin/claude-config/main/install.sh | bash -s v0.3.0

# Force manual installation (skip plugin)
INSTALL_METHOD=manual curl -fsSL ... | bash

# Enable debug output
DEBUG=1 curl -fsSL ... | bash
```

### Update

```bash
curl -fsSL https://raw.githubusercontent.com/o2alexanderfedin/claude-config/main/update.sh | bash
```

### Uninstall

```bash
curl -fsSL https://raw.githubusercontent.com/o2alexanderfedin/claude-config/main/uninstall.sh | bash
```
```

### Testing Strategy - Phase 2

#### 2.6 Cross-Platform Testing (2 hours)

**Test Environments:**

1. **macOS** (primary development)
   - Test with Homebrew dependencies
   - Test with zsh
   - Test both Intel and Apple Silicon

2. **Linux Ubuntu/Debian**
   - Test with apt dependencies
   - Test with bash
   - Test WSL2

3. **Windows Git Bash**
   - Test with Git for Windows
   - Test with bash
   - Document limitations

**Test Matrix:**

| Platform | Shell | Dependencies | Plugin | Manual | Result |
|----------|-------|--------------|--------|--------|--------|
| macOS 14 | zsh | brew | ✓ | ✓ | PASS |
| macOS 13 | bash | brew | ✓ | ✓ | PASS |
| Ubuntu 22.04 | bash | apt | ✓ | ✓ | PASS |
| Ubuntu 20.04 | bash | apt | ✓ | ✓ | PASS |
| WSL2 Ubuntu | bash | apt | ✓ | ✓ | PASS |
| Windows Git Bash | bash | manual | - | ✓ | PASS |

#### 2.7 CI/CD Integration Testing (1 hour)

**GitHub Actions Test Workflow:**

**File:** `.github/workflows/test-install.yml`

```yaml
name: Test Installation

on:
  push:
    branches: [main, develop]
  pull_request:
    branches: [main, develop]

jobs:
  test-install:
    strategy:
      matrix:
        os: [ubuntu-latest, macos-latest]
        include:
          - os: ubuntu-latest
            shell: bash
          - os: macos-latest
            shell: zsh

    runs-on: ${{ matrix.os }}

    steps:
      - uses: actions/checkout@v4

      - name: Install prerequisites
        run: |
          if [ "$RUNNER_OS" = "macOS" ]; then
            brew install jq
          else
            sudo apt-get update
            sudo apt-get install -y jq
          fi

      - name: Test installer
        run: |
          bash install.sh latest

      - name: Verify installation
        run: |
          test -f ~/.claude/bin/gh-projects/gh-project-init
          test -x ~/.claude/bin/gh-projects/gh-project-init

      - name: Test help
        run: |
          ~/.claude/bin/gh-projects/gh-project-init --help

      - name: Test uninstaller
        run: |
          bash uninstall.sh <<< "y"

      - name: Verify cleanup
        run: |
          test ! -d ~/.claude/bin/gh-projects
```

### Security Considerations - Phase 2

#### 2.8 Installer Security Audit (30 minutes)

**Security Checklist:**

- [ ] Installer uses `set -e` for error handling
- [ ] No eval of user input
- [ ] Downloads verify checksums (future enhancement)
- [ ] HTTPS only for downloads
- [ ] Backup before overwriting
- [ ] No sudo/root requirements
- [ ] Clear error messages
- [ ] Idempotent (safe to run multiple times)

**Pipe-to-bash Security:**

Document risks and alternatives:

```markdown
### Security Note: Pipe to Bash

The one-command install uses "pipe to bash" which has security implications:

**Risks:**
- Downloads and executes script without review
- MITM attacks possible (mitigated by HTTPS)
- No verification of script integrity

**Safer Alternative:**

```bash
# Download, review, then execute
curl -fsSL https://raw.githubusercontent.com/o2alexanderfedin/claude-config/main/install.sh > install.sh
less install.sh  # Review the script
chmod +x install.sh
./install.sh
```

**Future Enhancement:** Add checksum verification
```

### Rollout Strategy - Phase 2

#### 2.9 Phase 2 Release (1 hour)

**Release Steps:**

1. **Create release branch**
   ```bash
   git flow release start 0.3.0
   ```

2. **Complete Phase 2 tasks**
   - Create install.sh, uninstall.sh, update.sh
   - Add tests
   - Update README
   - Cross-platform testing

3. **Update CHANGELOG.md**
   ```markdown
   ## [0.3.0] - 2025-12-XX

   ### Added
   - Bootstrap installer script (install.sh)
   - Uninstaller script (uninstall.sh)
   - Update script (update.sh)
   - Cross-platform support (macOS, Linux, Windows Git Bash)
   - Automated PATH configuration
   - Installation tests

   ### Changed
   - Enhanced README with one-command installation
   - Improved documentation for multiple installation methods

   ### Fixed
   - N/A
   ```

4. **Update plugin.json version**
   ```bash
   jq '.version = "0.3.0"' .claude-plugin/plugin.json > tmp.json
   mv tmp.json .claude-plugin/plugin.json
   ```

5. **Commit and release**
   ```bash
   git add .
   git commit -m "feat: add bootstrap installer for v0.3.0

- Add install.sh with cross-platform support
- Add uninstall.sh and update.sh
- Add installation tests
- Improve documentation"

   git flow release finish 0.3.0
   git push origin develop main --tags
   ```

### Success Criteria - Phase 2

**Must Have:**
- [ ] One-command installation works on macOS, Linux, WSL
- [ ] Installer detects and reports missing prerequisites
- [ ] Backup created before overwriting
- [ ] PATH updated automatically
- [ ] Uninstaller removes all files
- [ ] Update script works correctly
- [ ] Documentation complete

**Nice to Have:**
- [ ] Windows Git Bash support
- [ ] Checksum verification
- [ ] Installation analytics

---

## Phase 3: Container Images (v0.4.0)

**Timeline:** 8-10 hours
**Impact:** MEDIUM - Valuable for CI/CD and container-first teams
**Effort:** HIGH - Requires Docker expertise and multi-arch builds
**Value:** Enterprise-ready deployment, reproducible environments

### Objectives

Create production-quality Docker images with:
- Pre-installed claude-config
- Multi-architecture support (amd64, arm64)
- GitHub Container Registry publishing
- CI/CD integration examples
- Development container support

### Tasks

#### 3.1 Create Dockerfile (2 hours)

**File:** `Dockerfile`

```dockerfile
# Multi-stage build for Claude Code with claude-config
# Supports: amd64, arm64

# Stage 1: Base image with system dependencies
FROM node:18-bookworm-slim AS base

# Install system dependencies
RUN apt-get update && apt-get install -y \
    git \
    curl \
    jq \
    ca-certificates \
    gnupg \
    && rm -rf /var/lib/apt/lists/*

# Install GitHub CLI
RUN curl -fsSL https://cli.github.com/packages/githubcli-archive-keyring.gpg | \
    dd of=/usr/share/keyrings/githubcli-archive-keyring.gpg && \
    chmod go+r /usr/share/keyrings/githubcli-archive-keyring.gpg && \
    echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/githubcli-archive-keyring.gpg] https://cli.github.com/packages stable main" | \
    tee /etc/apt/sources.list.d/github-cli.list && \
    apt-get update && \
    apt-get install -y gh && \
    rm -rf /var/lib/apt/lists/*

# Install git-flow (optional)
RUN apt-get update && apt-get install -y git-flow && \
    rm -rf /var/lib/apt/lists/*

# Stage 2: Claude Code installation
FROM base AS claude-code

# Install Claude Code globally
RUN npm install -g @anthropic-ai/claude-code

# Create non-root user
RUN useradd -m -s /bin/bash claude && \
    mkdir -p /home/claude/.claude && \
    chown -R claude:claude /home/claude

# Switch to claude user
USER claude
WORKDIR /home/claude

# Stage 3: claude-config installation
FROM claude-code AS final

# Copy claude-config repository
COPY --chown=claude:claude . /tmp/claude-config/

# Install claude-config
RUN mkdir -p /home/claude/.claude/bin && \
    cp -r /tmp/claude-config/bin/gh-projects /home/claude/.claude/bin/ && \
    find /home/claude/.claude/bin/gh-projects -type f -exec chmod +x {} \; && \
    rm -rf /tmp/claude-config

# Set environment variables
ENV PATH="/home/claude/.claude/bin/gh-projects:${PATH}"
ENV CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=true

# Create workspace directory
RUN mkdir -p /workspace
WORKDIR /workspace

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \
    CMD gh-project-init --help || exit 1

# Default command
ENTRYPOINT ["claude"]
CMD ["--help"]
```

#### 3.2 Create Docker Compose Configuration (1 hour)

**File:** `docker-compose.yml`

```yaml
version: '3.8'

services:
  claude-config:
    build:
      context: .
      dockerfile: Dockerfile
    image: ghcr.io/o2alexanderfedin/claude-config:latest
    container_name: claude-config

    # Environment variables
    environment:
      - ANTHROPIC_API_KEY=${ANTHROPIC_API_KEY}
      - GITHUB_TOKEN=${GITHUB_TOKEN}
      - CLAUDE_CODE_DISABLE_NONESSENTIAL_TRAFFIC=true

    # Volumes
    volumes:
      # Mount workspace
      - ./:/workspace:rw

      # Persistent Claude credentials
      - claude-credentials:/home/claude/.claude-credentials:rw

      # Optional: Mount global config (read-only)
      # - ~/.claude:/home/claude/.claude-global:ro

    # Working directory
    working_dir: /workspace

    # Interactive terminal
    stdin_open: true
    tty: true

    # Command (can be overridden)
    command: ["bash"]

  # Example: Development database
  postgres:
    image: postgres:15-alpine
    container_name: claude-config-db
    environment:
      POSTGRES_DB: myapp
      POSTGRES_USER: dev
      POSTGRES_PASSWORD: dev
    volumes:
      - postgres-data:/var/lib/postgresql/data
    ports:
      - "5432:5432"

volumes:
  claude-credentials:
    driver: local
  postgres-data:
    driver: local
```

#### 3.3 Create DevContainer Configuration (1 hour)

**File:** `.devcontainer/devcontainer.json`

```json
{
  "name": "Claude Code with claude-config",
  "build": {
    "dockerfile": "../Dockerfile",
    "context": ".."
  },

  "features": {
    "ghcr.io/devcontainers/features/docker-in-docker:2": {},
    "ghcr.io/devcontainers/features/git:1": {}
  },

  "customizations": {
    "vscode": {
      "extensions": [
        "anthropic.claude-code",
        "github.vscode-pull-request-github",
        "eamodio.gitlens"
      ],
      "settings": {
        "terminal.integrated.defaultProfile.linux": "bash"
      }
    }
  },

  "mounts": [
    "source=${localEnv:HOME}/.claude,target=/home/claude/.claude-global,type=bind,consistency=cached,readonly",
    "source=claude-config-credentials,target=/home/claude/.claude-credentials,type=volume"
  ],

  "remoteEnv": {
    "ANTHROPIC_API_KEY": "${localEnv:ANTHROPIC_API_KEY}",
    "GITHUB_TOKEN": "${localEnv:GITHUB_TOKEN}"
  },

  "postCreateCommand": "gh-project-init --help",

  "remoteUser": "claude"
}
```

#### 3.4 Create Multi-Arch Build Workflow (2 hours)

**File:** `.github/workflows/docker-build.yml`

```yaml
name: Build and Publish Docker Images

on:
  push:
    tags:
      - 'v*'
    branches:
      - main
      - develop
  pull_request:
    branches:
      - main

env:
  REGISTRY: ghcr.io
  IMAGE_NAME: ${{ github.repository }}

permissions:
  contents: read
  packages: write

jobs:
  build-and-push:
    runs-on: ubuntu-latest

    steps:
      - name: Checkout repository
        uses: actions/checkout@v4

      - name: Set up QEMU
        uses: docker/setup-qemu-action@v3

      - name: Set up Docker Buildx
        uses: docker/setup-buildx-action@v3

      - name: Log in to Container Registry
        uses: docker/login-action@v3
        with:
          registry: ${{ env.REGISTRY }}
          username: ${{ github.actor }}
          password: ${{ secrets.GITHUB_TOKEN }}

      - name: Extract metadata
        id: meta
        uses: docker/metadata-action@v5
        with:
          images: ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}
          tags: |
            # Version tags
            type=semver,pattern={{version}}
            type=semver,pattern={{major}}.{{minor}}
            type=semver,pattern={{major}}

            # Branch tags
            type=ref,event=branch

            # PR tags
            type=ref,event=pr

            # Latest tag
            type=raw,value=latest,enable={{is_default_branch}}

      - name: Build and push
        uses: docker/build-push-action@v5
        with:
          context: .
          platforms: linux/amd64,linux/arm64
          push: ${{ github.event_name != 'pull_request' }}
          tags: ${{ steps.meta.outputs.tags }}
          labels: ${{ steps.meta.outputs.labels }}
          cache-from: type=gha
          cache-to: type=gha,mode=max

      - name: Verify image
        if: github.event_name != 'pull_request'
        run: |
          docker pull ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:latest
          docker run --rm ${{ env.REGISTRY }}/${{ env.IMAGE_NAME }}:latest gh-project-init --help
```

#### 3.5 Create Container Usage Documentation (2 hours)

**File:** `docs/CONTAINER_GUIDE.md`

```markdown
# Container Guide

Complete guide to using claude-config in containerized environments.

## Docker Images

### Available Images

**GitHub Container Registry:**
- `ghcr.io/o2alexanderfedin/claude-config:latest` - Latest main branch
- `ghcr.io/o2alexanderfedin/claude-config:0.4.0` - Specific version
- `ghcr.io/o2alexanderfedin/claude-config:develop` - Development branch

**Architectures:**
- `linux/amd64` - Intel/AMD 64-bit
- `linux/arm64` - ARM 64-bit (Apple Silicon, AWS Graviton)

### Quick Start

```bash
# Pull image
docker pull ghcr.io/o2alexanderfedin/claude-config:latest

# Run interactive shell
docker run -it --rm \
  -e ANTHROPIC_API_KEY=$ANTHROPIC_API_KEY \
  -e GITHUB_TOKEN=$GITHUB_TOKEN \
  -v $(pwd):/workspace \
  ghcr.io/o2alexanderfedin/claude-config:latest \
  bash

# Run specific command
docker run --rm \
  -e ANTHROPIC_API_KEY=$ANTHROPIC_API_KEY \
  -v $(pwd):/workspace \
  ghcr.io/o2alexanderfedin/claude-config:latest \
  gh-project-init --help
```

## Docker Compose

### Development Setup

```yaml
version: '3.8'

services:
  claude:
    image: ghcr.io/o2alexanderfedin/claude-config:latest
    environment:
      - ANTHROPIC_API_KEY=${ANTHROPIC_API_KEY}
      - GITHUB_TOKEN=${GITHUB_TOKEN}
    volumes:
      - ./:/workspace
      - claude-creds:/home/claude/.claude-credentials
    working_dir: /workspace
    command: bash
    stdin_open: true
    tty: true

volumes:
  claude-creds:
```

**Usage:**
```bash
# Start services
docker-compose up -d

# Enter container
docker-compose exec claude bash

# Initialize project
docker-compose exec claude gh-project-init --project 14

# Stop services
docker-compose down
```

## DevContainers (VS Code)

### Setup

1. Install VS Code extension: "Dev Containers"
2. Open project in VS Code
3. Command Palette → "Dev Containers: Reopen in Container"
4. VS Code rebuilds container and opens inside

### Features

- Pre-installed claude-config scripts
- GitHub CLI authenticated
- Git configured
- Persistent credentials
- Integrated terminal

### Configuration

See `.devcontainer/devcontainer.json` for customization.

## CI/CD Integration

### GitHub Actions

```yaml
name: GitHub Projects Automation

on:
  push:
    branches: [main]

jobs:
  update-project:
    runs-on: ubuntu-latest

    container:
      image: ghcr.io/o2alexanderfedin/claude-config:latest
      credentials:
        username: ${{ github.actor }}
        password: ${{ secrets.GITHUB_TOKEN }}

    steps:
      - uses: actions/checkout@v4

      - name: Initialize project
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
        run: |
          gh-project-init --project 14

      - name: Create issue from commit
        env:
          GITHUB_TOKEN: ${{ secrets.GITHUB_TOKEN }}
        run: |
          COMMIT_MSG=$(git log -1 --pretty=%B)
          gh-project-create --title "Story: $COMMIT_MSG" --type story
```

### GitLab CI

```yaml
docker-build:
  image: ghcr.io/o2alexanderfedin/claude-config:latest

  variables:
    GITHUB_TOKEN: $CI_GITHUB_TOKEN

  script:
    - gh-project-init --project 14
    - gh-project-list --type epic
```

## Security Best Practices

### API Keys

**Never hardcode API keys in Dockerfiles or docker-compose.yml**

**Recommended approaches:**

1. **Environment variables (development)**
   ```bash
   docker run --rm \
     -e ANTHROPIC_API_KEY=$ANTHROPIC_API_KEY \
     ghcr.io/o2alexanderfedin/claude-config:latest
   ```

2. **Docker secrets (production)**
   ```yaml
   secrets:
     anthropic_key:
       external: true

   services:
     claude:
       secrets:
         - anthropic_key
       environment:
         ANTHROPIC_API_KEY_FILE: /run/secrets/anthropic_key
   ```

3. **Kubernetes secrets**
   ```yaml
   apiVersion: v1
   kind: Secret
   metadata:
     name: claude-credentials
   type: Opaque
   data:
     api-key: <base64-encoded>
   ```

### Network Security

Container has minimal network access:
- HTTPS only
- GitHub API (api.github.com)
- Anthropic API (api.anthropic.com)
- DNS resolution

### File Permissions

- Runs as non-root user `claude`
- Workspace mounted with user permissions
- Credentials stored in dedicated volume

## Troubleshooting

### Permission Denied

**Problem:** Cannot write to workspace

**Solution:** Check volume mount permissions
```bash
docker run --rm \
  -v $(pwd):/workspace:rw \
  --user $(id -u):$(id -g) \
  ghcr.io/o2alexanderfedin/claude-config:latest
```

### Credentials Not Persisting

**Problem:** API key required every run

**Solution:** Use named volume for credentials
```bash
docker volume create claude-creds

docker run --rm \
  -v claude-creds:/home/claude/.claude-credentials \
  ghcr.io/o2alexanderfedin/claude-config:latest
```

### Multi-arch Issues

**Problem:** Wrong architecture pulled

**Solution:** Specify platform explicitly
```bash
docker pull --platform linux/amd64 ghcr.io/o2alexanderfedin/claude-config:latest
```

## Advanced Usage

### Custom Base Image

```dockerfile
FROM ghcr.io/o2alexanderfedin/claude-config:latest

# Add your customizations
RUN apt-get update && apt-get install -y python3-pip
COPY requirements.txt /tmp/
RUN pip3 install -r /tmp/requirements.txt

# Add custom scripts
COPY my-scripts/ /home/claude/.claude/bin/
```

### Multi-Project Workflow

```bash
# Project A
docker run --rm \
  -v ~/projects/project-a:/workspace \
  -v project-a-creds:/home/claude/.claude-credentials \
  ghcr.io/o2alexanderfedin/claude-config:latest

# Project B (separate credentials)
docker run --rm \
  -v ~/projects/project-b:/workspace \
  -v project-b-creds:/home/claude/.claude-credentials \
  ghcr.io/o2alexanderfedin/claude-config:latest
```

### Kubernetes Deployment

```yaml
apiVersion: apps/v1
kind: Deployment
metadata:
  name: claude-config
spec:
  replicas: 1
  selector:
    matchLabels:
      app: claude-config
  template:
    metadata:
      labels:
        app: claude-config
    spec:
      containers:
      - name: claude
        image: ghcr.io/o2alexanderfedin/claude-config:latest
        env:
        - name: ANTHROPIC_API_KEY
          valueFrom:
            secretKeyRef:
              name: claude-credentials
              key: api-key
        - name: GITHUB_TOKEN
          valueFrom:
            secretKeyRef:
              name: claude-credentials
              key: github-token
        volumeMounts:
        - name: workspace
          mountPath: /workspace
      volumes:
      - name: workspace
        persistentVolumeClaim:
          claimName: claude-workspace
```

## References

- [Official Claude Code Docker Support](https://docs.docker.com/ai/sandboxes/claude-code/)
- [GitHub Container Registry Docs](https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-container-registry)
- [DevContainers Specification](https://containers.dev/)
```

#### 3.6 Add Container Tests (2 hours)

**File:** `tests/test-docker.sh`

```bash
#!/bin/bash
# Docker image test suite

set -e

IMAGE="ghcr.io/o2alexanderfedin/claude-config:latest"

info() { echo "[INFO] $1"; }
error() { echo "[ERROR] $1"; exit 1; }

# Test 1: Image builds successfully
test_build() {
    info "Testing image build..."
    docker build -t $IMAGE . || error "Build failed"
    info "✓ Build successful"
}

# Test 2: Scripts are installed
test_scripts_installed() {
    info "Testing scripts installation..."

    docker run --rm $IMAGE test -f /home/claude/.claude/bin/gh-projects/gh-project-init || \
        error "Scripts not installed"

    info "✓ Scripts installed"
}

# Test 3: Scripts are executable
test_scripts_executable() {
    info "Testing scripts are executable..."

    docker run --rm $IMAGE gh-project-init --help > /dev/null || \
        error "Scripts not executable"

    info "✓ Scripts executable"
}

# Test 4: Dependencies available
test_dependencies() {
    info "Testing dependencies..."

    docker run --rm $IMAGE which gh > /dev/null || error "gh not found"
    docker run --rm $IMAGE which git > /dev/null || error "git not found"
    docker run --rm $IMAGE which jq > /dev/null || error "jq not found"

    info "✓ Dependencies available"
}

# Test 5: Volume mounts work
test_volumes() {
    info "Testing volume mounts..."

    TMP_DIR=$(mktemp -d)
    echo "test" > $TMP_DIR/test.txt

    docker run --rm -v $TMP_DIR:/workspace $IMAGE cat /workspace/test.txt || \
        error "Volume mount failed"

    rm -rf $TMP_DIR
    info "✓ Volume mounts work"
}

# Test 6: User is non-root
test_nonroot() {
    info "Testing non-root user..."

    USER=$(docker run --rm $IMAGE whoami)

    if [ "$USER" = "root" ]; then
        error "Running as root (should be non-root)"
    fi

    info "✓ Running as non-root user: $USER"
}

# Test 7: Multi-arch support
test_multiarch() {
    info "Testing multi-arch support..."

    # AMD64
    docker pull --platform linux/amd64 $IMAGE || error "AMD64 image not available"

    # ARM64
    docker pull --platform linux/arm64 $IMAGE || error "ARM64 image not available"

    info "✓ Multi-arch support verified"
}

# Run all tests
main() {
    info "Running Docker image tests..."
    echo ""

    test_build
    test_scripts_installed
    test_scripts_executable
    test_dependencies
    test_volumes
    test_nonroot
    test_multiarch

    echo ""
    info "All Docker tests passed!"
}

main "$@"
```

#### 3.7 Update README with Container Instructions (30 minutes)

Add to README.md:

```markdown
## Container Deployment

### Docker

Pull and run pre-built image:

```bash
# Pull image
docker pull ghcr.io/o2alexanderfedin/claude-config:latest

# Run interactive
docker run -it --rm \
  -e ANTHROPIC_API_KEY=$ANTHROPIC_API_KEY \
  -e GITHUB_TOKEN=$GITHUB_TOKEN \
  -v $(pwd):/workspace \
  ghcr.io/o2alexanderfedin/claude-config:latest \
  bash
```

### Docker Compose

```bash
# Start services
docker-compose up -d

# Enter container
docker-compose exec claude-config bash

# Initialize project
docker-compose exec claude-config gh-project-init --project 14
```

### DevContainers

Open in VS Code:
1. Install "Dev Containers" extension
2. Command Palette → "Dev Containers: Reopen in Container"
3. Scripts automatically available

See [Container Guide](docs/CONTAINER_GUIDE.md) for complete documentation.
```

### Testing Strategy - Phase 3

#### 3.8 Container Testing (2 hours)

**Test Environments:**

1. **Local Docker Desktop**
   - macOS (Apple Silicon and Intel)
   - Test both architectures
   - Test volume mounts
   - Test credential persistence

2. **GitHub Actions Runners**
   - Ubuntu (AMD64)
   - Test multi-arch builds
   - Test registry publishing

3. **Production-like Environments**
   - AWS ECS (if available)
   - Kubernetes cluster (if available)
   - Test scaling and orchestration

**Test Scenarios:**

1. **Basic functionality**
   - Image builds successfully
   - Scripts installed and executable
   - Dependencies available
   - Help commands work

2. **Integration**
   - GitHub CLI authentication
   - Project initialization
   - Issue creation
   - Volume mounts work

3. **Security**
   - Runs as non-root
   - Secrets not in image
   - Network isolation works
   - File permissions correct

4. **Performance**
   - Image size reasonable (<500MB)
   - Build time acceptable (<10 minutes)
   - Startup time fast (<5 seconds)

### Security Considerations - Phase 3

#### 3.9 Container Security Audit (1 hour)

**Security Checklist:**

- [ ] Base image from trusted source (official Node.js)
- [ ] Multi-stage build minimizes attack surface
- [ ] Runs as non-root user
- [ ] No secrets in image layers
- [ ] Minimal dependencies installed
- [ ] Security patches applied (apt-get update)
- [ ] Health check implemented
- [ ] Image scanned for vulnerabilities

**Tools:**

1. **Trivy** - Vulnerability scanner
   ```bash
   docker run --rm \
     -v /var/run/docker.sock:/var/run/docker.sock \
     aquasec/trivy image ghcr.io/o2alexanderfedin/claude-config:latest
   ```

2. **Docker Scout**
   ```bash
   docker scout cves ghcr.io/o2alexanderfedin/claude-config:latest
   ```

3. **Hadolint** - Dockerfile linter
   ```bash
   docker run --rm -i hadolint/hadolint < Dockerfile
   ```

**Add to CI:**

```yaml
# .github/workflows/docker-security.yml
name: Container Security Scan

on:
  push:
    branches: [main, develop]

jobs:
  scan:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4

      - name: Build image
        run: docker build -t test-image .

      - name: Run Trivy
        uses: aquasecurity/trivy-action@master
        with:
          image-ref: 'test-image'
          format: 'table'
          exit-code: '1'
          severity: 'CRITICAL,HIGH'
```

### Rollout Strategy - Phase 3

#### 3.10 Phase 3 Release (1 hour)

**Release Steps:**

1. **Create release branch**
   ```bash
   git flow release start 0.4.0
   ```

2. **Complete Phase 3 tasks**
   - Create Dockerfile
   - Add Docker Compose
   - Add DevContainer config
   - Create documentation
   - Add tests
   - Security scans

3. **Update CHANGELOG.md**
   ```markdown
   ## [0.4.0] - 2025-12-XX

   ### Added
   - Docker image with multi-arch support (amd64, arm64)
   - GitHub Container Registry publishing
   - Docker Compose configuration
   - DevContainer support for VS Code
   - Container usage documentation
   - Container security scanning
   - CI/CD integration examples

   ### Changed
   - Enhanced README with container deployment options
   - Improved documentation structure

   ### Security
   - Implemented non-root container user
   - Added vulnerability scanning to CI
   - Documented secret management best practices
   ```

4. **Update plugin.json version**
   ```bash
   jq '.version = "0.4.0"' .claude-plugin/plugin.json > tmp.json
   mv tmp.json .claude-plugin/plugin.json
   ```

5. **Commit and release**
   ```bash
   git add .
   git commit -m "feat: add container images and DevContainer support for v0.4.0

- Add Dockerfile with multi-arch builds
- Add Docker Compose configuration
- Add DevContainer config for VS Code
- Create comprehensive container documentation
- Implement container security scanning
- Add GitHub Container Registry publishing"

   git flow release finish 0.4.0
   git push origin develop main --tags

   # GitHub Actions will automatically:
   # - Build multi-arch images
   # - Run security scans
   # - Publish to ghcr.io
   # - Create GitHub release
   ```

6. **Verify release**
   - Check GitHub Container Registry: https://github.com/o2alexanderfedin/claude-config/pkgs/container/claude-config
   - Test image pull: `docker pull ghcr.io/o2alexanderfedin/claude-config:0.4.0`
   - Verify both architectures available
   - Test functionality in container

### Success Criteria - Phase 3

**Must Have:**
- [ ] Docker image builds successfully
- [ ] Multi-arch support (amd64, arm64)
- [ ] Published to GitHub Container Registry
- [ ] Scripts functional in container
- [ ] Documentation complete
- [ ] Security scans pass
- [ ] DevContainer works in VS Code

**Nice to Have:**
- [ ] Image size optimized (<500MB)
- [ ] Kubernetes deployment example
- [ ] Helm chart
- [ ] Performance benchmarks

---

## Cross-Phase Considerations

### Version Management

**Semantic Versioning Strategy:**
- **0.2.0:** Plugin conversion (minor feature)
- **0.3.0:** Bootstrap installer (minor feature)
- **0.4.0:** Container images (minor feature)
- **1.0.0:** All three phases complete + production-ready (major milestone)

**Git Flow Integration:**
```bash
# Each phase follows standard git-flow
git flow release start X.Y.0
# ... implement phase
git flow release finish X.Y.0

# Automatic via GitHub Actions
# - Build and test
# - Create release notes
# - Publish artifacts
# - Update documentation
```

### Documentation Strategy

**Documentation Hierarchy:**
```
README.md                           # Overview, quick start, all installation methods
├── Installation Methods            # Plugin, manual, bootstrap, container
├── Quick Start Guide              # Basic usage
└── Links to detailed docs

bin/gh-projects/README.md          # Scripts documentation (existing)
├── Script reference
├── Workflow examples
└── Troubleshooting

docs/
├── CONTAINER_GUIDE.md             # Phase 3: Container usage
├── INSTALLATION_GUIDE.md          # Phase 2: Detailed installation
├── SECURITY.md                    # Security best practices
└── CONTRIBUTING.md                # Development guide

.github/
├── workflows/                     # CI/CD automation
│   ├── release.yml               # Phase 1: Release automation
│   ├── test-install.yml          # Phase 2: Installation tests
│   └── docker-build.yml          # Phase 3: Container builds
└── ISSUE_TEMPLATE/               # Issue templates

CHANGELOG.md                       # Version history
LICENSE                            # MIT License
```

### Backward Compatibility

**Commitment:**
- Manual installation always supported
- Existing documentation remains valid
- Scripts work without plugin system
- Container use optional
- Git-flow workflow unchanged

**Migration Path:**
```
v0.1.0 (manual) → v0.2.0 (manual OR plugin)
                → v0.3.0 (manual OR plugin OR bootstrap)
                → v0.4.0 (manual OR plugin OR bootstrap OR container)
```

### Security Throughout

**Phase 1 Security:**
- No API keys in repository
- GitHub Actions use secrets
- .gitignore comprehensive

**Phase 2 Security:**
- Installer validates inputs
- No eval of user data
- HTTPS only
- Backup before overwrite

**Phase 3 Security:**
- Non-root container user
- Secrets via environment/volumes
- Vulnerability scanning
- Minimal attack surface

**Ongoing:**
- Dependabot enabled
- Security advisories monitored
- Regular updates
- Community reporting encouraged

### Testing Matrix

| Phase | Unit Tests | Integration Tests | E2E Tests | Security Scans |
|-------|-----------|-------------------|-----------|----------------|
| 1 | JSON validation | Plugin install | Full workflow | Secret scan |
| 2 | Script functions | Cross-platform | Team onboarding | Input validation |
| 3 | Container build | Multi-arch | CI/CD pipeline | Trivy/Scout |

### Metrics and Success Tracking

**Phase 1 Metrics:**
- Plugin installations (if marketplace analytics available)
- GitHub stars/forks
- Release downloads
- Issue reports

**Phase 2 Metrics:**
- Install script executions (if analytics added)
- Cross-platform adoption
- Issue resolution time
- Documentation page views

**Phase 3 Metrics:**
- Container pulls from ghcr.io
- Multi-arch distribution
- CI/CD integration examples
- Security scan results

**Overall Success:**
- Adoption rate increase
- Positive community feedback
- Reduced installation support issues
- Increased contributions

---

## Risk Management

### High-Priority Risks

| Risk | Phase | Impact | Mitigation |
|------|-------|--------|------------|
| Plugin API changes | 1 | High | Monitor Claude Code releases, maintain manual install |
| Cross-platform compatibility | 2 | Medium | Comprehensive testing, clear platform docs |
| Container security vulnerabilities | 3 | High | Automated scanning, regular updates |
| Breaking changes to users | All | High | Semantic versioning, migration guides |

### Medium-Priority Risks

| Risk | Phase | Impact | Mitigation |
|------|-------|--------|------------|
| Documentation outdated | All | Medium | Automated doc generation where possible |
| Test coverage gaps | All | Medium | Increase test automation |
| Performance degradation | 3 | Low | Benchmarking, optimization |

### Low-Priority Risks

| Risk | Phase | Impact | Mitigation |
|------|-------|--------|------------|
| Marketplace rejection | 1 | Low | Review guidelines, iterate |
| Limited Windows support | 2 | Low | Document limitations, WSL recommended |
| Image size bloat | 3 | Low | Multi-stage builds, optimization |

---

## Timeline Summary

### Phase 1: Plugin Conversion (v0.2.0)
**Duration:** 1-2 hours
**Completion:** Week 1

**Detailed Breakdown:**
- Create plugin.json: 30 min
- Create marketplace.json: 15 min
- Restructure directories: 30 min
- Update README: 45 min
- Add LICENSE: 10 min
- Create release automation: 30 min
- Create CHANGELOG: 15 min
- Local testing: 30 min
- Security audit: 15 min
- Release execution: 30 min

### Phase 2: Bootstrap Installer (v0.3.0)
**Duration:** 4-6 hours
**Completion:** Week 2-3

**Detailed Breakdown:**
- Create install.sh: 2 hours
- Create uninstall.sh: 30 min
- Create update.sh: 30 min
- Add installation tests: 1 hour
- Update README: 30 min
- Cross-platform testing: 2 hours
- CI/CD integration: 1 hour
- Security audit: 30 min
- Release execution: 1 hour

### Phase 3: Container Images (v0.4.0)
**Duration:** 8-10 hours
**Completion:** Week 4-5

**Detailed Breakdown:**
- Create Dockerfile: 2 hours
- Create Docker Compose: 1 hour
- Create DevContainer config: 1 hour
- Create multi-arch workflow: 2 hours
- Create container documentation: 2 hours
- Add container tests: 2 hours
- Update README: 30 min
- Container testing: 2 hours
- Security audit: 1 hour
- Release execution: 1 hour

**Total Estimated Time:** 13-18 hours across 5 weeks

---

## Conclusion

This 3-phase roadmap transforms claude-config from a manual git repository into a professionally distributable Claude Code plugin with enterprise-ready deployment options:

**Phase 1 (v0.2.0)** establishes plugin distribution with minimal effort and maximum impact, enabling one-command installation and positioning for ecosystem integration.

**Phase 2 (v0.3.0)** adds automated bootstrap installation for teams and CI/CD, eliminating manual setup complexity and enabling zero-knowledge deployment.

**Phase 3 (v0.4.0)** provides container images for enterprise workflows, supporting DevContainers, CI/CD pipelines, and reproducible environments.

Each phase delivers independent value while maintaining backward compatibility with existing git-flow workflows. Security, testing, and documentation are prioritized throughout, ensuring production-quality releases at every step.

The result is a flexible, professionally distributed tool accessible to solo developers, teams, and enterprises—with installation methods ranging from one-command plugin installation to sophisticated container orchestration.
