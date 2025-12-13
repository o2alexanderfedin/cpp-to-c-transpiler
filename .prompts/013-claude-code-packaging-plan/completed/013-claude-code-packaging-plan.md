# Plan: Claude Code CLI Packaging Implementation

<objective>
Create implementation roadmap for packaging claude-config as a distributable Claude Code plugin with bootstrap installer and container support.

Purpose: Enable one-command installation for developers and CI/CD environments
Input: Research findings from claude-code-packaging-research.md
Output: claude-code-packaging-plan.md with 3-phase implementation roadmap
</objective>

<context>
Research findings: @.prompts/012-claude-code-packaging-research/claude-code-packaging-research.md

Key findings to incorporate:
- Plugin system is production-ready (Oct 2025 public beta)
- Simple structure: `.claude-plugin/plugin.json` + existing directories
- Hybrid approach: plugin + bootstrap + containers
- Git workflow remains unchanged (non-breaking)
- Docker support is official (docker/sandbox-templates:claude-code)

Current state:
- Repository: https://github.com/o2alexanderfedin/claude-config
- Version: v0.1.0
- Contents: epic-to-user-stories skill, ensure-git-repo-setup skill, 11 GitHub Projects scripts
- Structure: skills/, commands/, bin/, README.md, .gitignore
</context>

<planning_requirements>
**Must address:**
- Minimal disruption to existing git-flow workflow
- Progressive enhancement (each phase adds value independently)
- Security considerations (API keys, secrets, permissions)
- Cross-platform compatibility (Mac, Linux, Windows)
- Documentation and examples for each distribution method

**Constraints:**
- Maintain backward compatibility with existing users
- Keep simple things simple (plugin.json first)
- Don't over-engineer (start with Phase 1, iterate based on feedback)

**Success criteria:**
- Phase 1: `/plugin install o2alexanderfedin/claude-config` works
- Phase 2: `curl -fsSL https://.../install.sh | bash` works
- Phase 3: `docker run` with claude-config works
- All phases: Existing git workflow unchanged
</planning_requirements>

<output_structure>
Save to: `.prompts/013-claude-code-packaging-plan/claude-code-packaging-plan.md`

Structure the plan using this XML format:

```xml
<plan>
  <summary>
    {One paragraph overview of the 3-phase approach}
  </summary>

  <phases>
    <phase number="1" name="plugin-conversion">
      <objective>{What this phase accomplishes}</objective>
      <timeline>{Estimated effort}</timeline>
      <tasks>
        <task priority="high">{Specific actionable task}</task>
        <task priority="medium">{Another task}</task>
      </tasks>
      <deliverables>
        <deliverable>{What's produced}</deliverable>
      </deliverables>
      <dependencies>{What must exist before this phase}</dependencies>
      <testing>{How to verify this phase works}</testing>
      <execution_notes>{Hints for implementation}</execution_notes>
    </phase>

    <phase number="2" name="bootstrap-installer">
      <objective>{What this phase accomplishes}</objective>
      <timeline>{Estimated effort}</timeline>
      <tasks>
        <task priority="high">{Specific actionable task}</task>
      </tasks>
      <deliverables>
        <deliverable>{What's produced}</deliverable>
      </deliverables>
      <dependencies>{What must exist before this phase}</dependencies>
      <testing>{How to verify this phase works}</testing>
      <execution_notes>{Hints for implementation}</execution_notes>
    </phase>

    <phase number="3" name="container-images">
      <objective>{What this phase accomplishes}</objective>
      <timeline>{Estimated effort}</timeline>
      <tasks>
        <task priority="high">{Specific actionable task}</task>
      </tasks>
      <deliverables>
        <deliverable>{What's produced}</deliverable>
      </deliverables>
      <dependencies>{What must exist before this phase}</dependencies>
      <testing>{How to verify this phase works}</testing>
      <execution_notes>{Hints for implementation}</execution_notes>
    </phase>
  </phases>

  <implementation_details>
    <plugin_structure>
      {Expected .claude-plugin/ directory structure}
      {Required fields in plugin.json}
      {Optional marketplace.json considerations}
    </plugin_structure>

    <bootstrap_installer>
      {Key features of install.sh}
      {Dependency detection strategy}
      {Error handling approach}
    </bootstrap_installer>

    <container_strategy>
      {Base image selection}
      {Volume mounting patterns}
      {Environment variable configuration}
    </container_strategy>

    <security_considerations>
      {API key management}
      {permissions.deny patterns}
      {Secret management for CI/CD}
    </security_considerations>
  </implementation_details>

  <rollout_strategy>
    <version_plan>
      - v0.2.0: Phase 1 (plugin conversion)
      - v0.3.0: Phase 2 (bootstrap installer)
      - v0.4.0: Phase 3 (container images)
    </version_plan>

    <communication>
      {How to announce each phase}
      {Documentation updates needed}
      {Migration guidance if applicable}
    </communication>
  </rollout_strategy>

  <metadata>
    <confidence level="{high|medium|low}">
      {Why this confidence level}
    </confidence>

    <dependencies>
      - Git repository (existing)
      - GitHub account with repo access
      - Docker/container knowledge (Phase 3 only)
      - Shell scripting (Phase 2 and 3)
    </dependencies>

    <open_questions>
      - Should marketplace.json be included in v0.2.0 or later?
      - What level of Windows support is needed for bootstrap installer?
      - Which container registry (ghcr.io vs Docker Hub)?
    </open_questions>

    <assumptions>
      - Users have git installed
      - Users have Claude Code CLI installed
      - Plugin system remains stable (public beta status)
      - Research findings remain accurate
    </assumptions>
  </metadata>
</plan>
```
</output_structure>

<phase_guidelines>
**Phase 1: Plugin Conversion (v0.2.0 - Quick Win)**
- Focus: Minimal viable plugin
- Effort: 1-2 hours
- Impact: High (enables native installation)
- Risk: Low (additive, non-breaking)

Tasks should include:
- Create `.claude-plugin/` directory
- Write plugin.json with required fields
- Add README.md in .claude-plugin/ with installation instructions
- Test installation with `/plugin install`
- Document in main README.md
- Create git release v0.2.0

**Phase 2: Bootstrap Installer (v0.3.0 - Team Enablement)**
- Focus: Automated setup for teams
- Effort: 4-6 hours
- Impact: Medium (onboarding efficiency)
- Risk: Medium (shell scripting, platform differences)

Tasks should include:
- Write install.sh with dependency detection
- Add uninstall.sh for cleanup
- Test on Mac, Linux, Windows (WSL)
- Add GitHub Actions for installer validation
- Document usage patterns
- Create git release v0.3.0

**Phase 3: Container Images (v0.4.0 - CI/CD Focus)**
- Focus: Containerized environments
- Effort: 8-10 hours
- Impact: Targeted (CI/CD, production deployments)
- Risk: Medium (container complexity, security)

Tasks should include:
- Create Dockerfile with multi-stage builds
- Write docker-compose.yml for development
- Add GitHub Actions for image building
- Publish to container registry
- Document volume mounting patterns
- Create git release v0.4.0
</phase_guidelines>

<success_criteria>
- Plan breaks work into independently valuable phases
- Each phase has clear deliverables and testing strategy
- Phases build on each other but don't block parallel work
- Security considerations addressed in each phase
- Documentation requirements identified
- Rollback strategy for each phase
- Metadata captures uncertainties and assumptions
- SUMMARY.md provides phase overview
- Ready for Phase 1 implementation to begin
</success_criteria>

<summary_requirements>
Create `.prompts/013-claude-code-packaging-plan/SUMMARY.md`

Format:
```markdown
# Claude Code Packaging Plan Summary

**{One sentence describing the 3-phase approach}**

## Version
v1

## Phase Overview
- Phase 1 (v0.2.0): {Quick description} - 1-2 hours
- Phase 2 (v0.3.0): {Quick description} - 4-6 hours
- Phase 3 (v0.4.0): {Quick description} - 8-10 hours

## Key Assumptions
- {Critical assumption 1}
- {Critical assumption 2}
- {Critical assumption 3}

## Decisions Needed
{Specific choices before implementation, or "None - ready to start Phase 1"}

## Blockers
{External impediments, or "None"}

## Next Step
Execute Phase 1: Create `.claude-plugin/plugin.json`

---
*Confidence: {High|Medium|Low}*
*Iterations: 1*
*Full output: claude-code-packaging-plan.md*
```
</summary_requirements>
