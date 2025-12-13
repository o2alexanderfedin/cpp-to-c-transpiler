<objective>
Calculate comprehensive project velocity metrics across the full project history to understand development efficiency and productivity rates.

This analysis will help assess:
- How efficiently story points are being delivered
- Code output rates (production + test code)
- Feature/story completion rates
- Test coverage development alongside features
- Overall project health and sustainable pace

The results will inform future planning, estimation accuracy, and resource allocation decisions.
</objective>

<context>
This is the cpp-to-c-transpiler project - a C++ to C transpiler being developed using TDD, SOLID principles, and agile methodology with story point estimation.

Key project characteristics:
- All user stories have story point estimates (1-2 SP typically)
- Work is tracked in GitHub Project #14
- Epics and stories are documented in EPICS.md
- Test-driven development with comprehensive test coverage
- Git commits follow conventional commit format
- Multiple releases have been created (v0.1.0-research through v0.3.1)

@EPICS.md
@docs/ARCHITECTURE.md
</context>

<data_sources>
Gather data from multiple sources:

1. **Git history**: Analyze commit timestamps, commit messages, and code changes
   ```bash
   git log --all --pretty=format:"%H|%ai|%s" --numstat
   ```

2. **Story Points**: Extract from EPICS.md
   - Count total story points across all completed epics
   - List all user stories with their SP estimates

3. **Code metrics**: Calculate lines of code added/changed
   ```bash
   git log --all --numstat --pretty=format:"%H|%ai"
   ```

4. **Test coverage**: Identify test files and measure test code vs production code
   ```bash
   find . -name "*Test.cpp" -o -name "*test*.cpp" | xargs wc -l
   find ./src -name "*.cpp" | xargs wc -l
   ```

5. **Releases**: Analyze release tags and their scope
   ```bash
   git tag --list --sort=-version:refname
   git log --tags --simplify-by-decoration --pretty="format:%ai %d"
   ```

6. **GitHub Project data**: If accessible via gh CLI
   ```bash
   gh issue list --state closed --json number,title,labels,closedAt --limit 1000
   ```
</data_sources>

<analysis_requirements>
Thoroughly analyze the following metrics:

1. **Story Points Velocity**
   - Total story points delivered across all epics
   - Calculate: SP / estimated man-hours = SP per hour
   - Break down by epic/phase for trend analysis
   - Identify if velocity is increasing, stable, or decreasing

2. **Lines of Code Velocity**
   - Total LOC added (production code in ./src and ./include)
   - Total LOC added (test code in ./tests)
   - Calculate: LOC per hour for both categories
   - Ratio of test code to production code

3. **Features/Stories Velocity**
   - Total user stories completed
   - Total epics completed
   - Calculate: Stories per hour, Epics per hour
   - Average story completion time

4. **Test Coverage Velocity**
   - Number of test files created
   - Test LOC per production LOC ratio
   - Rate of test creation alongside features
   - Test count growth over time

5. **Time Estimation**
   Use commit patterns to estimate actual work time:
   - Group commits into work sessions (commits within 2 hours = same session)
   - Sum session durations (first commit to last commit in each session)
   - Account for gaps > 2 hours as breaks/non-work time
   - Calculate total estimated man-hours across project

6. **Efficiency Metrics**
   - Average time per story point
   - Average LOC per story point
   - Defect rate (if issues/bugs are tracked)
   - Refactoring ratio (commits with "refactor" in message)

7. **Trend Analysis**
   - Velocity changes over time (by epic or phase)
   - Learning curve effects (early vs later work)
   - Impact of methodology (TDD, SOLID) on velocity
</analysis_requirements>

<methodology>
Step-by-step analysis process:

1. **Extract commit data**
   - Get all commits with timestamps and stats
   - Parse conventional commit messages for categorization
   - Identify work sessions based on commit clustering

2. **Calculate work time**
   - Group commits within 2-hour windows into sessions
   - Sum session durations (first to last commit per session)
   - Total all session durations for man-hours estimate
   - Account for multi-day gaps appropriately

3. **Extract story point data**
   - Parse EPICS.md for all completed stories
   - Sum story points by epic, phase, and total
   - Map stories to commit timeframes if possible

4. **Calculate LOC metrics**
   - Separate production code (./src, ./include) from tests (./tests)
   - Sum additions and deletions to get net changes
   - Calculate total LOC contributed

5. **Compute velocity metrics**
   - SP per hour = Total SP / Total man-hours
   - LOC per hour = Total LOC / Total man-hours
   - Stories per hour = Total stories / Total man-hours
   - Tests per hour = Test LOC / Total man-hours

6. **Generate insights**
   - Compare metrics across epics/phases
   - Identify velocity trends
   - Assess sustainability of current pace
   - Recommend adjustments if needed
</methodology>

<output_format>
Create a comprehensive velocity report and save to: `./analyses/project-velocity-report.md`

Structure the report as follows:

## Project Velocity Analysis

### Executive Summary
- Total man-hours estimated
- Overall velocity (SP/hour, LOC/hour, Stories/hour)
- Key findings and recommendations

### Time Analysis
- Total commits analyzed
- Work sessions identified
- Total estimated man-hours
- Project timeline (start to current)
- Average daily work hours (if calculable)

### Story Points Velocity
- Total story points delivered
- Story points per hour
- Breakdown by epic/phase
- Velocity trend over time

### Code Output Velocity
- Total production LOC
- Total test LOC
- Production LOC per hour
- Test LOC per hour
- Test-to-production ratio

### Feature Delivery Velocity
- Total epics completed
- Total user stories completed
- Epics per hour
- Stories per hour
- Average story completion time

### Test Coverage Velocity
- Total test files created
- Tests per feature ratio
- Test coverage growth rate
- Testing efficiency

### Quality Metrics
- Refactoring rate
- Bug fix commits (if identifiable)
- Code review commits
- Documentation commits

### Trend Analysis
- Velocity changes over time
- Learning curve effects
- Methodology impact
- Sustainable pace assessment

### Recommendations
- Is current velocity sustainable?
- Areas for improvement
- Estimation accuracy assessment
- Future planning guidance

### Raw Data Summary
Include tables with:
- Epic breakdown (name, SP, stories, estimated hours)
- Session breakdown (date, duration, commits, LOC)
- Release milestones (tag, date, scope)
</output_format>

<verification>
Before completing, verify the analysis includes:

- [x] All git commits analyzed from project start to current
- [x] Work time estimated using commit clustering methodology
- [x] Story points tallied from EPICS.md
- [x] LOC calculated separately for production and test code
- [x] All four requested velocity metrics calculated (SP/hour, LOC/hour, Stories/hour, Test coverage)
- [x] Trend analysis showing velocity changes over time
- [x] Insights and recommendations based on data
- [x] Report saved to ./analyses/project-velocity-report.md
- [x] Raw data tables included for verification
</verification>

<success_criteria>
Analysis is complete and accurate when:

1. All commits from project inception are included in analysis
2. Man-hours estimation uses commit clustering (2-hour session windows)
3. All four velocity metrics are calculated with clear formulas shown
4. Story point data matches what's documented in EPICS.md
5. LOC calculations separate production code from test code
6. Trend analysis shows velocity changes across epics/phases
7. Report provides actionable insights and recommendations
8. All calculations are documented and reproducible
9. Report is saved to ./analyses/project-velocity-report.md
10. Executive summary answers: "What is our velocity in man-hours per hour?" for each metric
</success_criteria>
