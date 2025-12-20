# Auto-Configuration Flow Diagram

## High-Level Flow

```
┌─────────────────────────────────────────┐
│  Script calls load_config()            │
└────────────────┬────────────────────────┘
                 │
                 ▼
         ┌───────────────┐
         │ Config exists?│
         └───────┬───────┘
                 │
         ┌───────┴───────┐
         │               │
        YES              NO
         │               │
         ▼               ▼
┌─────────────────┐  ┌──────────────────┐
│ Load existing   │  │ auto_init_config()│
│ config          │  └────────┬──────────┘
└─────────────────┘           │
                              ▼
                      ┌────────────────┐
                      │ Try strategies │
                      │ 1 → 2 → 3      │
                      └───────┬────────┘
                              │
                      ┌───────┴────────┐
                      │                │
                   SUCCESS           FAIL
                      │                │
                      ▼                ▼
            ┌─────────────────┐  ┌─────────────┐
            │ Config created  │  │ Show error  │
            │ Continue        │  │ Exit 1      │
            └─────────────────┘  └─────────────┘
```

## Detailed Strategy Cascade

```
auto_init_config() Entry
         │
         ▼
┌─────────────────────────────────────────┐
│ STRATEGY 1: Environment Variable        │
└────────────────┬────────────────────────┘
                 │
                 ▼
    ┌────────────────────────┐
    │ GH_PROJECT_NUMBER set? │
    └───────┬────────────────┘
            │
    ┌───────┴───────┐
    │               │
   YES              NO
    │               │
    ▼               ▼
┌──────────────┐  ┌──────────────────────────┐
│ Validate     │  │ STRATEGY 2: Repo Link    │
│ number       │  └──────────┬───────────────┘
└──────┬───────┘             │
       │                     ▼
       │         ┌───────────────────────┐
       │         │ get_current_context() │
       │         └──────────┬────────────┘
       │                    │
       │            ┌───────┴────────┐
       │            │                │
       │          SUCCESS           FAIL
       │            │                │
       │            ▼                ▼
       │   ┌─────────────────┐  ┌────────────────────┐
       │   │ Query repo for  │  │ STRATEGY 3: Single │
       │   │ linked projects │  │ Project            │
       │   └────────┬────────┘  └─────────┬──────────┘
       │            │                      │
       │    ┌───────┴───────┐              ▼
       │    │               │    ┌──────────────────┐
       │   1 project    0 or 2+  │ Query user for   │
       │    │          projects  │ all projects     │
       │    │               │    └─────────┬────────┘
       │    │               │              │
       │    │               │      ┌───────┴───────┐
       │    │               │      │               │
       │    │               │   1 project    0 or 2+
       │    │               │      │          projects
       │    │               │      │               │
       ▼    ▼               ▼      ▼               ▼
   ┌──────────────────────────────────────────────────┐
   │          initialize_config_from_project()        │
   └──────────────────────┬───────────────────────────┘
                          │
                  ┌───────┴────────┐
                  │                │
               SUCCESS           FAIL
                  │                │
                  ▼                ▼
        ┌──────────────┐    ┌──────────────┐
        │ Return 0     │    │ Determine    │
        │ (success)    │    │ error type   │
        └──────────────┘    └──────┬───────┘
                                   │
                                   ▼
                         ┌──────────────────┐
                         │ Show contextual  │
                         │ error message    │
                         │ Return 1 (fail)  │
                         └──────────────────┘
```

## Error Decision Tree

```
Auto-init failed
      │
      ▼
┌─────────────────┐
│ Why did it fail?│
└────────┬────────┘
         │
    ┌────┴────┬────────┬────────┬─────────┐
    │         │        │        │         │
    ▼         ▼        ▼        ▼         ▼
┌────────┐ ┌────┐ ┌────────┐ ┌─────┐ ┌────────┐
│No git  │ │No  │ │Multiple│ │API  │ │Project │
│repo    │ │proj│ │projects│ │fail │ │access  │
└───┬────┘ └─┬──┘ └───┬────┘ └──┬──┘ └───┬────┘
    │        │        │         │        │
    ▼        ▼        ▼         ▼        ▼
┌────────────────────────────────────────────┐
│         Show appropriate error             │
│         with specific solutions            │
└────────────────────────────────────────────┘
```

## Function Call Hierarchy

```
load_config()
    │
    ├─ ensure_config_dir()
    │
    ├─ auto_init_config()
    │   │
    │   ├─ detect_project_from_env()
    │   │
    │   ├─ detect_project_from_repo_link()
    │   │   │
    │   │   ├─ get_current_context()
    │   │   │   └─ gh repo view
    │   │   │
    │   │   └─ gh api graphql (repo projects)
    │   │
    │   ├─ get_single_project()
    │   │   └─ gh api graphql (user projects)
    │   │
    │   ├─ initialize_config_from_project()
    │   │   │
    │   │   ├─ get_current_context()
    │   │   ├─ gh project view (validate)
    │   │   ├─ get_project_id()
    │   │   ├─ save_config()
    │   │   └─ cache_fields()
    │   │
    │   └─ error_message_function()
    │
    └─ export config variables
```

## API Call Flow

```
┌─────────────────────────────────────────┐
│ Strategy 1: No API calls                │
│ (Environment variable check only)       │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│ Strategy 2: Repository Link             │
│                                         │
│  1. gh repo view                        │
│     → Get owner/repo                    │
│                                         │
│  2. gh api graphql                      │
│     → Query repository.projectsV2       │
│                                         │
│  3. gh project view NUM                 │
│     → Validate project access           │
│                                         │
│  4. gh project field-list NUM           │
│     → Cache field metadata              │
└─────────────────────────────────────────┘

┌─────────────────────────────────────────┐
│ Strategy 3: Single Project              │
│                                         │
│  1. gh repo view                        │
│     → Get owner/repo                    │
│                                         │
│  2. gh api graphql                      │
│     → Query viewer.projectsV2           │
│                                         │
│  3. gh project view NUM                 │
│     → Validate project access           │
│                                         │
│  4. gh project field-list NUM           │
│     → Cache field metadata              │
└─────────────────────────────────────────┘
```

## State Transitions

```
[No Config] ──(auto_init_config)──> [Config Created]
                    │
                    │ (fail)
                    ▼
                [Error + Exit]


[Config Exists] ──(load_config)──> [Config Loaded]
                                         │
                                         ▼
                                   [Script Runs]
```

## Detection Strategy Priority

```
Priority 1: GH_PROJECT_NUMBER
   ↓ (not set)
Priority 2: Repository Link
   ↓ (not found or multiple)
Priority 3: Single Project
   ↓ (multiple or none)
Fail with error
```

## Test Coverage Map

```
                    ┌─────────────────┐
                    │  load_config()  │
                    └────────┬────────┘
                             │
        ┌────────────────────┼────────────────────┐
        │                    │                    │
        ▼                    ▼                    ▼
┌───────────────┐  ┌──────────────────┐  ┌────────────────┐
│ Config exists │  │ auto_init_config │  │ Config invalid │
│ (load normal) │  │ (try detection)  │  │ (fail)         │
└───────────────┘  └─────────┬────────┘  └────────────────┘
                             │
        ┌────────────────────┼────────────────────┐
        │                    │                    │
        ▼                    ▼                    ▼
┌───────────────┐  ┌──────────────────┐  ┌────────────────┐
│ Strategy 1    │  │ Strategy 2       │  │ Strategy 3     │
│ (env var)     │  │ (repo link)      │  │ (single proj)  │
└───────┬───────┘  └─────────┬────────┘  └────────┬───────┘
        │                    │                    │
        ├─ Set & valid       ├─ 1 project         ├─ 1 project
        ├─ Set & invalid     ├─ 0 projects        ├─ 0 projects
        └─ Not set           ├─ 2+ projects       └─ 2+ projects
                             └─ API failure

Each branch = test case
```

## User Experience Flows

### Happy Path 1: Environment Variable

```
User sets: export GH_PROJECT_NUMBER=14
      │
      ▼
Script runs
      │
      ▼
load_config() called
      │
      ▼
No config exists
      │
      ▼
auto_init_config()
      │
      ▼
Strategy 1: Detects GH_PROJECT_NUMBER=14
      │
      ▼
Validates project #14 exists
      │
      ▼
Creates config.json
      │
      ▼
Script continues normally
```

### Happy Path 2: Repository Link

```
User cloned repo linked to project #14
      │
      ▼
Script runs (no env var set)
      │
      ▼
load_config() called
      │
      ▼
No config exists
      │
      ▼
auto_init_config()
      │
      ▼
Strategy 1: No env var (skip)
      │
      ▼
Strategy 2: Query repo for projects
      │
      ▼
Finds project #14 linked to repo
      │
      ▼
Creates config.json
      │
      ▼
Script continues normally
```

### Happy Path 3: Single Project

```
User has only 1 project (#14)
      │
      ▼
Script runs (no env var, no repo link)
      │
      ▼
load_config() called
      │
      ▼
No config exists
      │
      ▼
auto_init_config()
      │
      ▼
Strategy 1: No env var (skip)
      │
      ▼
Strategy 2: No repo link (skip)
      │
      ▼
Strategy 3: Query user projects
      │
      ▼
Finds exactly 1 project (#14)
      │
      ▼
Creates config.json
      │
      ▼
Script continues normally
```

### Error Path: Multiple Projects

```
User has 3 projects (#12, #14, #16)
      │
      ▼
Script runs (no env var, no repo link)
      │
      ▼
load_config() called
      │
      ▼
No config exists
      │
      ▼
auto_init_config()
      │
      ▼
Strategy 1: No env var (skip)
      │
      ▼
Strategy 2: No repo link (skip)
      │
      ▼
Strategy 3: Query user projects
      │
      ▼
Finds 3 projects (ambiguous)
      │
      ▼
Shows error message:
  "Multiple projects found. Cannot auto-select."
  "Specify which project to use:"
  "  1. export GH_PROJECT_NUMBER=14"
  "  2. gh-project-init --project 14"
      │
      ▼
Script exits with code 1
```

## Performance Profile

```
Scenario                    API Calls    Time
────────────────────────────────────────────
Config exists               0            <0.1s
Strategy 1 (env var)        2-3          <3s
Strategy 2 (repo link)      3-4          <4s
Strategy 3 (single project) 3-4          <4s
All strategies fail         4-5          <5s

First run (cold cache):     2-5 calls    <5s
Subsequent runs:            0 calls      <0.1s
```

## Config File Lifecycle

```
[No Config]
    │
    │ (auto_init_config succeeds)
    ▼
[Config Created]
    │
    │ (load_config on subsequent runs)
    ▼
[Config Loaded]
    │
    │ (script modifies project)
    ▼
[Config Still Valid]
    │
    │ (user runs gh-project-init --project OTHER)
    ▼
[Config Updated]
    │
    │ (user deletes config)
    ▼
[No Config] (cycle repeats)
```

## Rollback Scenarios

```
┌─────────────────────────────────────────┐
│ Auto-init causes issues                 │
└─────────────────┬───────────────────────┘
                  │
        ┌─────────┴─────────┐
        │                   │
        ▼                   ▼
┌─────────────┐   ┌──────────────────┐
│ Full revert │   │ Partial rollback │
└──────┬──────┘   └─────────┬────────┘
       │                    │
       ▼                    ▼
┌─────────────────┐  ┌───────────────────┐
│ Git revert      │  │ Revert only       │
│ entire commit   │  │ load_config()     │
│                 │  │ modification      │
│ All changes     │  │                   │
│ removed         │  │ Keep new functions│
│                 │  │ for future use    │
└─────────────────┘  └───────────────────┘
```

## Summary

This flowchart document visualizes:
1. Overall auto-init flow
2. Strategy cascade logic
3. Error handling paths
4. Function call hierarchy
5. API interaction patterns
6. User experience flows
7. Performance characteristics
8. Config lifecycle
9. Rollback options

Use these diagrams alongside the detailed implementation plan to guide development and testing.
