# GitHub Project Configuration

**Project Name:** C++ to C Transpiler
**Project URL:** https://github.com/users/o2alexanderfedin/projects/14
**Project Number:** #14
**Created:** 2025-12-08

## Overview

This project uses a SCRUM/Kanban hybrid approach with custom fields for tracking Epics, User Stories, and Tasks.

## Custom Fields

### Type (Single Select)
Defines the hierarchy and type of work item:
- **Epic** - Large feature or initiative spanning multiple sprints
- **User Story** - User-facing functionality (usually 1-2 sprints)
- **Task** - Implementation work or technical task
- **Bug** - Defect or issue to fix
- **Spike** - Research or investigation work

### Priority (Single Select)
Business priority for the work item:
- **Critical** - Blocking or severe impact, must be done ASAP
- **High** - Important, should be done soon
- **Medium** - Normal priority, planned work
- **Low** - Nice to have, backlog item

### Effort (Single Select)
Estimated complexity/size (T-shirt sizing):
- **XS** - < 2 hours
- **S** - 2-4 hours
- **M** - 1-2 days
- **L** - 3-5 days
- **XL** - 1-2 weeks
- **XXL** - > 2 weeks (should be broken down)

### Sprint (Text)
Sprint identifier (e.g., "2025-W50", "Sprint 1")

### Story Points (Number)
Fibonacci-based story points (1, 2, 3, 5, 8, 13, 21)

### Target Date (Date)
Target completion date for the item

## Default Fields (GitHub)

- **Status** - Todo, In Progress, Done, etc.
- **Assignees** - Who is working on this
- **Labels** - Additional categorization
- **Milestone** - Release milestone
- **Repository** - Linked repository

## Workflow Structure

### Epic → User Story → Task Hierarchy

```
Epic: Exception Handling Implementation
├─ User Story: PNaCl SJLJ Pattern
│  ├─ Task: Implement frame stack
│  ├─ Task: Implement setjmp/longjmp wrapper
│  └─ Task: Create action tables
├─ User Story: CFG-based Destructor Injection
│  ├─ Task: Analyze control flow graph
│  ├─ Task: Identify cleanup points
│  └─ Task: Inject destructor calls
└─ User Story: Exception Runtime Library
   ├─ Task: Implement cxx_throw
   ├─ Task: Implement cxx_frame_push/pop
   └─ Task: Create exception_runtime.c
```

## Views (To Be Created)

### 1. Kanban Board
- **Columns:** Backlog, Todo, In Progress, Review, Done
- **Group by:** Status
- **Filter:** Current sprint items

### 2. Sprint Board
- **Columns:** Todo, In Progress, Done
- **Group by:** Type (Epic → Story → Task)
- **Filter:** Items with Sprint field set

### 3. Backlog
- **Layout:** Table view
- **Columns:** Title, Type, Priority, Effort, Sprint
- **Sort by:** Priority (desc), Effort (asc)
- **Filter:** Status != Done

### 4. Roadmap
- **Layout:** Timeline/Roadmap view
- **Group by:** Epic
- **Show:** Target Date and dependencies
- **Filter:** Type = Epic OR Type = User Story

## Usage Guidelines

### Creating Epics

1. Create GitHub Issue with title: `[EPIC] Feature Name`
2. Add to Project #14
3. Set Type = Epic
4. Set Priority based on business value
5. Set Target Date for completion
6. Link to PRD/Architecture docs in description
7. Tag with epic label

### Creating User Stories

1. Create GitHub Issue with title: `As a [user], I want [goal] so that [benefit]`
2. Add to Project #14
3. Set Type = User Story
4. Set Priority (inherit from Epic or adjust)
5. Set Effort (S/M/L for stories)
6. Set Story Points (Fibonacci: 1, 2, 3, 5, 8, 13)
7. Link to parent Epic in description: `Epic: #123`
8. Tag with story label

### Creating Tasks

1. Create GitHub Issue with title describing technical work
2. Add to Project #14
3. Set Type = Task
4. Set Effort (XS/S/M for tasks)
5. Link to parent User Story: `Story: #456`
6. Assign to developer
7. Add technical labels (component, area)

### Sprint Planning

1. Create new sprint (e.g., "2025-W50")
2. Select User Stories from backlog
3. Break down stories into tasks
4. Set Sprint field on all items
5. Assign tasks to team members
6. Sum story points for velocity tracking

## Automation (Future)

GitHub Actions workflows can automate:
- Auto-assign Type based on issue title prefix
- Auto-set Priority based on labels
- Move items to "In Progress" when assigned
- Move items to "Review" when PR created
- Move items to "Done" when PR merged
- Update Sprint field based on milestone

## Integration with Repository

The project is linked to: `o2alexanderfedin/cpp-to-c-transpiler`

All issues created in this repository will be available to add to the project.

## Field IDs (For Automation)

- **Type:** PVTSSF_lAHOBJ7Qkc4BKHLIzg6E1I4
- **Priority:** PVTSSF_lAHOBJ7Qkc4BKHLIzg6E1Kk
- **Effort:** PVTSSF_lAHOBJ7Qkc4BKHLIzg6E1M4
- **Sprint:** PVTF_lAHOBJ7Qkc4BKHLIzg6E1O0
- **Story Points:** PVTF_lAHOBJ7Qkc4BKHLIzg6E1SA
- **Target Date:** PVTF_lAHOBJ7Qkc4BKHLIzg6E1VU

## References

- **GitHub Projects Docs:** https://docs.github.com/en/issues/planning-and-tracking-with-projects
- **SCRUM Guide:** https://scrumguides.org/
- **Story Point Estimation:** Use Fibonacci sequence (1, 2, 3, 5, 8, 13, 21)
- **T-shirt Sizing:** XS < 2h, S = 2-4h, M = 1-2d, L = 3-5d, XL = 1-2w

---

**Last Updated:** 2025-12-08
**Maintained By:** Project Team
