# GitHub Projects Templates

This directory contains version-controlled project templates that are available to all users of the repository.

## Available Templates

### `cpp-transpiler.json`

Standard project structure for C++ to C transpiler development.

**Source:** Project #14 - C++ to C Transpiler

**Fields (9):**
- **Status** (Single Select): Todo, In Progress, Done
- **Type** (Single Select): Epic, User Story, Task, Bug, Spike
- **Priority** (Single Select): Critical, High, Medium, Low
- **Effort** (Single Select): XS (0.5 days), S (1-2 days), M (3-5 days), L (1-2 weeks), XL (2+ weeks)
- **Sprint** (Text): Sprint identifier
- **Story Points** (Number): Estimation in points
- **Target Date** (Date): Target completion date
- **Parent issue** (Issue): Link to parent epic/story
- **Sub-issues progress** (Tracked by): Progress tracking for sub-issues

**Views (3):**
- **All** - Table view with all items
- **Kanban** - Board view grouped by Status
- **All Todo** - Filtered view showing Todo items

**Usage:**

```bash
# Clone complete project with all fields and views
gh-project-setup-clone \
  --template cpp-transpiler \
  --title "My Transpiler Project"

# Apply fields only to existing project
gh-project-setup-apply \
  --template cpp-transpiler \
  --project 15
```

## Creating Custom Templates

Export your own project structure as a template:

```bash
# Export to user templates directory
gh-project-setup-init --project 14 --owner myorg

# Export with custom name
gh-project-setup-init \
  --project 14 \
  --owner myorg \
  --name my-custom-template

# Export to repository (commit to version control)
gh-project-setup-init \
  --project 14 \
  --owner myorg \
  --output scripts/gh-projects/templates/my-template.json
```

## Template Structure

Templates are JSON files with the following structure:

```json
{
  "template_name": "cpp-transpiler",
  "template_version": "1.0",
  "export_timestamp": "2025-12-10T07:26:09Z",
  "source_project": {
    "owner": "o2alexanderfedin",
    "number": 14,
    "id": "PVT_kwHOBJ7Qkc4BKHLI",
    "title": "C++ to C Transpiler"
  },
  "fields": [
    {
      "name": "Status",
      "data_type": "ProjectV2SingleSelectField",
      "options": [
        {"name": "Todo", "description": "", "color": ""},
        {"name": "In Progress", "description": "", "color": ""},
        {"name": "Done", "description": "", "color": ""}
      ]
    }
  ],
  "views": [
    {
      "name": "Kanban",
      "layout": "BOARD_LAYOUT",
      "group_by_fields": ["Status"],
      "note": "Views cannot be created programmatically"
    }
  ]
}
```

## Template Priority

Templates are searched in the following order:

1. **Repository templates** (`scripts/gh-projects/templates/`) - Version-controlled, available to all users
2. **User templates** (`~/.config/gh-projects/templates/`) - Local customizations

If a template exists in both locations, the repository version takes precedence.

## Notes

- **View Limitation:** GitHub's GraphQL API does not support programmatic view creation. Use `gh-project-setup-clone` (which uses `copyProjectV2`) to clone projects with views, or create views manually in the UI.
- **Field Types:** Supports TEXT, NUMBER, DATE, SINGLE_SELECT, and ITERATION fields.
- **Source Project Access:** Cloning via `copyProjectV2` requires read access to the source project.
