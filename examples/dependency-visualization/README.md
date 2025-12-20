# Dependency Graph Visualization Example

This directory demonstrates the dependency graph visualization feature of the C++ to C transpiler.

## Overview

The `DependencyGraphVisualizer` component analyzes include dependencies across generated C header and implementation files, detects circular dependencies, and outputs the dependency graph in DOT (Graphviz) format for easy visualization.

## Features

1. **Dependency Tracking**: Tracks which files include which other files
2. **Circular Dependency Detection**: Identifies and highlights circular dependencies
3. **Forward Declaration Tracking**: Shows forward declarations separately
4. **Visual Styling**: Different node styles for headers (.h) vs implementation files (.c)
5. **DOT Output**: Standard Graphviz format for easy rendering

## Usage

### Command Line Options

```bash
# Generate dependency graph with default filename (deps.dot)
cpptoc --visualize-deps source.cpp

# Generate dependency graph with custom filename
cpptoc --dump-deps=my-deps.dot source.cpp
```

### Viewing the Graph

Once you have a .dot file, you can visualize it using Graphviz:

```bash
# Generate PNG image
dot -Tpng deps.dot -o deps.png

# Generate SVG (scalable vector graphics)
dot -Tsvg deps.dot -o deps.svg

# Generate PDF
dot -Tpdf deps.dot -o deps.pdf

# Interactive viewer (if available)
xdot deps.dot
```

## Example Output

The `example-deps.dot` file in this directory shows a sample dependency graph for a simple multi-file project with:
- Point.h/Point.c (base data structure)
- Circle.h/Circle.c (depends on Point)
- Rectangle.h/Rectangle.c (depends on Point)
- Main.c (depends on all headers)

### Legend

- **Blue boxes**: Header files (.h)
- **Green ellipses**: Implementation files (.c)
- **Pink diamonds**: Forward declarations
- **Red highlighting**: Files/edges involved in circular dependencies (if any)

## Integration Points

The visualizer is designed to integrate with:
- `HeaderSeparator`: Tracks which declarations go to headers vs implementation
- `DependencyAnalyzer`: Tracks include dependencies for each file
- `FileOutputManager`: Handles file I/O for the .dot output

## Implementation

The implementation follows SOLID principles:
- **Single Responsibility**: Only handles dependency graph visualization
- **Open/Closed**: Extensible for different output formats
- **Interface Segregation**: Minimal, focused interface
- **Dependency Inversion**: Depends on abstractions (string-based file tracking)

## Testing

Comprehensive tests are available in `tests/DependencyGraphVisualizerTest.cpp`:
- Empty visualizer
- Single file dependencies
- Multiple file dependencies
- Forward declarations
- Simple circular dependencies
- Complex circular dependencies (A→B→C→A)
- DOT format validation
- File I/O

Run tests:
```bash
cd build
./DependencyGraphVisualizerTest
```

## Future Enhancements

Potential future improvements:
- HTML/interactive output format
- Dependency metrics (depth, fan-in, fan-out)
- Module grouping/clustering
- Highlight critical paths
- Integration with build systems
