# Resource Manager - Real-World Test Project

## Overview
Generic resource management system demonstrating:
- RAII (Resource Acquisition Is Initialization)
- Smart pointers (unique_ptr, shared_ptr)
- Move semantics
- Template metaprogramming
- Custom deleters
- Reference counting
- Thread safety (basic)

## Features
- Generic resource handles
- Automatic cleanup
- Custom deleters for different resource types
- Resource pools
- Reference counting
- Scope guards
- File handles, memory, network connections
- RAII wrappers for C resources

## C++ Features Tested
1. **RAII**: Automatic resource management
2. **Smart Pointers**: unique_ptr, shared_ptr custom implementations
3. **Move Semantics**: Efficient resource transfer
4. **Templates**: Generic resource management
5. **Custom Deleters**: Type-specific cleanup
6. **Exceptions**: Resource leak prevention
7. **STL**: std::vector, std::map, std::function

## Target Size
7,000-10,000 LOC (with extensive examples and resource types)
