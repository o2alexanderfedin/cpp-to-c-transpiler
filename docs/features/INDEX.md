# C++ Feature Implementation Guides

This directory contains detailed implementation guides for translating advanced C++ features to C code.

## Feature Guides

### [exceptions.md](exceptions.md) - Exception Handling (599 lines)

**PNaCl SJLJ Pattern** - Thread-safe exception handling with action tables

- setjmp/longjmp based implementation
- Thread-local exception frame stack
- Action tables for destructor management
- RAII + exceptions integration via CFG analysis
- Validated by: Comeau C++ (1990s), PNaCl (2013), Emscripten (present)

**Key Sections:**
- Exception runtime API (cxx_throw, cxx_frame_push/pop)
- Try-catch block transformation
- Exception action tables
- Integration with RAII destructors

### [rtti.md](rtti.md) - Runtime Type Information (938 lines)

**Itanium ABI Pattern** - type_info generation and dynamic_cast translation

- type_info structure generation
- Class hierarchy tables
- dynamic_cast pointer adjustment
- typeid operator translation
- vtable integration

**Key Sections:**
- type_info table structure
- Class hierarchy encoding
- Pointer adjustment algorithms
- Integration with virtual functions

### [virtual-inheritance.md](virtual-inheritance.md) - Virtual Inheritance (997 lines)

**VTT Generation** - Resolving the diamond problem in C

- Virtual Table Tables (VTT)
- Virtual base offset tables
- Construction vtables
- Diamond problem resolution
- Multiple virtual bases

**Key Sections:**
- VTT structure and layout
- Virtual base offset computation
- Constructor/destructor handling
- Memory layout optimization

### [coroutines.md](coroutines.md) - C++20 Coroutines (1,321 lines)

**State Machine Transformation** - LLVM CoroSplit patterns for C

- Coroutine frame generation
- State machine transformation
- Suspend/resume points
- Promise type translation
- Coroutine handle implementation

**Key Sections:**
- Frame layout design
- State enumeration
- Suspend/resume mechanics
- Promise object integration
- Heap vs. stack elision

## Implementation Timeline

- **Phase 3** (8-12 weeks): Exceptions + RTTI
- **Phase 4** (8-12 weeks): Virtual inheritance + Coroutines

## Complexity Estimates

| Feature | Implementation Complexity | Lines of Code | Time Estimate |
|---------|---------------------------|---------------|---------------|
| Exceptions | Medium | 800-1200 | 3-4 weeks |
| RTTI | Medium | 600-900 | 3-4 weeks |
| Virtual Inheritance | High | 1000-1500 | 4-5 weeks |
| Coroutines | High | 1200-1800 | 5-6 weeks |

## Related Documentation

- [../SUMMARY.md](../SUMMARY.md) - Executive summary
- [../technical-analysis.md](../technical-analysis.md) - Complete technical analysis
- [../architecture/](../architecture/) - Architecture decisions

---

*Part of C++ to C Transpiler Research v1.5.1*
