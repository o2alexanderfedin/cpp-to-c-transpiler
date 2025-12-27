# Phase 52: Special Operator Overloading

**Quick Reference**: Detailed plan in `PHASE52-PLAN.md`

## Overview

Implement 12 special operators with complex semantics, including TODO resolution.

**Effort**: 105-165 hours sequential, 4-5 days parallel (12 agents)

## Operators Covered

1. Instance Subscript (`[]`)
2. Instance Call (`()`)
3. Arrow (`->`)
4. Dereference (`*`)
5. Stream Output (`<<`)
6. Stream Input (`>>`)
7. Bool Conversion (`operator bool()`)
8. Generic Conversion (`operator T()`)
9. Copy Assignment (`operator=`) - **TODO resolution**
10. Move Assignment (`operator=(T&&)`) - **TODO resolution**
11. Address-of (`&`)
12. Comma (`,`)

## Key Files

- **Plan**: `PHASE52-PLAN.md` (1400+ lines, complete specification)
- **Roadmap**: `../../OPERATOR_OVERLOADING_ROADMAP.md` (master coordination)

## Execution

```bash
/run-plan .planning/phases/52-special-operators/PHASE52-PLAN.md
```

## Success Criteria

- ✅ All 12 operators translate correctly
- ✅ 167-225 unit tests passing (100%)
- ✅ 30-40 integration tests passing (90%+)
- ✅ Smart pointer patterns work
- ✅ Stream I/O round-trips work
- ✅ TODOs resolved (CppToCVisitor.cpp:84-93, :95-101)
- ✅ Performance within 10% of C++

## Translation Example

```cpp
// C++
ptr->method();

// C
ClassName_method(SmartPointer_operator_arrow(&ptr));
```

## Critical TODO Resolution

This phase resolves two blocking TODOs:
- **CppToCVisitor.cpp:95-101**: Copy assignment storage (Task 9)
- **CppToCVisitor.cpp:84-93**: Move assignment storage (Task 10)

See `PHASE52-PLAN.md` for complete details.
