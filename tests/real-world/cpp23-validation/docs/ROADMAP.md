# C++23 Transpiler Support Roadmap

**Project**: Hupyy C++ to C Transpiler
**Document Type**: Development Roadmap
**Last Updated**: December 24, 2025
**Related**: [FEATURE-MATRIX.md](FEATURE-MATRIX.md), [GAPS.md](GAPS.md)

---

## Vision and Strategic Goals

### North Star
**Enable practical C++ → C transpilation for embedded, safety-critical, and legacy C environments while maintaining realistic expectations about C++23 support.**

### Core Principles
1. **Honesty First**: Document what works and what doesn't
2. **Practicality Over Perfection**: 80% support for useful features beats 10% support for all features
3. **Incremental Progress**: Improve step-by-step, validate with tests
4. **Architectural Realism**: Accept that some C++ features cannot be cleanly transpiled to C

### Success Criteria
- **Build Success Rate**: 70%+ of adapted tests compile as C99
- **Output Match Rate**: 50%+ of compiled tests produce correct output
- **C++11 Support**: 85%+ (up from current 70-75%)
- **C++17 Support**: 60%+ (up from current 40-45%)
- **C++20 Support**: 30%+ (up from current 15-20%)
- **C++23 Support**: 15%+ (up from current 0-5%)

---

## Roadmap Phases

### Phase 34: Foundation Cleanup (Current → +10% Overall)
**Timeline**: 1-2 weeks
**Focus**: Fix known issues, establish baseline, improve core infrastructure
**Priority**: CRITICAL

#### Objectives
1. ✅ **Baseline Establishment**
   - Run Phase 33.5: Generate baseline metrics from 130 GCC tests
   - Document actual pass rates (currently unknown)
   - Identify quick wins vs hard problems

2. 🔧 **Critical Bug Fixes**
   - Fix namespace handling (currently not converted to C)
   - Fix class-to-struct conversion edge cases
   - Fix template monomorphization for pointer types (recent fix, validate thoroughly)

3. 🔧 **Attribute Handling**
   - Strip or preserve common attributes (`[[nodiscard]]`, `[[maybe_unused]]`, etc.)
   - Document which attributes are safe to strip
   - Add warnings for critical attributes like `[[assume]]`

4. 🔧 **Error Message Improvements**
   - Better diagnostics when C++23 features are encountered
   - Suggest workarounds in error messages
   - Point users to GAPS.md for unsupported features

#### Deliverables
- [ ] `results/baseline-metrics.json` with real data
- [ ] `results/compliance-report.html`
- [ ] Bug fixes for top 5 failing test categories
- [ ] Improved error messages with actionable guidance

#### Success Metrics
- All 130 adapted tests have known status (pass/fail/build-error)
- At least 10% improvement in build success rate from baseline
- Clear understanding of what needs to be fixed next

---

### Phase 35: Template System Enhancements (C++11 → 80%)
**Timeline**: 2-3 weeks
**Focus**: Improve template monomorphization, CTAD, and specialization
**Priority**: HIGH

#### Objectives
1. 🔧 **Advanced Monomorphization**
   - Support variadic templates (currently partial)
   - Handle template template parameters
   - Improve deduction for complex types

2. 🔧 **CTAD Improvements**
   - Full Class Template Argument Deduction for C++17
   - Deduction guides
   - Inherited constructor deduction (C++23, P2582R1)

3. 🔧 **Specialization**
   - Partial template specialization edge cases
   - Explicit specialization with inheritance
   - Function template specialization

4. 📋 **Testing**
   - Validate against AdvancedTemplateIntegrationTest
   - Run template-heavy real-world code
   - A/B test with monomorphization-generated code

#### Deliverables
- [ ] Variadic template support (pack expansion)
- [ ] CTAD with inheritance working
- [ ] Template specialization passing 80%+ of tests
- [ ] Updated FEATURE-MATRIX.md with improved template scores

#### Success Metrics
- Template category: 35% → 60% pass rate
- auto-deduction-P0849: 0/22 → 15/22 passing
- class-template-deduction: 0/10 → 7/10 passing

#### Known Limitations
- ❌ Template metaprogramming (SFINAE, concepts) - deferred
- ❌ Fold expressions - deferred
- ❌ C++20 concepts - architectural limitation

---

### Phase 36: Type System & auto Deduction (C++14 → 70%)
**Timeline**: 1-2 weeks
**Focus**: Improve `auto`, `decltype`, and type inference
**Priority**: HIGH

#### Objectives
1. 🔧 **Enhanced auto Deduction**
   - `auto` for lambda types
   - `auto` return type deduction
   - Structured bindings (C++17, if possible)

2. 🔧 **decltype Support**
   - `decltype(auto)`
   - `decltype` in complex expressions
   - SFINAE-friendly decltype

3. 📋 **auto(x) Decay-Copy (P0849R8)**
   - Implement decay semantics
   - `auto(x)` vs `auto{x}` distinction
   - Validate with GCC auto-deduction tests

#### Deliverables
- [ ] `auto` passing 90%+ of simple cases
- [ ] `decltype` working for most expressions
- [ ] `auto(x)` decay-copy implemented
- [ ] auto-deduction-P0849: 15/22 → 18/22 passing

#### Success Metrics
- Type system category: 55% → 75% pass rate
- auto-deduction tests: 0/22 → 18/22 passing

#### Known Limitations
- ❌ Structured bindings - complex, deferred
- ⚠️ auto with lambdas - may have edge cases

---

### Phase 37: Lambda Improvements (C++11/14 → 50%)
**Timeline**: 2-3 weeks
**Focus**: Better lambda support, closure conversion
**Priority**: MEDIUM

#### Objectives
1. 🔧 **Stateless Lambda Optimization**
   - Convert stateless lambdas to function pointers
   - Inline simple lambdas
   - Optimize vtable generation

2. 🔧 **Capture Improvements**
   - Mutable captures
   - Init-captures (C++14)
   - Perfect forwarding in captures

3. 📋 **Generic Lambdas (C++14)**
   - Auto parameters in lambdas
   - Generate monomorphized versions
   - Validate with real-world code

#### Deliverables
- [ ] Stateless lambdas: 40% → 80% pass rate
- [ ] Capture support: 25% → 60% pass rate
- [ ] Generic lambda support (basic cases)

#### Success Metrics
- Lambda category: 20% → 50% pass rate
- Real-world code with lambdas transpiles correctly

#### Known Limitations
- ❌ Template lambdas (C++20) - deferred
- ❌ Lambdas in unevaluated contexts - architectural limitation
- ⚠️ Complex captures may still have issues

---

### Phase 38: Partial constexpr Support (C++11 → 25%)
**Timeline**: 2-4 weeks
**Focus**: Limited compile-time evaluation via constant folding
**Priority**: MEDIUM

#### Objectives
1. 🔧 **Constant Folding**
   - Evaluate simple `constexpr` expressions at transpile-time
   - Integer arithmetic, boolean logic
   - Compile-time constant propagation

2. 📋 **Constexpr Variables**
   - Detect `constexpr` variables with compile-time values
   - Emit as `#define` or `static const` in C
   - Validate with simple cases

3. ⚠️ **Limited constexpr Functions**
   - Convert simple `constexpr` functions to runtime equivalents
   - Warn when compile-time evaluation is lost
   - Document performance implications

#### Deliverables
- [ ] Constant folding for arithmetic expressions
- [ ] `constexpr` variables as C constants
- [ ] Basic `constexpr` function conversion
- [ ] constexpr-enhancements: 0/19 → 5/19 passing

#### Success Metrics
- Constexpr category: 0% → 25% pass rate
- Simple compile-time constants work
- Users understand performance trade-offs

#### Known Limitations
- ❌ Full `constexpr` evaluation - requires compile-time interpreter (massive undertaking)
- ❌ `consteval` immediate functions - architectural limitation
- ❌ `if consteval` - architectural limitation
- ⚠️ Only simple expressions can be folded

**Important Note**: This phase provides **limited** constexpr support. Full compile-time execution is not feasible. See GAPS.md for details.

---

### Phase 39: Operator Overloading Extensions (Incremental)
**Timeline**: 1-2 weeks
**Focus**: Better operator conversion, C++23 operator features
**Priority**: LOW

#### Objectives
1. 🔧 **Improved Operator Conversion**
   - Better name mangling for operators
   - Consistent conversion to `Type_operator_add()` style
   - Operator chaining support

2. 📋 **Multidimensional Subscript (P2128R6)**
   - Convert `operator[](T1, T2)` to `Type_subscript_2d(T1, T2)`
   - Generate helper macros for ergonomics
   - Validate with Matrix/Tensor examples

3. 📋 **Static Operators (P1169R4)**
   - Convert static `operator()` to free functions
   - Convert static `operator[]` to free functions
   - Document usage patterns

#### Deliverables
- [ ] Multidimensional subscript working (basic cases)
- [ ] Static operators converted correctly
- [ ] multidim-subscript-P2128: 0/16 → 10/16 passing
- [ ] static-operators-P1169: 0/8 → 6/8 passing

#### Success Metrics
- Operator category: 50% → 65% pass rate
- C++23 operator tests: 0/24 → 16/24 passing

#### Known Limitations
- ⚠️ Syntax is less ergonomic in C (function calls vs operators)
- ⚠️ Complex operator overloading may still fail

---

### Phase 40: Exception Handling Hardening (C++11 → 80%)
**Timeline**: 1-2 weeks
**Focus**: Fix edge cases in exception handling
**Priority**: LOW

#### Objectives
1. 🔧 **Stack Unwinding**
   - Fix destructor calls in complex control flow
   - Early returns, gotos, loop exits
   - Nested try/catch blocks

2. 🔧 **Exception Specifications**
   - `noexcept` tracking and enforcement
   - Dynamic exception specifications (deprecated but still exist)
   - Propagate exception info through call stack

3. 📋 **Performance**
   - Reduce `setjmp`/`longjmp` overhead
   - Optimize exception-free paths
   - Consider table-based unwinding

#### Deliverables
- [ ] Exception category: 60% → 80% pass rate
- [ ] Complex exception tests passing
- [ ] Performance benchmarks

#### Success Metrics
- Exception handling robust for real-world code
- No memory leaks or crashes in exception paths

#### Known Limitations
- ⚠️ `setjmp`/`longjmp` has inherent limitations
- ⚠️ Performance overhead vs native C++ exceptions

---

### Phase 41: RTTI Improvements (C++11 → 85%)
**Timeline**: 1 week
**Focus**: Improve `typeid`, `dynamic_cast`, and type_info generation
**Priority**: LOW

#### Objectives
1. 🔧 **Type Info Generation**
   - Complete type_info structs for all polymorphic types
   - Inheritance hierarchy metadata
   - Cross-cast support

2. 🔧 **dynamic_cast Edge Cases**
   - Cross-casts in complex hierarchies
   - Virtual inheritance casts
   - Null and void* casts

3. 📋 **Performance**
   - Optimize type checks
   - Cache cast results
   - Reduce type_info size

#### Deliverables
- [ ] RTTI category: 70% → 85% pass rate
- [ ] dynamic_cast working for all inheritance patterns

#### Success Metrics
- Real-world polymorphic code transpiles correctly
- RTTI overhead acceptable

---

### Phase 42: Documentation & Tooling (Ongoing)
**Timeline**: Ongoing
**Focus**: Improve user experience, documentation, and tooling
**Priority**: MEDIUM

#### Objectives
1. 📋 **User Guide**
   - Comprehensive guide for using transpiler
   - Common pitfalls and workarounds
   - Best practices for transpilable C++

2. 📋 **Migration Guide**
   - How to adapt C++23 code for transpilation
   - Feature compatibility checklist
   - Automated feature detection tool

3. 📋 **Error Message Improvements**
   - Context-aware error messages
   - Suggest fixes for common issues
   - Link to relevant GAPS.md sections

4. 📋 **IDE Integration**
   - LSP server for transpiler
   - Real-time feature support hints
   - Inline warnings for unsupported features

#### Deliverables
- [ ] User guide (50+ pages)
- [ ] Migration guide
- [ ] Feature detection tool
- [ ] Improved error messages

#### Success Metrics
- Users can self-serve solutions to 80% of problems
- Reduced support burden
- Faster onboarding for new users

---

### Phase 43: Real-World Validation (Testing)
**Timeline**: Ongoing
**Focus**: Test against real C++ projects, not just GCC tests
**Priority**: HIGH

#### Objectives
1. 📋 **Real-World Projects**
   - Integrate additional C++23 projects (beyond scivision/Cpp23-examples)
   - Embedded C++ frameworks
   - Game engine components
   - Scientific computing libraries

2. 📋 **Benchmarking**
   - Performance comparison (C vs C++)
   - Memory usage comparison
   - Binary size comparison

3. 📋 **Continuous Integration**
   - GitHub Actions workflow
   - Nightly compliance testing
   - Automated PR validation
   - Coverage badges

#### Deliverables
- [ ] 5+ real-world projects tested
- [ ] Performance benchmarks
- [ ] CI/CD pipeline active

#### Success Metrics
- Real-world code transpiles with <10% manual fixes
- Performance within 2x of native C++
- CI catches regressions before merge

---

## Features Unlikely to Be Supported (Architectural Limitations)

Based on analysis in [GAPS.md](GAPS.md), the following features are **architecturally incompatible** with C and unlikely to ever be fully supported:

### Never Supported
- ❌ **Full constexpr/consteval evaluation**: Requires compile-time interpreter (massive scope)
- ❌ **Concepts (C++20/23)**: No C equivalent, fundamental to template metaprogramming
- ❌ **Modules (C++20)**: C has no module system
- ❌ **Coroutines (full support)**: C has no native coroutines (partial support via manual transform)
- ❌ **Ranges library**: STL transpilation out of scope
- ❌ **Standard Library (C++20/23)**: std::expected, std::mdspan, std::format, etc.

### Partial Support Only (Workarounds)
- ⚠️ **Deducing this (P0847R7)**: Manual expansion to const/non-const/rvalue overloads
- ⚠️ **if consteval (P1938R3)**: May support detection but not compile-time branching
- ⚠️ **Template metaprogramming**: Monomorphization works, but not Turing-complete metaprogramming
- ⚠️ **Lambdas (advanced)**: Basic support possible, but not template lambdas or complex closures

---

## Success Metrics Over Time

### Current (Phase 33 Baseline)
- C++98/03: 85-90%
- C++11: 70-75%
- C++14: 60-65%
- C++17: 40-45%
- C++20: 15-20%
- C++23: 0-5%

### Target (After Phase 40)
- C++98/03: 95%
- C++11: 85%
- C++14: 75%
- C++17: 60%
- C++20: 30%
- C++23: 15%

### Stretch Goal (Phase 43+)
- C++98/03: 98%
- C++11: 90%
- C++14: 80%
- C++17: 70%
- C++20: 40%
- C++23: 25%

**Note**: 100% support is unrealistic due to architectural limitations. Focus is on practical, useful subset.

---

## Implementation Principles

### 1. Test-Driven Development
- Write/adapt tests before implementing features
- Use A/B testing framework for validation
- Maintain 80%+ test pass rate at all times

### 2. Incremental Progress
- Small, focused phases
- Ship early, ship often
- Validate before moving to next phase

### 3. Documentation-Driven
- Update FEATURE-MATRIX.md after each phase
- Keep GAPS.md current
- Document workarounds for users

### 4. Performance Awareness
- Benchmark C vs C++ output
- Optimize hot paths
- Document performance trade-offs

### 5. Backward Compatibility
- Don't break existing transpilation
- Regression tests for all phases
- Maintain stable API

---

## Risk Management

### High-Risk Items
1. **Scope Creep**: Attempting to support too many C++23 features
   - **Mitigation**: Strict prioritization, focus on high-impact features

2. **Performance Degradation**: More features → slower transpiler
   - **Mitigation**: Profile and optimize, use caching

3. **Architectural Limitations**: Hitting fundamental C vs C++ barriers
   - **Mitigation**: Be honest in GAPS.md, document workarounds

### Medium-Risk Items
1. **Test Suite Maintenance**: 130+ tests to keep updated
   - **Mitigation**: Automated test adaptation, CI/CD

2. **User Expectations**: Users expect 100% C++23 support
   - **Mitigation**: Clear communication in docs, realistic roadmap

### Low-Risk Items
1. **Dependency Updates**: Clang/LLVM version changes
   - **Mitigation**: Pin versions, test before upgrading

---

## Community Contributions

### How to Contribute
1. Pick a feature from "Phase 34-43" above
2. Check GAPS.md to understand limitations
3. Write tests first (adapt from GCC suite or create new)
4. Implement feature
5. Update FEATURE-MATRIX.md with results
6. Submit PR with tests + implementation

### Good First Issues
- Attribute handling (Phase 34)
- Error message improvements (Phase 34)
- Constant folding for simple expressions (Phase 38)
- Documentation improvements (Phase 42)

### Advanced Contributions
- Template metaprogramming (Phase 35)
- Lambda improvements (Phase 37)
- Exception handling edge cases (Phase 40)

---

## Conclusion

This roadmap is **ambitious but realistic**. It acknowledges architectural limitations while targeting practical improvements. The goal is not 100% C++23 support (impossible), but **maximum utility for real-world C++ → C transpilation**.

### Key Takeaways
1. **Phases 34-36 are highest priority**: Fix bugs, improve templates, enhance type system
2. **Phases 37-40 are incremental improvements**: Lambdas, constexpr, operators, exceptions
3. **Phases 41-43 are polish**: RTTI, docs, real-world testing
4. **Some C++23 features will never be supported**: Document and accept this reality
5. **Success is measured by practical utility**, not feature count

---

## Related Documents

- **[FEATURE-MATRIX.md](FEATURE-MATRIX.md)**: Current feature support status
- **[GAPS.md](GAPS.md)**: Known limitations and architectural constraints
- **[README.md](../README.md)**: Validation suite overview
- **Phase 33 Plan**: `.planning/phases/33-cpp23-validation-suite/33-01-PLAN.md`

---

**Document Version**: 1.0
**Created**: December 24, 2025
**Maintained By**: Transpiler Development Team
**Status**: Living Document (update as phases complete)
**Next Review**: After Phase 34 completion
