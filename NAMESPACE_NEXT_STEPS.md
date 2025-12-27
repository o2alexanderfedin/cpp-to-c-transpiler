# Namespace Support - Action Items

## Current State
- 70% namespace support implemented and stable
- Production-ready for basic namespaces (single, nested, classes, methods)
- 5 tests passing, covering main use cases
- Integrated throughout transpiler pipeline (Stage 2 & 3)

---

## Immediate Actions (Next Sprint)

### 1. Documentation (2-3 hours)
**Priority:** HIGH - Unblocks users

**Tasks:**
- [ ] Create `docs/NAMESPACE_GUIDE.md`
  - What's supported (with examples)
  - What's not supported (with workarounds)
  - Naming convention explanation
  - Common patterns

- [ ] Add namespace section to `docs/TRANSPILABLE_CPP.md`
  - Update existing section with implementation notes
  - Reference the NAMESPACE_GUIDE.md

- [ ] Create FAQ document `docs/NAMESPACE_FAQ.md`
  - Q: Why is my namespace function called "ns_func"?
  - Q: Can I use "using namespace"?
  - Q: What about anonymous namespaces?
  - Q: How do I hide internal APIs?

**Definition of Done:**
- [ ] 3 new documents created
- [ ] Examples compile and transpile
- [ ] No linter warnings
- [ ] Linked from main README

---

### 2. Test Enhancement (1-2 hours)
**Priority:** MEDIUM - Improves coverage

**Add to `tests/NameManglerTest.cpp`:**

```cpp
TEST_F(NameManglerTest, ExternCInNamespace) {
    // extern "C" prevents mangling even in namespace
}

TEST_F(NameManglerTest, NamespacedSccopedEnum) {
    // namespace ns { enum class E { A, B }; }
    // Should produce: ns_E__A, ns_E__B
}

TEST_F(NameManglerTest, DeepNesting) {
    // Test 6-level deep namespace nesting
}

TEST_F(NameManglerTest, OverloadedNamespacedFunc) {
    // ns::func(int), ns::func(double)
    // Should produce: ns_func_int, ns_func_double
}

TEST_F(NameManglerTest, StaticMethodInNamespace) {
    // namespace ns { class C { static void m(); }; }
    // Should produce: ns_C_m (no this parameter)
}
```

**Definition of Done:**
- [ ] All 5 new tests pass
- [ ] Increase test coverage to 95%+
- [ ] No test regressions

---

### 3. Integration Verification (2 hours)
**Priority:** MEDIUM - Ensures stability

**Verify all integration points:**

- [ ] `src/CppToCVisitor.cpp`
  - Line 32: Mangler initialization ✅
  - Line 537: VisitCXXMethodDecl ✅
  - Line 682: VisitCXXConstructorDecl ✅
  - Line 919: VisitCXXDestructorDecl ✅
  - Line 1114: VisitFunctionDecl ✅

- [ ] `src/handlers/ExpressionHandler.cpp`
  - translateDeclRefExpr preserves QualifierLoc ✅

- [ ] `src/CodeGenerator.cpp`
  - Emits mangled names correctly ✅

**Definition of Done:**
- [ ] All integration points verified
- [ ] No dead code paths
- [ ] No unused NameMangler methods

---

## Short-term Actions (2-4 weeks)

### 4. Anonymous Namespace Support (4-6 hours)
**Priority:** LOW - Edge case, but complete feature

**Approach:** Use source location hash for unique IDs

**Implementation:**
```cpp
std::vector<std::string> NameMangler::extractNamespaceHierarchy(Decl *D) {
    std::vector<std::string> namespaces;
    DeclContext *DC = D->getDeclContext();

    while (DC) {
        if (auto *ND = dyn_cast<NamespaceDecl>(DC)) {
            if (!ND->isAnonymousNamespace()) {
                namespaces.push_back(ND->getName().str());
            } else {
                // Generate unique ID from namespace address or source location
                std::string uniqueId = "_anon_" + std::to_string(
                    (uintptr_t)ND / 16  // Simple hash of address
                );
                namespaces.push_back(uniqueId);
            }
        }
        DC = DC->getParent();
    }
    std::reverse(namespaces.begin(), namespaces.end());
    return namespaces;
}
```

**Testing:**
```cpp
TEST_F(NameManglerTest, AnonymousNamespace) {
    // namespace { void func(); }
    // Should produce: _anon_XXXXX_func
}
```

**Definition of Done:**
- [ ] Anonymous namespace functions generate unique names
- [ ] Anonymous namespace classes work
- [ ] Test passes
- [ ] Documentation updated

---

### 5. Scoped Enum Namespace Integration Polish (2-3 hours)
**Priority:** MEDIUM - Completes existing feature

**Current gap:** Scoped enums in namespaces may not fully respect namespace prefixing

**Verify and fix:**
- [ ] Namespace + scoped enum = both prefixes applied
  - Expected: `namespace n { enum class E { A }; }` → `n_E__A` ✅
  - Verify this works end-to-end

- [ ] DeclRefExpr to namespaced enum constants
  - Example: `GameState::Menu` in different namespace
  - Should resolve to correct `ns_GameState__Menu`

- [ ] Add test to NameManglerTest
  ```cpp
  TEST_F(NameManglerTest, NamespacedScopedEnum)
  ```

**Definition of Done:**
- [ ] Scoped enums in namespaces work correctly
- [ ] DeclRefExpr resolution verified
- [ ] E2E test passes
- [ ] No regressions in existing enum tests

---

## Long-term Actions (1-3 months)

### 6. Using Directives Support (6-8 hours)
**Priority:** LOW - Complex, uncommon in transpilable code

**Approach:** Name resolution during translation phase

**Pseudo-algorithm:**
```
For each DeclRefExpr with name "foo":
  1. If "foo" directly available → use it
  2. Else, search all active "using namespace ns"
  3. If found in exactly one → replace with "ns_foo"
  4. Else if found in multiple → error (ambiguous)
  5. Else → original resolution
```

**Risk:** High complexity, potential for name collision issues

**Recommendation:** Document as "not supported" for now, allow workaround (explicit names)

---

### 7. Namespace Aliases Support (3-4 hours)
**Priority:** LOW - Convenience feature

**Current behavior:** Clang resolves aliases internally, so may already work

**Action:**
- [ ] Test if `namespace alias = ns;` already works
- [ ] If yes, document as supported
- [ ] If no, implement alias resolution in NameMangler

**Definition of Done:**
- [ ] Aliases resolve correctly or are documented as unsupported
- [ ] Test added

---

## Documentation Roadmap

### Phase 1: User-Facing Docs (This Sprint)
- [ ] NAMESPACE_GUIDE.md - User-level documentation
- [ ] NAMESPACE_FAQ.md - Common questions
- [ ] Update TRANSPILABLE_CPP.md with implementation details

### Phase 2: Developer Docs (Next Sprint)
- [ ] Add inline comments to NameMangler.cpp explaining algorithm
- [ ] Create architecture diagram showing pipeline flow
- [ ] Document integration points

### Phase 3: Examples (Future)
- [ ] Create example transpilation: complex nested namespaces
- [ ] Demonstrate best practices
- [ ] Show workarounds for unsupported features

---

## Success Criteria

### Definition of Done (All Actions)
- [ ] No new compiler warnings
- [ ] All existing tests pass (100% regression free)
- [ ] New tests pass (95%+ code coverage)
- [ ] Documentation complete and reviewed
- [ ] Performance: no measurable impact
- [ ] Commits follow conventions
- [ ] PR reviewed before merge

### Metrics to Track
- Test coverage: Maintain > 90%
- Documentation: 3+ user-facing guides
- Integration points: 5/5 verified working
- Performance: < 1% overhead from namespace handling

---

## Effort Summary

| Task | Effort | Priority | Sprint |
|------|--------|----------|--------|
| Documentation | 2-3h | HIGH | This |
| Test Enhancement | 1-2h | MEDIUM | This |
| Integration Verify | 2h | MEDIUM | This |
| Anonymous Namespaces | 4-6h | LOW | Next |
| Scoped Enum Polish | 2-3h | MEDIUM | Next |
| Using Directives | 6-8h | LOW | Later |
| Namespace Aliases | 3-4h | LOW | Later |
| **Total** | **22-29h** | - | - |

**Estimate for reaching 90%:** 8-10 hours (docs + tests + polish)

---

## Owner Assignment

**Recommended Owner:** Claude Code (automated testing and implementation)

**Review Required:** Domain expert review before documentation release

---

## Dependencies

**Blockers:** None - all prerequisites already in place

**Related Work:**
- Epic #5: RAII implementation uses NameMangler
- Phase 8: Standalone functions use NameMangler
- Phase 35: Header separation may need namespace awareness

---

## Risk Assessment

### Risk 1: Over-engineering
**Mitigation:** Focus on 70% feature completeness, document gaps

### Risk 2: Name Collision
**Mitigation:** Well-tested mangling algorithm, comprehensive test suite

### Risk 3: Performance Regression
**Mitigation:** Profile before/after, no measurable overhead expected

### Risk 4: Breaking Changes
**Mitigation:** All changes backward compatible, versioned

---

## Questions for Project Lead

1. Should we support anonymous namespaces? (adds complexity)
2. Should we support using directives? (adds complexity, uncommon in code)
3. How much user documentation is needed vs. developer documentation?
4. Should we create example transpilations?
5. Target release version for complete namespace support?

