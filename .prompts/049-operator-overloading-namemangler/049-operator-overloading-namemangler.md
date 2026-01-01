# Prompt: Implement Unified Operator Name Mangling in NameMangler (Phase 53)

## Objective

Extend `NameMangler` to properly support C++ operator overloading with deterministic, OverloadRegistry-integrated name mangling. This fixes the critical gap where operator methods produce invalid C identifiers and ensures all operators follow the established dispatcher/handler framework.

## Context

### Current State Analysis

**Problem**: NameMangler produces invalid C identifiers for operators by directly concatenating raw operator symbols:
- `Array::operator[]` → `Array_operator[]` (INVALID - contains brackets)
- `Functor::operator()` → `Array_operator()` (INVALID - contains parentheses)
- `SmartPtr::operator->` → `SmartPtr_operator->` (INVALID - contains arrow)

**Root Cause** (NameMangler.cpp:269):
```cpp
mangledName += Parent->getName().str() + "_" + MD->getNameAsString();
```

`getNameAsString()` returns raw symbols like `"operator[]"`, `"operator()"` without sanitization.

**Workarounds**:
- `SpecialOperatorTranslator::generateConversionName()` has custom sanitization for conversion operators
- Other operators would produce invalid identifiers (not currently detected in tests)
- Three separate `m_methodMap` caches across translator classes

### Architecture Framework

**Established Pattern** (from Phase 3 refactoring):
```cpp
cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
NameMangler mangler(cppASTContext, registry);
std::string mangledName = mangler.mangleXXX(declaration);
```

**Dispatcher Framework**:
- `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/*.cpp`
- All handlers delegate name mangling to NameMangler
- Stateless, self-contained translations
- Chain of Responsibility pattern

### Operator Categories

**Currently Handled by 3 Translators**:
1. **SpecialOperatorTranslator** (12 operators):
   - Instance access: `[]`, `()`
   - Smart pointers: `->`, `*`
   - Stream I/O: `<<`, `>>`
   - Conversion: `operator T()`, `operator bool()`
   - Assignment: `=` (copy/move)
   - Rare: `&`, `,`

2. **ArithmeticOperatorTranslator** (11 operators):
   - Binary: `+`, `-`, `*`, `/`, `%`
   - Unary: `-`, `+`, `++` (prefix/postfix), `--` (prefix/postfix)
   - Bitwise: `~`, `&`, `|`, `^`, `<<`, `>>`

3. **ComparisonOperatorTranslator** (6 operators):
   - Relational: `<`, `<=`, `>`, `>=`, `==`, `!=`

**Total**: 29 operators across 3 translators, all need proper name mangling

## Requirements

### 1. Add Operator Sanitization to NameMangler

**File**: `src/NameMangler.cpp`

**New method** (add after `mangleStandaloneFunction`):
```cpp
std::string NameMangler::sanitizeOperatorName(clang::OverloadedOperatorKind Op) {
    // Convert operator kind to valid C identifier suffix
    // Pattern: operator+ → operator_plus, operator[] → operator_subscript
    switch (Op) {
        case clang::OO_Plus:           return "operator_plus";
        case clang::OO_Minus:          return "operator_minus";
        case clang::OO_Star:           return "operator_star";           // Dereference or multiplication
        case clang::OO_Slash:          return "operator_divide";
        case clang::OO_Percent:        return "operator_modulo";
        case clang::OO_Caret:          return "operator_xor";
        case clang::OO_Amp:            return "operator_amp";            // Address-of or bitwise AND
        case clang::OO_Pipe:           return "operator_pipe";
        case clang::OO_Tilde:          return "operator_tilde";
        case clang::OO_Exclaim:        return "operator_not";
        case clang::OO_Equal:          return "operator_assign";
        case clang::OO_Less:           return "operator_less";
        case clang::OO_Greater:        return "operator_greater";
        case clang::OO_PlusEqual:      return "operator_plus_assign";
        case clang::OO_MinusEqual:     return "operator_minus_assign";
        case clang::OO_StarEqual:      return "operator_multiply_assign";
        case clang::OO_SlashEqual:     return "operator_divide_assign";
        case clang::OO_PercentEqual:   return "operator_modulo_assign";
        case clang::OO_CaretEqual:     return "operator_xor_assign";
        case clang::OO_AmpEqual:       return "operator_and_assign";
        case clang::OO_PipeEqual:      return "operator_or_assign";
        case clang::OO_LessLess:       return "operator_left_shift";    // Stream << or bitwise
        case clang::OO_GreaterGreater: return "operator_right_shift";   // Stream >> or bitwise
        case clang::OO_LessLessEqual:  return "operator_left_shift_assign";
        case clang::OO_GreaterGreaterEqual: return "operator_right_shift_assign";
        case clang::OO_EqualEqual:     return "operator_equal";
        case clang::OO_ExclaimEqual:   return "operator_not_equal";
        case clang::OO_LessEqual:      return "operator_less_equal";
        case clang::OO_GreaterEqual:   return "operator_greater_equal";
        case clang::OO_Spaceship:      return "operator_spaceship";     // C++20 <=>
        case clang::OO_AmpAmp:         return "operator_and";
        case clang::OO_PipePipe:       return "operator_or";
        case clang::OO_PlusPlus:       return "operator_increment";
        case clang::OO_MinusMinus:     return "operator_decrement";
        case clang::OO_Comma:          return "operator_comma";
        case clang::OO_ArrowStar:      return "operator_arrow_star";    // Rare: ->*
        case clang::OO_Arrow:          return "operator_arrow";
        case clang::OO_Call:           return "operator_call";
        case clang::OO_Subscript:      return "operator_subscript";
        case clang::OO_Conditional:    return "operator_conditional";   // C++23: operator?:
        case clang::OO_Coawait:        return "operator_coawait";       // C++20 coroutines
        default:
            return "operator_unknown";
    }
}
```

**Update `mangleMethodName()`** (line 241-272):
```cpp
std::string NameMangler::mangleMethodName(CXXMethodDecl *MD) {
    // Check if parent is valid (can be null in some edge cases)
    CXXRecordDecl* Parent = MD->getParent();
    if (!Parent) {
        llvm::errs() << "WARNING: CXXMethodDecl has null parent, using method name only: "
                     << MD->getNameAsString() << "\\n";
        return MD->getNameAsString();
    }

    // Extract namespace hierarchy
    std::vector<std::string> namespaces = extractNamespaceHierarchy(Parent);

    // Build mangled name: ns1_ns2_ClassName_methodName
    std::string mangledName;
    for (const auto &ns : namespaces) {
        mangledName += ns + "_";
    }

    // PHASE 53: Handle operator methods with proper sanitization
    std::string methodName;
    if (MD->isOverloadedOperator()) {
        // Use sanitized operator name instead of raw symbols
        methodName = sanitizeOperatorName(MD->getOverloadedOperator());

        // Add prefix/postfix distinguisher for ++ and --
        if (MD->getOverloadedOperator() == clang::OO_PlusPlus ||
            MD->getOverloadedOperator() == clang::OO_MinusMinus) {
            // Postfix has dummy int parameter
            if (MD->getNumParams() > 0) {
                methodName += "_postfix";
            } else {
                methodName += "_prefix";
            }
        }
    } else {
        // Regular method - use getNameAsString() as before
        methodName = MD->getNameAsString();
    }

    mangledName += Parent->getName().str() + "_" + methodName;

    return mangledName;
}
```

### 2. Add Conversion Operator Support

**File**: `src/NameMangler.cpp`

**New method**:
```cpp
std::string NameMangler::mangleConversionOperator(clang::CXXConversionDecl *CD) {
    // Phase 53: Mangle conversion operators with proper type encoding
    // Pattern: ClassName_operator_to_TargetType[_const]

    CXXRecordDecl* Parent = CD->getParent();
    if (!Parent) {
        return "operator_to_unknown";
    }

    // Extract namespace hierarchy
    std::vector<std::string> namespaces = extractNamespaceHierarchy(Parent);

    // Build class name with namespace prefix
    std::string mangledName;
    for (const auto &ns : namespaces) {
        mangledName += ns + "_";
    }
    mangledName += Parent->getName().str();

    // Get conversion target type
    QualType ConvType = CD->getConversionType();
    std::string targetTypeName = getSimpleTypeName(ConvType);

    // Build conversion operator name
    mangledName += "_operator_to_" + targetTypeName;

    // Add const qualifier if present
    if (CD->isConst()) {
        mangledName += "_const";
    }

    // Register with OverloadRegistry
    std::string baseName = Parent->getName().str() + "_operator_to";
    registry_.registerOverload(baseName, CD, mangledName);

    return mangledName;
}
```

**Update header** (`include/NameMangler.h`):
```cpp
class NameMangler {
public:
    // ... existing methods ...

    /**
     * @brief Mangle conversion operator (operator T()) to C function name
     * @param CD Conversion operator declaration
     * @return Mangled name (e.g., "String_operator_to_int_const")
     *
     * Phase 53: Operator Overloading Support
     * Translates C++ conversion operators to valid C identifiers.
     * Pattern: ClassName_operator_to_TargetType[_const]
     */
    std::string mangleConversionOperator(clang::CXXConversionDecl *CD);

private:
    /**
     * @brief Sanitize operator kind to valid C identifier
     * @param Op Operator kind from Clang AST
     * @return Sanitized operator name (e.g., "operator_plus", "operator_subscript")
     *
     * Phase 53: Operator Overloading Support
     * Converts operator symbols to valid C identifiers.
     */
    std::string sanitizeOperatorName(clang::OverloadedOperatorKind Op);
};
```

### 3. Update SpecialOperatorTranslator to Use NameMangler

**File**: `src/SpecialOperatorTranslator.cpp`

**Remove custom name generation** (lines 776-818):
```cpp
// PHASE 53: Remove generateOperatorName() and generateConversionName()
// Now delegated to NameMangler

// DELETE:
// std::string SpecialOperatorTranslator::generateOperatorName(const CXXMethodDecl* MD)
// std::string SpecialOperatorTranslator::generateConversionName(const CXXConversionDecl* CD)
```

**Update method translation** (example: line 57):
```cpp
// OLD:
// std::string FnName = generateOperatorName(MD);

// NEW:
std::string FnName = m_mangler.mangleMethodName(const_cast<CXXMethodDecl*>(MD));
```

**Update conversion translation** (around line 139):
```cpp
// OLD:
// std::string FnName = generateConversionName(CD);

// NEW:
std::string FnName = m_mangler.mangleConversionOperator(const_cast<CXXConversionDecl*>(CD));
```

### 4. Extend mangleName() to Use sanitizeOperatorName()

**File**: `src/NameMangler.cpp`

**Update `mangleName()`** (lines 24-47):
```cpp
std::string NameMangler::mangleName(CXXMethodDecl *MD) {
    // Phase 2: Registry-backed mangling for cross-file consistency

    // Phase 53: Handle operator methods
    std::string baseName;
    if (MD->isOverloadedOperator()) {
        // Use sanitized operator name
        std::string operatorName = sanitizeOperatorName(MD->getOverloadedOperator());
        baseName = MD->getParent()->getName().str() + "_" + operatorName;
    } else {
        // Regular method
        baseName = MD->getParent()->getName().str() + "_" + MD->getName().str();
    }

    // Always append parameter types for cross-file consistency
    std::string mangledName = baseName;
    for (ParmVarDecl *Param : MD->parameters()) {
        std::string paramType = getSimpleTypeName(Param->getType());
        mangledName += "_" + paramType;
    }

    // If no parameters, use base name
    if (MD->param_size() == 0) {
        mangledName = baseName;
    }

    // Phase 53: Add prefix/postfix distinguisher for increment/decrement
    if (MD->isOverloadedOperator() &&
        (MD->getOverloadedOperator() == clang::OO_PlusPlus ||
         MD->getOverloadedOperator() == clang::OO_MinusMinus)) {
        if (MD->getNumParams() > 0) {
            mangledName += "_postfix";
        } else {
            mangledName += "_prefix";
        }
    }

    // Register with global registry for cross-file tracking
    registry_.registerOverload(baseName, MD, mangledName);

    return mangledName;
}
```

## Implementation Strategy

### Phase 1: Add Operator Sanitization (Foundation)

**Tasks**:
1. Add `sanitizeOperatorName()` to NameMangler (covers all 40+ Clang operators)
2. Write unit tests for operator name sanitization
3. Verify invalid chars (brackets, arrows, symbols) are eliminated

**Test Cases** (create `tests/unit/NameManglerOperatorTest.cpp`):
```cpp
TEST(NameManglerOperatorTest, SanitizeOperatorSubscript) {
    // operator[] → "operator_subscript"
    EXPECT_EQ(sanitizeOperatorName(OO_Subscript), "operator_subscript");
}

TEST(NameManglerOperatorTest, SanitizeOperatorCall) {
    // operator() → "operator_call"
    EXPECT_EQ(sanitizeOperatorName(OO_Call), "operator_call");
}

TEST(NameManglerOperatorTest, SanitizeOperatorArrow) {
    // operator-> → "operator_arrow"
    EXPECT_EQ(sanitizeOperatorName(OO_Arrow), "operator_arrow");
}

// ... test all 40+ operators
```

### Phase 2: Integrate Operators into mangleName()

**Tasks**:
1. Update `mangleName()` to detect operator methods via `isOverloadedOperator()`
2. Call `sanitizeOperatorName()` for operators
3. Handle prefix/postfix increment/decrement
4. Ensure OverloadRegistry integration works

**Test Cases**:
```cpp
TEST(NameManglerOperatorTest, MangleOperatorPlus) {
    // Vector::operator+(const Vector&) → "Vector_operator_plus_const_Vector_ref"
}

TEST(NameManglerOperatorTest, MangleOperatorPlusPlusPrefix) {
    // Iterator::operator++() → "Iterator_operator_increment_prefix"
}

TEST(NameManglerOperatorTest, MangleOperatorPlusPlusPostfix) {
    // Iterator::operator++(int) → "Iterator_operator_increment_postfix_int"
}
```

### Phase 3: Add Conversion Operator Support

**Tasks**:
1. Add `mangleConversionOperator()` method
2. Use `getSimpleTypeName()` for target type encoding
3. Register with OverloadRegistry

**Test Cases**:
```cpp
TEST(NameManglerOperatorTest, MangleConversionToBool) {
    // String::operator bool() const → "String_operator_to_bool_const"
}

TEST(NameManglerOperatorTest, MangleConversionToInt) {
    // Celsius::operator int() → "Celsius_operator_to_int"
}
```

### Phase 4: Update SpecialOperatorTranslator

**Tasks**:
1. Remove `generateOperatorName()` and `generateConversionName()`
2. Replace all calls with `m_mangler.mangleMethodName()` and `m_mangler.mangleConversionOperator()`
3. Run all SpecialOperatorTranslator tests
4. Verify no regressions

**Verification**:
```bash
ctest -R SpecialOperator -V
# All 14 tests should pass
```

### Phase 5: Dispatcher Integration (Future Enhancement)

**Goal**: Make operator translators accessible via dispatcher

**Current Limitation** (from CXXOperatorCallExprHandler.cpp:8):
> "SpecialOperatorTranslator requires CNodeBuilder and NameMangler (not available in dispatcher)"

**Solution**:
1. Add `CNodeBuilder` and `NameMangler` to dispatcher context
2. Create unified `OperatorHandler` that wraps all three translators
3. Register with dispatcher for `CXXOperatorCallExpr` nodes
4. Follow same pattern as `StaticMethodHandler` and `InstanceMethodHandler`

**Benefits**:
- Stateless operator translation
- Dispatcher handles recursion automatically
- Consistent with Phase 3 architecture
- Eliminates need for three separate translator classes

## Success Criteria

1. **No invalid C identifiers**: All operator methods produce valid C function names
2. **All 40+ operators supported**: Complete coverage of Clang's `OverloadedOperatorKind` enum
3. **OverloadRegistry integration**: All operators registered for cross-file consistency
4. **Prefix/postfix handled**: `++` and `--` distinguished correctly
5. **Conversion operators work**: `operator T()` produces deterministic names
6. **All tests pass**: No regressions in existing operator translator tests
7. **Documentation updated**: Header comments reflect Phase 53 changes
8. **Code removed**: Custom name generation logic deleted from SpecialOperatorTranslator

## Testing Strategy

### Unit Tests
- `tests/unit/NameManglerOperatorTest.cpp` - Test all 40+ operator sanitization
- Extend `tests/NameManglerTest.cpp` - Test operator method mangling

### Integration Tests
- `tests/SpecialOperatorTranslatorTest.cpp` - Verify translators use NameMangler
- `tests/ArithmeticOperatorTranslatorTest.cpp` - Verify arithmetic operators work
- `tests/ComparisonOperatorTranslatorTest.cpp` - Verify comparison operators work

### Regression Tests
- Run all dispatcher tests: `ctest -R Dispatcher`
- Run all operator tests: `ctest -R Operator`
- Verify 100% pass rate

## Files to Modify

### Core Implementation
- `src/NameMangler.cpp` - Add operator sanitization and conversion support
- `include/NameMangler.h` - Add new method declarations

### Operator Translators
- `src/SpecialOperatorTranslator.cpp` - Remove custom name generation
- `include/SpecialOperatorTranslator.h` - Update interface

### Tests (New)
- `tests/unit/NameManglerOperatorTest.cpp` - Operator sanitization tests

### Tests (Update)
- `tests/NameManglerTest.cpp` - Add operator mangling tests
- `tests/SpecialOperatorTranslatorTest.cpp` - Verify NameMangler integration

## Expected Outcomes

### Before Phase 53
```cpp
// C++
class Array {
    int& operator[](int i);
};

// Generated C (INVALID)
int* Array_operator[](struct Array* this, int i);  // ❌ Contains brackets
```

### After Phase 53
```cpp
// C++
class Array {
    int& operator[](int i);
};

// Generated C (VALID)
int* Array_operator_subscript(struct Array* this, int i);  // ✅ Valid C identifier
```

### Naming Examples

| C++ Operator | Current (Invalid) | Phase 53 (Valid) |
|--------------|------------------|------------------|
| `operator[]` | `Array_operator[]` | `Array_operator_subscript` |
| `operator()` | `Functor_operator()` | `Functor_operator_call` |
| `operator->` | `SmartPtr_operator->` | `SmartPtr_operator_arrow_const` |
| `operator*` | `SmartPtr_operator*` | `SmartPtr_operator_star_const` |
| `operator++` (prefix) | `Iterator_operator++` | `Iterator_operator_increment_prefix` |
| `operator++` (postfix) | `Iterator_operator++` | `Iterator_operator_increment_postfix_int` |
| `operator bool()` | `String_operator` | `String_operator_to_bool_const` |
| `operator int()` | `Celsius_operator` | `Celsius_operator_to_int` |

## Architecture Compliance

### SOLID Principles
- ✅ **Single Responsibility**: NameMangler handles all name mangling (including operators)
- ✅ **Open/Closed**: Extend via `sanitizeOperatorName()` switch, don't modify existing
- ✅ **Liskov Substitution**: `mangleName()` works for all CXXMethodDecl (operators or not)
- ✅ **Interface Segregation**: SpecialOperatorTranslator uses only what it needs from NameMangler
- ✅ **Dependency Inversion**: Depends on NameMangler abstraction, not implementation details

### Pipeline Separation (3 Stages)
- ✅ **Stage 1** (Clang): Parse C++ into C++ AST
- ✅ **Stage 2** (CppToCVisitor): Transform C++ AST to C AST with proper naming
- ✅ **Stage 3** (CodeGenerator): Emit C source from C AST (no translation decisions)

### Pattern Consistency
Follows Phase 3 pattern established for all handlers:
```cpp
cpptoc::OverloadRegistry& registry = cpptoc::OverloadRegistry::getInstance();
NameMangler mangler(cppASTContext, registry);
std::string mangledName = mangler.mangleXXX(declaration);
```

## Risks and Mitigations

| Risk | Impact | Mitigation |
|------|--------|-----------|
| Breaking existing operator tests | High | Run full test suite before/after |
| Naming conflicts with existing code | Medium | Use OverloadRegistry conflict detection |
| Prefix/postfix detection fails | Medium | Test both variants explicitly |
| Conversion operator type encoding issues | Medium | Reuse `getSimpleTypeName()` (proven) |
| Performance impact from operator checks | Low | `isOverloadedOperator()` is O(1) flag check |

## Future Enhancements

1. **Dispatcher Integration**: Make translators accessible via dispatcher context
2. **Unified OperatorHandler**: Single handler for all operator types
3. **Operator Kind Metadata**: Store operator kind in OverloadRegistry for debugging
4. **Performance Optimization**: Cache sanitized names for frequent operators
5. **Custom Operator Names**: Allow users to override default naming via config

## References

- **Phase 3 Refactoring**: Established NameMangler + OverloadRegistry pattern
- **Operator Translator Docs**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/.planning/phases/50-arithmetic-operators/PHASE50-PLAN.md`
- **Special Operator Docs**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/.planning/phases/52-special-operators/PHASE52-PLAN.md`
- **Dispatcher Architecture**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/dispatch/*.cpp`
- **NameMangler Implementation**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/NameMangler.cpp`

---

**This prompt was generated via `/taches-cc-resources:create-meta-prompt` on 2025-12-29**
**Working directory**: `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c`
**Phase**: 53 (Operator Overloading NameMangler Integration)
