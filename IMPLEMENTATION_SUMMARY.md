# AST-Based Template Monomorphization Implementation

## Overview
Successfully implemented AST-based template monomorphization in TemplateMonomorphizer.cpp, migrating from string-based code generation to Clang AST node creation.

## Changes Made

### 1. TemplateMonomorphizer.cpp (Complete Rewrite)
**Location:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/TemplateMonomorphizer.cpp`

#### Constructor Update
- Added `CNodeBuilder& Builder` parameter
- Now accepts: `TemplateMonomorphizer(ASTContext&, NameMangler&, CNodeBuilder&)`

#### New AST-Based Methods

**monomorphizeClass(ClassTemplateSpecializationDecl* D) -> RecordDecl***
- Returns C struct AST node instead of string
- Uses `CNodeBuilder.structDecl()` for clean AST creation
- Automatically adds to C TranslationUnit

**monomorphizeClassMethods(ClassTemplateSpecializationDecl* D, RecordDecl* CStruct) -> vector<FunctionDecl*>**
- NEW method for generating method functions separately
- Returns vector of C function AST nodes
- Handles 'this' pointer injection for methods

**monomorphizeFunction(FunctionDecl* D) -> FunctionDecl***
- Returns C function AST node instead of string
- Uses `CNodeBuilder.funcDecl()` for parameter creation
- Proper type substitution from template arguments

#### Private Helper Methods

**createStruct(ClassTemplateSpecializationDecl*, string&) -> RecordDecl***
- Creates C struct with fields from template class
- Follows CppToCVisitor::VisitCXXRecordDecl pattern
- Uses CNodeBuilder for clean field creation

**createMethodFunction(CXXMethodDecl*, string&, TemplateArgumentList&) -> FunctionDecl***
- Creates C function from C++ method
- Injects 'this' pointer as first parameter
- Handles template type substitution

#### Unchanged Methods
- `generateMangledName()` - Name mangling logic preserved
- `typeToIdentifierString()` - Type conversion preserved
- `substituteType()` - Future enhancement hook

#### Deprecated Code
- Old string generation methods commented out with `#if 0`
- Marked as deprecated with TODO for removal
- Kept temporarily for reference

### 2. CppToCVisitor.cpp Updates
**Location:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCVisitor.cpp`

#### Constructor Change (Line 79-80)
```cpp
// OLD:
m_templateMonomorphizer = std::make_unique<TemplateMonomorphizer>(Context, Mangler);

// NEW:
m_templateMonomorphizer = std::make_unique<TemplateMonomorphizer>(Context, Mangler, Builder);
```

#### processTemplateInstantiations() Refactor (Lines 2876-2938)
**Before:** Generated string-based code to `m_monomorphizedCode`
**After:** Generates AST nodes, adds to C_TranslationUnit

Key changes:
- Removed `std::ostringstream codeStream`
- Call `monomorphizeClass()` to get `RecordDecl*`
- Call `monomorphizeClassMethods()` to get method functions
- Call `monomorphizeFunction()` to get `FunctionDecl*`
- AST nodes automatically added by CNodeBuilder
- Removed string output (`llvm::outs() << m_monomorphizedCode`)

### 3. Test Updates
**Location:** `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/TemplateIntegrationTest.cpp`

- Added `#include "../include/CNodeBuilder.h"`
- Updated constructor calls to include `CNodeBuilder builder(AST->getASTContext())`
- Changed assertions from string checks to AST node checks
- All 15 tests passing

## Design Principles Applied

### SOLID
- **Single Responsibility:** TemplateMonomorphizer only handles monomorphization
- **Open/Closed:** Easy to extend with new template features
- **Dependency Inversion:** Depends on CNodeBuilder abstraction

### KISS
- Simple, clear method names
- Reused existing CNodeBuilder patterns
- One method = one clear purpose

### DRY
- Reused CNodeBuilder methods instead of duplicate AST construction
- Followed existing VisitCXXRecordDecl pattern

### YAGNI
- Only implemented what's needed for template monomorphization
- Kept helper methods minimal and focused

## Verification

### Build Status
✅ cpptoc builds successfully
✅ All tests compile without errors
✅ No warnings introduced

### Test Results
✅ All 15 TemplateIntegrationTest tests passing:
- SimpleClassTemplateInstantiation
- TemplateFunctionMultipleInstantiations
- ExplicitInstantiation
- ImplicitInstantiation
- NestedTemplateInstantiation
- FullTemplateSpecialization
- PartialTemplateSpecialization
- TemplateFunctionCallingTemplateClass
- DeduplicationSameTemplateSameArgs
- TemplateFriendFunction
- DependentTypeResolution
- ComplexTemplateHierarchy
- TemplateInstantiationTrackerBasics
- NonTypeTemplateParameters
- VariadicTemplate

### Integration Test
Tested with real C++ template code:
```cpp
template<typename T>
class Stack {
    T data[10];
    int top;
public:
    void push(T val);
    T pop();
};

int main() {
    Stack<int> s1;
    Stack<double> s2;
    // ...
}
```

Generated correct monomorphized structs:
- `Stack_int` with `int data[10]`
- `Stack_double` with `double data[10]`
- Method functions: `Stack_int_push`, `Stack_int_pop`, etc.

## Files Modified
1. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/TemplateMonomorphizer.cpp` (complete rewrite)
2. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/src/CppToCVisitor.cpp` (constructor + processTemplateInstantiations)
3. `/Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/tests/TemplateIntegrationTest.cpp` (test updates)

## Next Steps
1. Remove deprecated string generation methods (marked with `#if 0`)
2. Add more comprehensive integration tests for edge cases
3. Performance profiling of AST generation vs string generation
4. Update documentation to reflect AST-based approach

## Summary
Successfully migrated TemplateMonomorphizer from string-based code generation to AST-based generation, following SOLID/KISS/DRY/YAGNI principles. All tests passing, integration verified with real template code.
