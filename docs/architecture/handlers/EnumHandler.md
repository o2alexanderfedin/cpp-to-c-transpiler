# EnumHandler Specification

## Responsibility

Translate C++ enum declarations (both scoped and unscoped) to C enum declarations, applying name prefixing for scoped enums to maintain scope.

## AST Nodes Processed

- `clang::EnumDecl` - Enum declaration (scoped or unscoped)
- `clang::EnumConstantDecl` - Individual enum constants
- `clang::DeclRefExpr` - References to enum constants (via ExpressionHandler)

## Translation Strategy

### Unscoped Enums (C-compatible)
```cpp
// C++
enum Color { Red, Green, Blue };

// C (direct mapping)
enum Color { Red, Green, Blue };
```

**Translation**: Direct 1:1 mapping - same syntax in C.

### Scoped Enums (C++ only)
```cpp
// C++
enum class State { Idle, Running, Stopped };

// C (with prefixing)
enum State { State__Idle, State__Running, State__Stopped };
```

**Translation**:
1. Remove `class` keyword (C doesn't support it)
2. Prefix each constant with `EnumName__`
3. Store mapping: `C++ EnumConstantDecl` → `C EnumConstantDecl`

## Dependencies

- **CNodeBuilder**: Create C `EnumDecl` and `EnumConstantDecl` nodes
- **HandlerContext**: Store enum constant mappings for later reference lookup
- **ExpressionHandler**: Translate enum constant references using the mapping

## Algorithm

### Processing EnumDecl

```
1. Determine if enum is scoped (ED->isScoped())

2. Create C EnumDecl with same name:
   C_Enum = builder.createEnumDecl(ED->getNameAsString())

3. For each enumerator in ED->enumerators():
   a. Get name and value
   b. If scoped:
        newName = EnumName + "__" + ConstantName
      Else:
        newName = ConstantName
   c. Create C EnumConstantDecl:
        C_Constant = builder.createEnumConstantDecl(newName, value)
   d. Add to C_Enum
   e. If scoped:
        context.registerEnumConstant(CPP_Constant, C_Constant)

4. Return C_Enum
```

### Processing Enum Constant References

Handled by `ExpressionHandler`, but uses mapping from this handler:

```
1. Given DeclRefExpr pointing to C++ EnumConstantDecl
2. Lookup in context.enumConstantMap
3. Create new DeclRefExpr pointing to C EnumConstantDecl
4. Return translated expression
```

## C++ Example

```cpp
// Input: C++
enum class GameState {
    Menu,
    Playing = 10,
    Paused,
    GameOver
};

GameState getCurrentState() {
    return GameState::Menu;
}

bool isPlaying(GameState state) {
    return state == GameState::Playing;
}
```

## C Example

```c
// Output: C
enum GameState {
    GameState__Menu = 0,
    GameState__Playing = 10,
    GameState__Paused = 11,
    GameState__GameOver = 12
};

enum GameState getCurrentState(void) {
    return GameState__Menu;
}

int isPlaying(enum GameState state) {
    return state == GameState__Playing;
}
```

## Implementation Details

### Enum Constant Mapping Storage

```cpp
// In HandlerContext
std::map<const EnumConstantDecl*, EnumConstantDecl*> enumConstantMap;

void registerEnumConstant(const EnumConstantDecl* cpp, EnumConstantDecl* c) {
    enumConstantMap[cpp] = c;
}

EnumConstantDecl* lookupEnumConstant(const EnumConstantDecl* cpp) {
    auto it = enumConstantMap.find(cpp);
    return (it != enumConstantMap.end()) ? it->second : nullptr;
}
```

### Name Generation

```cpp
std::string generateEnumConstantName(const EnumDecl* ED, const EnumConstantDecl* ECD) {
    if (ED->isScoped()) {
        return ED->getNameAsString() + "__" + ECD->getNameAsString();
    } else {
        return ECD->getNameAsString();
    }
}
```

## Test Cases

### Test 1: Unscoped Enum
**Input**:
```cpp
enum Color { Red, Green, Blue };
Color c = Red;
```

**Expected**:
```c
enum Color { Red, Green, Blue };
enum Color c = Red;
```

### Test 2: Scoped Enum
**Input**:
```cpp
enum class State { Idle, Running };
State s = State::Idle;
```

**Expected**:
```c
enum State { State__Idle, State__Running };
enum State s = State__Idle;
```

### Test 3: Scoped Enum in Switch
**Input**:
```cpp
enum class Status { OK, Error };

int handle(Status s) {
    switch (s) {
        case Status::OK:
            return 0;
        case Status::Error:
            return 1;
    }
    return -1;
}
```

**Expected**:
```c
enum Status { Status__OK, Status__Error };

int handle(enum Status s) {
    switch (s) {
        case Status__OK:
            return 0;
        case Status__Error:
            return 1;
    }
    return -1;
}
```

### Test 4: Explicit Values
**Input**:
```cpp
enum class Priority { Low = 1, Medium = 5, High = 10 };
```

**Expected**:
```c
enum Priority { Priority__Low = 1, Priority__Medium = 5, Priority__High = 10 };
```

### Test 5: Enum as Function Parameter
**Input**:
```cpp
enum class Mode { Read, Write };
void setMode(Mode m);
```

**Expected**:
```c
enum Mode { Mode__Read, Mode__Write };
void setMode(enum Mode m);
```

## Edge Cases

### Mixed Scoped and Unscoped
```cpp
enum Color { Red, Green };
enum class State { Idle, Running };

// C output
enum Color { Red, Green };           // No prefix
enum State { State__Idle, State__Running };  // With prefix
```

### Nested Enums (in classes)
```cpp
class Foo {
public:
    enum class Status { OK, Error };
};

// Handled by RecordHandler + EnumHandler
// Result: enum Foo__Status { Foo__Status__OK, Foo__Status__Error };
```

### Forward Declarations
```cpp
enum class State;  // Forward declaration

// C doesn't support enum forward declarations - skip or error
```

## Integration with Other Handlers

### ExpressionHandler Integration

When `ExpressionHandler` encounters a `DeclRefExpr` to an enum constant:

```cpp
Expr* ExpressionHandler::handleDeclRefExpr(DeclRefExpr* E, HandlerContext& ctx) {
    Decl* D = E->getDecl();

    if (EnumConstantDecl* ECD = dyn_cast<EnumConstantDecl>(D)) {
        // Lookup translated enum constant
        EnumConstantDecl* C_ECD = ctx.lookupEnumConstant(ECD);
        if (C_ECD) {
            return ctx.builder.createDeclRefExpr(C_ECD);
        }
    }

    // ... handle other decl types
}
```

### TypeHandler Integration

Enum types need proper translation:

```cpp
QualType TypeHandler::translateType(QualType T, HandlerContext& ctx) {
    if (const EnumType* ET = T->getAs<EnumType>()) {
        EnumDecl* CPP_Enum = ET->getDecl();
        EnumDecl* C_Enum = ctx.lookupDecl<EnumDecl>(CPP_Enum);
        return ctx.cContext.getEnumType(C_Enum);
    }
    // ... handle other types
}
```

## Performance Considerations

- Enum constant mapping is O(1) lookup (hash map)
- All enum constants registered during `EnumDecl` processing
- No need to re-process enum constants later

## Future Enhancements

### Enum Class with Underlying Type
```cpp
enum class Status : uint8_t { OK, Error };

// C99 doesn't support underlying type specification
// C23 might - check and use if available
```

### Type-Safe Enums
Could optionally generate type-safe wrappers:
```c
typedef enum Status { Status__OK, Status__Error } Status;
```

## Summary

**Complexity**: Level 2 (Simple transformation)

**Key Points**:
- Unscoped enums: direct mapping
- Scoped enums: prefix with `EnumName__`
- Store mapping for reference translation
- Integrate with ExpressionHandler for references

**Testing Focus**:
- Verify prefix application for scoped enums
- Verify no prefix for unscoped enums
- Test enum constant references in expressions
- Test enum constants in switch cases
