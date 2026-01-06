# Phase 56 Plan: Virtual Inheritance (Diamond Problem Solution)

**Phase**: 56 (Virtual Inheritance)
**Prerequisite**: Phase 46 (Multiple Inheritance) - COMPLETE
**Status**: PLANNING
**Priority**: MEDIUM (less common, but important for completeness)
**Target**: Implement C++ virtual inheritance using virtual base class tables (VTT) and virtual base pointers

## Phase Goal

Extend Phase 46's multiple inheritance support to handle virtual inheritance, solving the diamond problem. Generate virtual base class tables (VTT), virtual base pointers (vbptr), and implement shared base class instance semantics with correct offset calculations.

## Context

**Why Virtual Inheritance?**
Virtual inheritance solves the "diamond problem" where a class inherits from multiple classes that share a common base, ensuring only ONE instance of the shared base exists:

```cpp
     Animal
      /  \
   Dog    Cat
      \  /
      PetHybrid  // Single Animal instance, not two!
```

**Current State:**
- Phase 46 (Multiple Inheritance) complete: Multiple vtables, this-pointer thunks
- Phase 45 (Virtual Methods) complete: COM-style vtables with lpVtbl
- Phase 44 (Classes) complete: Class to struct transformation
- Diamond inheritance NOT supported: Would create duplicate base instances

**Phase 56 Scope:**
- Virtual base class detection
- Virtual base table (VTT) generation
- Virtual base pointer (vbptr) injection
- Shared base instance allocation
- Virtual base offset calculation
- Virtual base constructor ordering
- Virtual base destructor handling
- Diamond inheritance pattern support

**Translation Strategy:**
Virtual inheritance requires:
1. **Virtual Base Pointer (vbptr)**: Points to shared base instance
2. **Virtual Base Table (VTT)**: Contains offsets to virtual bases
3. **Single Base Instance**: Shared base allocated once, referenced by all paths
4. **Constructor Ordering**: Virtual base constructed once, before other bases
5. **Offset Indirection**: Access via vbptr + offset lookup

**Priority: MEDIUM**
- Virtual inheritance less common than regular multiple inheritance
- Critical for some design patterns: Streams, mixins, interface hierarchies
- Completes inheritance feature set
- Important for real-world C++ code translation (e.g., iostream)

---

## Diamond Problem Explanation

### The Problem (Without Virtual Inheritance)

**C++ Diamond (Non-Virtual):**
```cpp
class Animal {
    int age;
public:
    Animal(int a) : age(a) {}
};

class Dog : public Animal {  // Non-virtual inheritance
public:
    Dog(int a) : Animal(a) {}
};

class Cat : public Animal {  // Non-virtual inheritance
public:
    Cat(int a) : Animal(a) {}
};

class PetHybrid : public Dog, public Cat {
public:
    PetHybrid(int a) : Dog(a), Cat(a) {}  // TWO Animal instances!
};
```

**Problem**: PetHybrid has TWO Animal instances (one from Dog, one from Cat)
- Ambiguous member access: `hybrid.age` - which Animal::age?
- Wasted memory: Duplicate base data
- Semantic incorrectness: Should be ONE animal

### The Solution (Virtual Inheritance)

**C++ Diamond (Virtual):**
```cpp
class Animal {
    int age;
public:
    Animal(int a) : age(a) {}
    virtual ~Animal() {}
};

class Dog : public virtual Animal {  // Virtual inheritance
public:
    Dog(int a) : Animal(a) {}
};

class Cat : public virtual Animal {  // Virtual inheritance
public:
    Cat(int a) : Animal(a) {}
};

class PetHybrid : public Dog, public Cat {
public:
    PetHybrid(int a) : Dog(a), Cat(a), Animal(a) {}  // ONE Animal instance!
};
```

**Solution**: Virtual inheritance ensures:
- Single shared Animal instance
- PetHybrid directly constructs Animal (most derived class responsible)
- Dog and Cat constructors skip Animal construction in this context
- All paths point to same Animal instance

---

## Translation Pattern

### Virtual Inheritance with VTT

**C++ Source (Diamond Pattern):**
```cpp
class Animal {
    int age;
public:
    Animal(int a) : age(a) {}
    virtual ~Animal() {}
    virtual void speak() = 0;
};

class Dog : public virtual Animal {
    int dogData;
public:
    Dog(int a) : Animal(a), dogData(0) {}
    virtual void speak() override { printf("Woof\n"); }
};

class Cat : public virtual Animal {
    int catData;
public:
    Cat(int a) : Animal(a), catData(0) {}
    virtual void speak() override { printf("Meow\n"); }
};

class PetHybrid : public Dog, public Cat {
    int hybridData;
public:
    PetHybrid(int a) : Animal(a), Dog(a), Cat(a), hybridData(0) {}
    virtual void speak() override { printf("Woof-Meow\n"); }
};
```

**Generated C (Virtual Inheritance Pattern):**

```c
/* ============================================
   Forward Declarations
   ============================================ */
struct Animal;
struct Dog;
struct Cat;
struct PetHybrid;

/* ============================================
   Virtual Base Table Structures
   ============================================ */

/* VTT Entry: Offset to virtual base from derived object start */
struct VTT_Entry {
    ptrdiff_t offset;  /* Offset in bytes */
};

/* Virtual Base Table for Dog (points to virtual base Animal) */
struct Dog_VTT {
    struct VTT_Entry animal_offset;  /* Offset to Animal within Dog */
};

/* Virtual Base Table for Cat (points to virtual base Animal) */
struct Cat_VTT {
    struct VTT_Entry animal_offset;  /* Offset to Animal within Cat */
};

/* Virtual Base Table for PetHybrid (points to shared Animal) */
struct PetHybrid_VTT {
    struct VTT_Entry animal_offset_from_dog;  /* Offset to Animal via Dog path */
    struct VTT_Entry animal_offset_from_cat;  /* Offset to Animal via Cat path */
};

/* ============================================
   Vtable Structures (for virtual methods)
   ============================================ */

typedef void (*Animal_destructor_fn)(struct Animal* this);
typedef void (*Animal_speak_fn)(struct Animal* this);

struct Animal_vtable {
    Animal_destructor_fn destructor;
    Animal_speak_fn speak;
};

typedef void (*Dog_destructor_fn)(struct Dog* this);
typedef void (*Dog_speak_fn)(struct Dog* this);

struct Dog_vtable {
    Dog_destructor_fn destructor;
    Dog_speak_fn speak;
};

typedef void (*Cat_destructor_fn)(struct Cat* this);
typedef void (*Cat_speak_fn)(struct Cat* this);

struct Cat_vtable {
    Cat_destructor_fn destructor;
    Cat_speak_fn speak;
};

typedef void (*PetHybrid_destructor_fn)(struct PetHybrid* this);
typedef void (*PetHybrid_speak_fn)(struct PetHybrid* this);

struct PetHybrid_vtable {
    PetHybrid_destructor_fn destructor;
    PetHybrid_speak_fn speak;
};

/* ============================================
   Class Structures
   ============================================ */

/* Animal - Virtual base class */
struct Animal {
    const struct Animal_vtable* lpVtbl;
    int age;
};

/* Dog - Derives from virtual Animal */
struct Dog {
    const struct Dog_vtable* lpVtbl;          /* Own vtable */
    const struct Dog_VTT* vbptr;              /* Virtual base pointer */
    int dogData;
    /* NOTE: Animal is NOT embedded, accessed via vbptr */
};

/* Cat - Derives from virtual Animal */
struct Cat {
    const struct Cat_vtable* lpVtbl;          /* Own vtable */
    const struct Cat_VTT* vbptr;              /* Virtual base pointer */
    int catData;
    /* NOTE: Animal is NOT embedded, accessed via vbptr */
};

/* PetHybrid - Multiple inheritance with shared virtual base */
struct PetHybrid {
    /* Primary base: Dog */
    const struct PetHybrid_vtable* lpVtbl;    /* Own vtable */
    const struct PetHybrid_VTT* vbptr;        /* Virtual base pointer */
    int dogData;                               /* Dog's data */

    /* Non-primary base: Cat */
    const struct PetHybrid_vtable* lpVtbl2;   /* Cat's vtable interface */
    int catData;                               /* Cat's data */

    /* Own data */
    int hybridData;

    /* Virtual base: Animal (shared, at end of object) */
    struct Animal animal;                      /* Single shared Animal instance */
};

/* ============================================
   VTT Instances
   ============================================ */

/* Dog VTT - points to Animal within standalone Dog object */
static const struct Dog_VTT Dog_VTT_instance = {
    .animal_offset = { .offset = offsetof(struct Dog, dogData) + sizeof(int) }
};

/* Cat VTT - points to Animal within standalone Cat object */
static const struct Cat_VTT Cat_VTT_instance = {
    .animal_offset = { .offset = offsetof(struct Cat, catData) + sizeof(int) }
};

/* PetHybrid VTT - points to shared Animal instance */
static const struct PetHybrid_VTT PetHybrid_VTT_instance = {
    .animal_offset_from_dog = { .offset = offsetof(struct PetHybrid, animal) },
    .animal_offset_from_cat = { .offset = offsetof(struct PetHybrid, animal) }
};

/* ============================================
   Method Implementations
   ============================================ */

/* Animal methods */
void Animal_init(struct Animal* this, int a) {
    /* lpVtbl initialization deferred to most derived class */
    this->age = a;
}

void Animal_destructor(struct Animal* this) {
    /* Cleanup */
}

/* Dog methods */
void Dog_destructor(struct Dog* this) {
    /* Get virtual base Animal via vbptr */
    struct Animal* animal = (struct Animal*)((char*)this + this->vbptr->animal_offset.offset);
    Animal_destructor(animal);
}

void Dog_speak(struct Dog* this) {
    printf("Woof\n");
}

/* Dog vtable instance */
static const struct Dog_vtable Dog_vtable_instance = {
    .destructor = (Dog_destructor_fn)Dog_destructor,
    .speak = (Dog_speak_fn)Dog_speak
};

/* Dog constructor */
void Dog_init(struct Dog* this, int a) {
    this->lpVtbl = &Dog_vtable_instance;
    this->vbptr = &Dog_VTT_instance;

    /* Construct virtual base Animal (when Dog is standalone) */
    struct Animal* animal = (struct Animal*)((char*)this + this->vbptr->animal_offset.offset);
    Animal_init(animal, a);

    this->dogData = 0;
}

/* Cat methods */
void Cat_destructor(struct Cat* this) {
    /* Get virtual base Animal via vbptr */
    struct Animal* animal = (struct Animal*)((char*)this + this->vbptr->animal_offset.offset);
    Animal_destructor(animal);
}

void Cat_speak(struct Cat* this) {
    printf("Meow\n");
}

/* Cat vtable instance */
static const struct Cat_vtable Cat_vtable_instance = {
    .destructor = (Cat_destructor_fn)Cat_destructor,
    .speak = (Cat_speak_fn)Cat_speak
};

/* Cat constructor */
void Cat_init(struct Cat* this, int a) {
    this->lpVtbl = &Cat_vtable_instance;
    this->vbptr = &Cat_VTT_instance;

    /* Construct virtual base Animal (when Cat is standalone) */
    struct Animal* animal = (struct Animal*)((char*)this + this->vbptr->animal_offset.offset);
    Animal_init(animal, a);

    this->catData = 0;
}

/* PetHybrid methods */
void PetHybrid_destructor(struct PetHybrid* this) {
    /* Destroy virtual base last */
    Animal_destructor(&this->animal);
}

void PetHybrid_speak(struct PetHybrid* this) {
    printf("Woof-Meow\n");
}

/* PetHybrid vtable instance */
static const struct PetHybrid_vtable PetHybrid_vtable_instance = {
    .destructor = (PetHybrid_destructor_fn)PetHybrid_destructor,
    .speak = (PetHybrid_speak_fn)PetHybrid_speak
};

/* PetHybrid constructor */
void PetHybrid_init(struct PetHybrid* this, int a) {
    /* 1. Construct shared virtual base Animal FIRST (most derived class responsibility) */
    Animal_init(&this->animal, a);

    /* 2. Initialize Dog subobject (skip Animal construction via flag) */
    this->lpVtbl = &PetHybrid_vtable_instance;
    this->vbptr = &PetHybrid_VTT_instance;
    this->dogData = 0;
    /* Dog's Animal constructor skipped - already constructed */

    /* 3. Initialize Cat subobject (skip Animal construction via flag) */
    this->lpVtbl2 = &PetHybrid_vtable_instance;  /* Same vtable for polymorphism */
    this->catData = 0;
    /* Cat's Animal constructor skipped - already constructed */

    /* 4. Initialize own members */
    this->hybridData = 0;
}

/* ============================================
   Polymorphic Usage
   ============================================ */

void test_virtual_inheritance() {
    struct PetHybrid hybrid;
    PetHybrid_init(&hybrid, 5);

    /* Cast to Dog* - points to Dog subobject */
    struct Dog* dog = (struct Dog*)&hybrid;

    /* Cast to Cat* - points to Cat subobject (with offset) */
    struct Cat* cat = (struct Cat*)((char*)&hybrid + offsetof(struct PetHybrid, lpVtbl2));

    /* Cast to Animal* - points to SHARED Animal instance */
    struct Animal* animal = &hybrid.animal;

    /* All paths point to SAME Animal instance - diamond problem solved! */
    animal->lpVtbl->speak(animal);  /* Calls PetHybrid_speak */

    /* Cleanup */
    PetHybrid_destructor(&hybrid);
}
```

---

## Key Concepts

### Virtual Base Table (VTT)

The VTT stores offsets to virtual base classes:
- **Purpose**: Indirection to shared base instance
- **Structure**: Array of offset entries
- **One per class**: Each class with virtual bases has its own VTT
- **Runtime lookup**: `vbptr + offset` to find virtual base

### Virtual Base Pointer (vbptr)

The vbptr points to the VTT:
- **Location**: Member of each class with virtual bases
- **Type**: `const struct ClassName_VTT*`
- **Initialization**: Set in constructor to point to static VTT instance
- **Usage**: Access virtual base via `(char*)this + vbptr->base_offset.offset`

### Object Layout

**Standalone Dog Object:**
```
+--------------------+
| lpVtbl             | (vtable pointer)
| vbptr              | (virtual base table pointer)
| dogData            |
+--------------------+
| Animal instance    | (virtual base, at end)
|   lpVtbl           |
|   age              |
+--------------------+
```

**PetHybrid Object (Diamond):**
```
+--------------------+
| Dog subobject:     |
|   lpVtbl           | (points to PetHybrid vtable)
|   vbptr            | (points to PetHybrid VTT)
|   dogData          |
+--------------------+
| Cat subobject:     |
|   lpVtbl2          | (points to PetHybrid vtable)
|   catData          |
+--------------------+
| hybridData         | (PetHybrid's own data)
+--------------------+
| Animal instance    | (SHARED virtual base, at end)
|   lpVtbl           |
|   age              |
+--------------------+
```

### Constructor Ordering

**Virtual Base Constructor Rule:**
The most derived class constructs virtual bases, intermediate bases skip construction.

**PetHybrid Construction Order:**
1. **Animal** (virtual base, constructed by PetHybrid)
2. **Dog** subobject (skips Animal construction)
3. **Cat** subobject (skips Animal construction)
4. **PetHybrid** own members

---

## Implementation Tasks

### Group 1: Virtual Base Detection (2 parallel tasks)

**Task 1: Virtual Base Analyzer** (Est. 4-5 hours)
- **Component**: VirtualBaseAnalyzer (NEW)
- **Method**: Detect virtual inheritance in C++ AST
- **Implementation**:
  - Create VirtualBaseAnalyzer helper class
  - Detect virtual base specifiers in CXXRecordDecl
  - Identify all virtual bases in inheritance hierarchy
  - Determine if class is a virtual base
  - Build virtual base graph (who inherits what virtually)
  - Detect diamond patterns
  - Calculate virtual base layout (position at end of object)
- **Tests** (10-12 tests):
  - Detect single virtual base
  - Detect multiple virtual bases
  - Detect diamond pattern (shared virtual base)
  - Distinguish virtual from non-virtual bases
  - Multi-level virtual inheritance
  - Virtual base in deep hierarchy
  - Virtual base with non-virtual bases mixed
  - Standalone class with virtual base
  - Most derived class in diamond
  - Virtual base graph construction
  - Null/invalid inheritance handling

**Task 2: VTT Offset Calculator** (Est. 3-4 hours) - PARALLEL with Task 1
- **Component**: VTTOffsetCalculator (NEW)
- **Method**: Calculate offsets to virtual bases
- **Implementation**:
  - Create VTTOffsetCalculator helper class
  - Calculate offset from derived object start to virtual base
  - Handle multiple virtual bases (multiple offsets)
  - Calculate offset for standalone objects
  - Calculate offset for diamond pattern objects
  - Use Clang's ASTRecordLayout API
  - Account for non-virtual base sizes
  - Account for vbptr size
- **Tests** (8-10 tests):
  - Calculate offset for single virtual base
  - Calculate offset for multiple virtual bases
  - Calculate offset in diamond pattern
  - Calculate offset with non-virtual bases
  - Calculate offset in deep hierarchy
  - Offset calculation for standalone object
  - Offset calculation for most derived class
  - Null/invalid class handling

### Group 2: VTT Generation (3 parallel tasks)

**Task 3: VTT Struct Generator** (Est. 3-4 hours)
- **Component**: VTTStructGenerator (NEW)
- **Method**: Generate VTT struct definition
- **Implementation**:
  - Create VTTStructGenerator helper class
  - Generate VTT_Entry struct (offset field)
  - Generate per-class VTT struct (ClassName_VTT)
  - Include offset entry for each virtual base
  - Name entries: `basename_offset` or `basename_offset_from_path`
  - Support multiple paths to same virtual base (diamond)
- **Tests** (8-10 tests):
  - Generate VTT_Entry struct
  - Generate VTT struct for single virtual base
  - Generate VTT struct for multiple virtual bases
  - Generate VTT struct for diamond pattern
  - VTT naming convention correct
  - VTT field naming correct
  - Multiple paths - multiple offset entries
  - Empty VTT (no virtual bases)

**Task 4: VTT Instance Generator** (Est. 3-4 hours) - PARALLEL with Task 3
- **Component**: VTTInstanceGenerator (NEW)
- **Method**: Generate static VTT instance
- **Implementation**:
  - Create VTTInstanceGenerator helper class
  - Generate static const VTT instance
  - Pattern: `static const struct ClassName_VTT ClassName_VTT_instance = { ... };`
  - Initialize offset entries with calculated values
  - Use offsetof() or literal offsets
  - Designated initializers for clarity
- **Tests** (8-10 tests):
  - Generate VTT instance for single virtual base
  - Generate VTT instance for multiple virtual bases
  - Generate VTT instance for diamond pattern
  - VTT instance is static const
  - VTT instance initialization correct
  - Offset values correct
  - Designated initializers used
  - Multiple VTT instances for multiple classes

**Task 5: vbptr Injection** (Est. 2-3 hours) - PARALLEL with Task 3, 4
- **Component**: RecordHandler (extend)
- **Method**: Inject vbptr field into structs with virtual bases
- **Implementation**:
  - Extend RecordHandler to detect virtual bases
  - Inject vbptr field after lpVtbl
  - Pattern: `const struct ClassName_VTT* vbptr;`
  - Order: lpVtbl, vbptr, then other fields
  - Only inject if class has virtual bases
  - Correct type for vbptr (ClassName_VTT*)
- **Tests** (8-10 tests):
  - Inject vbptr for single virtual base
  - Inject vbptr for multiple virtual bases
  - vbptr after lpVtbl field
  - vbptr has correct type
  - vbptr is const pointer
  - No vbptr if no virtual bases
  - vbptr in derived class with virtual bases
  - Field order: lpVtbl, vbptr, data

### Group 3: Virtual Base Layout (3 tasks - 2 parallel + 1)

**Task 6: Virtual Base Embedding** (Est. 4-5 hours)
- **Component**: RecordHandler (extend)
- **Method**: Embed virtual base instances in struct layout
- **Implementation**:
  - Place virtual bases at END of struct
  - Order: non-virtual bases, own data, then virtual bases
  - For diamond: Embed virtual base ONCE in most derived class
  - For standalone: Embed virtual base at end
  - Calculate correct layout with ASTRecordLayout
  - Update field offsets accordingly
- **Tests** (10-12 tests):
  - Embed single virtual base at end
  - Embed multiple virtual bases at end
  - Diamond pattern - single base instance
  - Standalone class with virtual base
  - Virtual base after non-virtual bases
  - Virtual base after own data
  - Field offset calculation correct
  - Virtual base type correct
  - Virtual base initialization order
  - Complex hierarchy virtual base placement

**Task 7: Virtual Base Access Code Generator** (Est. 3-4 hours) - PARALLEL with Task 6
- **Component**: ExpressionHandler (extend)
- **Method**: Generate virtual base access via vbptr
- **Implementation**:
  - Detect access to virtual base members
  - Generate offset lookup: `(char*)this + this->vbptr->base_offset.offset`
  - Cast to base type: `(struct Base*)(offset_address)`
  - Access member through base pointer
  - Handle both read and write access
  - Handle virtual base method calls
- **Tests** (10-12 tests):
  - Access virtual base member
  - Access virtual base via vbptr
  - Virtual base member read
  - Virtual base member write
  - Virtual base method call
  - Virtual base in diamond pattern
  - Offset calculation correct
  - Cast to virtual base type
  - Nested virtual base access
  - Complex expression with virtual base

**Task 8: Virtual Base Constructor Ordering** (Est. 4-5 hours) - DEPENDS on Tasks 6, 7
- **Component**: ConstructorHandler (extend)
- **Method**: Implement virtual base constructor ordering
- **Implementation**:
  - Most derived class constructs virtual bases FIRST
  - Intermediate classes skip virtual base construction
  - Inject virtual base constructor calls before non-virtual base calls
  - Use construction flags or conditional logic to skip
  - Initialize vbptr before accessing virtual base
  - Ensure single construction of shared virtual base
- **Tests** (12-15 tests):
  - Virtual base constructed first in most derived
  - Intermediate class skips virtual base construction
  - Diamond pattern - single virtual base construction
  - Constructor ordering: virtual bases, non-virtual bases, own data
  - vbptr initialization before virtual base access
  - Multiple virtual bases - all constructed first
  - Virtual base constructor with parameters
  - Virtual base default constructor
  - Virtual base initialization list
  - Standalone class constructs virtual base
  - Nested virtual inheritance constructor order
  - Virtual base construction flag logic

### Group 4: Polymorphic Calls and Casts (2 parallel tasks)

**Task 9: Virtual Base Cast Handling** (Est. 3-4 hours)
- **Component**: ExpressionHandler (extend)
- **Method**: Handle casts to/from virtual bases
- **Implementation**:
  - Detect cast to virtual base
  - Generate cast code using vbptr offset
  - Pattern: `(Base*)((char*)derived + derived->vbptr->base_offset.offset)`
  - Handle upcast (derived to virtual base)
  - Handle downcast (virtual base to derived)
  - Handle static_cast, reinterpret_cast
  - Handle implicit casts
- **Tests** (10-12 tests):
  - Upcast to virtual base
  - Downcast from virtual base
  - Static cast to virtual base
  - Reinterpret cast to virtual base
  - Implicit cast to virtual base
  - Cast in diamond pattern
  - Cast to shared virtual base from different paths
  - Cast to non-virtual base (no vbptr needed)
  - Offset calculation in cast
  - Complex cast expression

**Task 10: Virtual Method Dispatch with Virtual Bases** (Est. 3-4 hours) - PARALLEL with Task 9
- **Component**: ExpressionHandler (extend)
- **Method**: Handle virtual method calls through virtual base pointers
- **Implementation**:
  - Detect virtual method call through virtual base pointer
  - Access virtual base via vbptr
  - Call method through base vtable
  - Pattern: `base->lpVtbl->method(base)`
  - Ensure correct this pointer adjustment
  - Handle overridden methods in derived class
- **Tests** (10-12 tests):
  - Virtual method call through virtual base
  - Virtual method call in diamond pattern
  - Overridden virtual method call
  - Virtual method call with parameters
  - Virtual method call with return value
  - Virtual method call via different diamond paths
  - Polymorphic call through virtual base pointer
  - Virtual destructor call on virtual base
  - Virtual method in standalone class with virtual base
  - Complex virtual call expression

### Group 5: Integration & E2E (2 sequential tasks)

**Task 11: Integration Tests** (Est. 5-6 hours)
- **File**: `tests/integration/handlers/VirtualInheritanceIntegrationTest.cpp`
- **Tests** (35-40 tests):
  - Simple virtual inheritance (single virtual base)
  - Multiple virtual bases (multiple virtual inheritance)
  - Diamond pattern (classic diamond problem)
  - Multi-level virtual inheritance (A -v-> B -v-> C)
  - Mixed virtual and non-virtual inheritance
  - Virtual base with virtual methods
  - Virtual base with data members
  - Virtual base constructor ordering
  - Virtual base destructor ordering
  - Virtual base access via vbptr
  - Virtual base member read
  - Virtual base member write
  - Virtual base method call
  - Cast to virtual base
  - Cast from virtual base
  - Polymorphic call through virtual base
  - Diamond with multiple paths to virtual base
  - Standalone class with virtual base
  - Most derived class in diamond
  - Virtual base in deep hierarchy
  - Virtual base with complex data types
  - Virtual base with pointers/references
  - Virtual base initialization with parameters
  - VTT generation verification
  - vbptr injection verification
  - Offset calculation verification
  - Object layout verification
  - Constructor ordering verification
  - Destructor ordering verification
  - Complete diamond example (Animal/Dog/Cat/Hybrid)

**Task 12: E2E Tests** (Est. 3-4 hours) - SEQUENTIAL after Task 11
- **File**: `tests/e2e/phase56/VirtualInheritanceE2ETest.cpp`
- **Tests** (15 tests):
  - 2 active sanity tests (simple virtual inheritance, basic diamond)
  - 3-4 active tests (real algorithms with virtual inheritance)
  - 10-11 disabled algorithm tests:
    - iostream hierarchy (istream/ostream/iostream)
    - GUI widget hierarchy with virtual base
    - Plugin system with virtual interface
    - Mixin pattern with virtual bases
    - CRTP with virtual inheritance
    - Multi-level diamond pattern
    - Complex inheritance graph
    - Virtual base with RTTI (if supported)
    - Virtual base with exceptions (if supported)
    - Real-world diamond pattern example

---

## Execution Strategy

### Parallel Execution Groups

**Group 1 (Tasks 1-2)**: Virtual Base Detection - 2 parallel tasks
- Duration: ~4-5 hours parallel (vs ~7-9 hours sequential)

**Group 2 (Tasks 3-5)**: VTT Generation - 3 parallel tasks
- Duration: ~3-4 hours parallel (vs ~8-11 hours sequential)

**Group 3 (Tasks 6-8)**: Virtual Base Layout - 2 parallel + 1 sequential
- Duration: ~7-9 hours (4-5 parallel + 4-5 sequential)

**Group 4 (Tasks 9-10)**: Polymorphic Calls and Casts - 2 parallel tasks
- Duration: ~3-4 hours parallel (vs ~6-8 hours sequential)

**Group 5 (Tasks 11-12)**: Integration & E2E - Sequential
- Duration: ~8-10 hours sequential

**Total Estimated Time:**
- Parallel: ~25-32 hours
- Sequential: ~45-60 hours
- **Time Savings: ~35-45%**

---

## Files to Create

1. `include/VirtualBaseAnalyzer.h` - Virtual base detection and analysis
2. `src/VirtualBaseAnalyzer.cpp` - Implementation
3. `tests/unit/VirtualBaseAnalyzerTest.cpp` - Unit tests
4. `include/VTTOffsetCalculator.h` - VTT offset calculation
5. `src/VTTOffsetCalculator.cpp` - Implementation
6. `tests/unit/VTTOffsetCalculatorTest.cpp` - Unit tests
7. `include/VTTStructGenerator.h` - VTT struct generation
8. `src/VTTStructGenerator.cpp` - Implementation
9. `tests/unit/VTTStructGeneratorTest.cpp` - Unit tests
10. `include/VTTInstanceGenerator.h` - VTT instance generation
11. `src/VTTInstanceGenerator.cpp` - Implementation
12. `tests/unit/VTTInstanceGeneratorTest.cpp` - Unit tests
13. `tests/integration/handlers/VirtualInheritanceIntegrationTest.cpp` - Integration tests
14. `tests/e2e/phase56/VirtualInheritanceE2ETest.cpp` - E2E tests
15. `.planning/phases/56-virtual-inheritance/PHASE56-COMPLETE.md` - Summary doc

## Files to Modify

1. `include/handlers/RecordHandler.h` - Add vbptr injection, virtual base embedding
2. `src/handlers/RecordHandler.cpp` - Implement virtual base layout
3. `include/handlers/ConstructorHandler.h` - Add virtual base constructor ordering
4. `src/handlers/ConstructorHandler.cpp` - Implement virtual base construction
5. `include/handlers/ExpressionHandler.h` - Add virtual base access, casts, calls
6. `src/handlers/ExpressionHandler.cpp` - Implement virtual base operations
7. `include/handlers/HandlerContext.h` - Add virtual base tracking
8. `src/handlers/HandlerContext.cpp` - Implement virtual base metadata storage
9. `include/MultipleInheritanceAnalyzer.h` - Extend for virtual inheritance
10. `src/MultipleInheritanceAnalyzer.cpp` - Add virtual base detection
11. `CMakeLists.txt` - Add new test targets

---

## Success Criteria

- [ ] All 95-110 unit tests pass (100%)
- [ ] All 35-40 integration tests pass (100%)
- [ ] 2-4 E2E active tests pass (100%)
- [ ] VTT structs generated for classes with virtual bases
- [ ] VTT instances generated with correct offsets
- [ ] vbptr injected into structs with virtual bases
- [ ] Virtual bases embedded at end of object layout
- [ ] Virtual base constructed once in diamond pattern
- [ ] Virtual base constructor ordering correct (most derived constructs first)
- [ ] Virtual base access via vbptr works correctly
- [ ] Casts to/from virtual bases calculate correct offsets
- [ ] Virtual method dispatch through virtual bases works
- [ ] Generated C code compiles without warnings
- [ ] Code follows SOLID principles
- [ ] TDD followed throughout
- [ ] Diamond pattern fully supported

---

## Test Count Targets

- **Group 1 Tests**: 18-22 tests (Analyzer 10-12, Offset Calc 8-10)
- **Group 2 Tests**: 24-30 tests (VTT Struct 8-10, VTT Instance 8-10, vbptr 8-10)
- **Group 3 Tests**: 32-39 tests (Embedding 10-12, Access 10-12, Constructor 12-15)
- **Group 4 Tests**: 20-24 tests (Cast 10-12, Virtual Call 10-12)
- **Group 5 Tests**: 50 tests (Integration 35-40, E2E 15)
- **Total: 144-165 tests** (target 95-110 active, rest for complex scenarios)

---

## Dependencies

**Requires:**
- Phase 46 (Multiple Inheritance) - COMPLETE ✅
- Phase 45 (Virtual Methods COM-Style) - COMPLETE ✅
- Phase 44 (Classes Simple) - COMPLETE ✅
- MultipleInheritanceAnalyzer - base class analysis
- VtableGenerator - vtable generation
- RecordHandler - struct layout
- ConstructorHandler - constructor generation
- ExpressionHandler - member access, casts, calls

**External:**
- Clang AST API for virtual base detection
- Clang ASTRecordLayout for offset calculation
- Google Test framework
- CMake build system

---

## Risk Mitigation

**Risk 1: VTT Offset Calculation Complexity**
- Mitigation: Use Clang's ASTRecordLayout API for accurate offsets
- Fallback: Manual calculation based on field sizes
- Test: Comprehensive offset verification tests

**Risk 2: Virtual Base Constructor Ordering Complexity**
- Mitigation: Careful analysis of C++ constructor ordering rules
- Implement construction flags to skip intermediate construction
- Test: Extensive constructor ordering tests

**Risk 3: Diamond Pattern Edge Cases**
- Mitigation: Thorough testing of diamond patterns
- Support multiple paths to same virtual base
- Test: Various diamond configurations

**Risk 4: Virtual + Non-Virtual Mix**
- Mitigation: Clearly distinguish virtual from non-virtual bases
- Test: Mixed inheritance patterns

**Risk 5: Deep Virtual Hierarchies**
- Mitigation: Recursive virtual base analysis
- Support multi-level virtual inheritance
- Test: Deep hierarchy tests

---

## Key Differences from Phase 46 (Multiple Inheritance)

### Phase 46: Multiple Inheritance (Non-Virtual)
- **Multiple vtables**: lpVtbl, lpVtbl2, lpVtbl3
- **This-pointer thunks**: Adjust this for non-primary bases
- **Separate base instances**: Each inheritance path has its own base instance
- **No shared bases**: Diamond creates DUPLICATE base instances

### Phase 56: Virtual Inheritance
- **VTT (Virtual Base Table)**: Contains offsets to virtual bases
- **vbptr (Virtual Base Pointer)**: Points to VTT for offset lookup
- **Single base instance**: Shared virtual base embedded ONCE at end of object
- **Solves diamond problem**: Only ONE instance of common base
- **Constructor ordering**: Most derived constructs virtual bases first
- **Offset indirection**: Access virtual base via `vbptr + offset` lookup

### When to Use Which Pattern

**Use Multiple Inheritance (Phase 46)** when:
- No shared base class (independent interfaces)
- Want separate instances of common base (rare)
- No diamond pattern

**Use Virtual Inheritance (Phase 56)** when:
- Diamond pattern exists
- Want single shared base instance
- iostream-like hierarchies
- Mixin patterns with common base

---

## Naming Conventions

### VTT Structures
- VTT entry struct: `VTT_Entry` (single offset field)
- VTT struct: `ClassName_VTT`
- VTT instance: `ClassName_VTT_instance`
- VTT offset field: `basename_offset` or `basename_offset_from_path`

### Virtual Base Pointer
- Field name: `vbptr` (follows COM convention like lpVtbl)
- Type: `const struct ClassName_VTT*`
- Position: After lpVtbl, before data members

### Virtual Base Access
- Offset lookup: `this->vbptr->basename_offset.offset`
- Base pointer: `(struct Base*)((char*)this + offset)`
- Member access: `base->member`

---

## Example: Complete Diamond Pattern

See translation pattern section above for full example of:
- Animal (virtual base)
- Dog : virtual Animal
- Cat : virtual Animal
- PetHybrid : Dog, Cat (diamond with shared Animal)

Shows:
- VTT struct and instance generation
- vbptr injection
- Virtual base embedding at end
- Constructor ordering (Animal first)
- Virtual base access via vbptr
- Single shared Animal instance

---

## Next Steps After Completion

**Phase 57: RTTI with Virtual Inheritance** - Est. 15-20 hours
- Type info for virtual bases
- Dynamic cast with virtual base offset
- Typeid for virtual inheritance hierarchies

**Phase 58: Covariant Return Types** - Est. 10-15 hours
- Override with derived return type
- Virtual base as return type
- Offset adjustment in return

**Phase 59: Exception Handling with Virtual Bases** - Est. 20-25 hours
- Catch handlers for virtual base types
- Exception object with virtual inheritance
- Proper cleanup of virtual bases during unwinding

---

## References

### Virtual Inheritance Technical Details
- [Virtual inheritance - cppreference.com](https://en.cppreference.com/w/cpp/language/derived_class#Virtual_base_classes)
- [The Diamond Problem - Wikipedia](https://en.wikipedia.org/wiki/Multiple_inheritance#The_diamond_problem)
- [Virtual Base Class Tables - Itanium C++ ABI](https://itanium-cxx-abi.github.io/cxx-abi/abi.html#vtable-components)

### Implementation Resources
- [C++ Object Layout: Virtual Inheritance](https://shaharmike.com/cpp/vtable-part3/)
- [Virtual Inheritance Implementation - LLVM](https://clang.llvm.org/doxygen/classclang_1_1CXXRecordDecl.html#a8c3b3b3b3b3b3b3b3b3b)
- [Virtual Base Offset Tables - Raymond Chen](https://devblogs.microsoft.com/oldnewthing/20040217-00/?p=40563)

### Diamond Pattern Examples
- [iostream hierarchy - C++ Standard Library](https://en.cppreference.com/w/cpp/io)
- [Solving the Diamond Problem in C++](https://www.learncpp.com/cpp-tutorial/virtual-base-classes/)

---

**Created**: 2025-12-26
**Status**: READY FOR IMPLEMENTATION
**Pattern**: Virtual Base Tables (VTT) with virtual base pointers (vbptr)
**Priority**: MEDIUM (important for completeness, less common than non-virtual multiple inheritance)
**Estimated Duration**: 40-60 hours (sequential), 25-32 hours (parallel with ~40% time savings)
