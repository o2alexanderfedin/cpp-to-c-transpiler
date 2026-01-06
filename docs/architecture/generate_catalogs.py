#!/usr/bin/env python3
"""
Generate JSON catalogs for Clang C++ AST nodes.
Based on official Clang documentation and AST hierarchy.
"""

import json
from pathlib import Path

# Output directory
OUTPUT_DIR = Path(__file__).parent

def create_basic_nodes_catalog():
    """Catalog of AST nodes for basic C++ features"""
    return {
        "category": "basic",
        "description": "AST nodes for fundamental C++ features: functions, variables, expressions, and basic control flow",
        "nodes": [
            {
                "name": "FunctionDecl",
                "purpose": "Represents a function declaration or definition",
                "inherits_from": "DeclaratorDecl → ValueDecl → NamedDecl → Decl",
                "key_methods": [
                    "getReturnType() - Returns QualType of return value",
                    "parameters() - Iterator over ParmVarDecl parameters",
                    "getBody() - Returns CompoundStmt if function has body",
                    "isThisDeclarationADefinition() - True if body exists",
                    "getNameAsString() - Function name as string"
                ],
                "used_for": ["Function definitions", "Function declarations (prototypes)", "Main function"],
                "c_equivalent": "C function declaration/definition (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct mapping to C function. Extract name, return type, parameters, and body.",
                "example_cpp": "int add(int a, int b) { return a + b; }",
                "example_c": "int add(int a, int b) { return a + b; }"
            },
            {
                "name": "ParmVarDecl",
                "purpose": "Represents a function parameter",
                "inherits_from": "VarDecl → DeclaratorDecl → ValueDecl → NamedDecl → Decl",
                "key_methods": [
                    "getType() - Returns QualType of parameter",
                    "getNameAsString() - Parameter name",
                    "hasDefaultArg() - True if has default argument (C++ only)"
                ],
                "used_for": ["Function parameters"],
                "c_equivalent": "C function parameter (same syntax for simple types)",
                "complexity": 1,
                "translation_notes": "Direct mapping. C++ references become pointers.",
                "example_cpp": "int a, const std::string& name",
                "example_c": "int a, const char* name"
            },
            {
                "name": "VarDecl",
                "purpose": "Represents a variable declaration (local or global)",
                "inherits_from": "DeclaratorDecl → ValueDecl → NamedDecl → Decl",
                "key_methods": [
                    "getType() - Returns QualType",
                    "getInit() - Returns initializer Expr (if any)",
                    "hasInit() - True if has initializer",
                    "isStaticLocal() - True for static local variables",
                    "hasGlobalStorage() - True for global variables"
                ],
                "used_for": ["Local variables", "Global variables", "Static variables"],
                "c_equivalent": "C variable declaration",
                "complexity": 1,
                "translation_notes": "Direct mapping. Handle initialization expression separately.",
                "example_cpp": "int result = a + b;",
                "example_c": "int result = a + b;"
            },
            {
                "name": "DeclRefExpr",
                "purpose": "Represents a reference to a declared variable, parameter, or function",
                "inherits_from": "Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getDecl() - Returns referenced Decl",
                    "getNameInfo() - Name information",
                    "getType() - Type of the referenced entity"
                ],
                "used_for": ["Variable references", "Parameter references", "Function references"],
                "c_equivalent": "C identifier",
                "complexity": 1,
                "translation_notes": "Emit the name of the referenced declaration. Track scope.",
                "example_cpp": "return result; // 'result' is DeclRefExpr",
                "example_c": "return result;"
            },
            {
                "name": "BinaryOperator",
                "purpose": "Represents a binary operator expression (e.g., +, -, *, ==, =)",
                "inherits_from": "Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getOpcode() - Returns operator kind (BO_Add, BO_Mul, etc.)",
                    "getOpcodeStr() - Returns operator as string ('+', '*', etc.)",
                    "getLHS() - Left-hand side expression",
                    "getRHS() - Right-hand side expression"
                ],
                "used_for": ["Arithmetic operators (+, -, *, /, %)", "Comparison operators (==, !=, <, >)", "Logical operators (&&, ||)", "Assignment operators (=, +=, -=)"],
                "c_equivalent": "C binary operator (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct mapping. Recursively translate LHS and RHS.",
                "example_cpp": "a + b, x == y",
                "example_c": "a + b, x == y"
            },
            {
                "name": "UnaryOperator",
                "purpose": "Represents a unary operator expression (e.g., -, !, &, *, ++, --)",
                "inherits_from": "Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getOpcode() - Returns operator kind (UO_Minus, UO_AddrOf, etc.)",
                    "getOpcodeStr() - Returns operator as string",
                    "getSubExpr() - The operand expression",
                    "isPrefix() - True for prefix operators (++i)",
                    "isPostfix() - True for postfix operators (i++)"
                ],
                "used_for": ["Negation (-x)", "Logical NOT (!x)", "Address-of (&x)", "Dereference (*ptr)", "Increment/decrement (++, --)"],
                "c_equivalent": "C unary operator (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct mapping. Handle prefix/postfix for ++ and --.",
                "example_cpp": "-x, !flag, &variable",
                "example_c": "-x, !flag, &variable"
            },
            {
                "name": "IntegerLiteral",
                "purpose": "Represents an integer literal constant",
                "inherits_from": "Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getValue() - Returns APInt value",
                    "getType() - Type (int, unsigned, long, etc.)"
                ],
                "used_for": ["Integer constants (42, 0, -1)"],
                "c_equivalent": "C integer literal (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct emission of the value.",
                "example_cpp": "42, 0xFF, 100L",
                "example_c": "42, 0xFF, 100L"
            },
            {
                "name": "FloatingLiteral",
                "purpose": "Represents a floating-point literal constant",
                "inherits_from": "Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getValue() - Returns APFloat value",
                    "getValueAsApproximateDouble() - Double approximation"
                ],
                "used_for": ["Float/double constants (3.14, 2.0f)"],
                "c_equivalent": "C floating literal (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct emission with proper suffix (f, L).",
                "example_cpp": "3.14, 2.0f",
                "example_c": "3.14, 2.0f"
            },
            {
                "name": "StringLiteral",
                "purpose": "Represents a string literal constant",
                "inherits_from": "Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getString() - Returns the string value",
                    "getLength() - String length"
                ],
                "used_for": ["String constants"],
                "c_equivalent": "C string literal (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct emission. Handle escape sequences.",
                "example_cpp": "\"hello world\"",
                "example_c": "\"hello world\""
            },
            {
                "name": "CharacterLiteral",
                "purpose": "Represents a character literal constant",
                "inherits_from": "Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getValue() - Returns character value"
                ],
                "used_for": ["Character constants"],
                "c_equivalent": "C character literal (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct emission.",
                "example_cpp": "'a', '\\n'",
                "example_c": "'a', '\\n'"
            },
            {
                "name": "CallExpr",
                "purpose": "Represents a function call expression",
                "inherits_from": "Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getCallee() - Returns expression being called",
                    "getNumArgs() - Number of arguments",
                    "getArg(i) - Get i-th argument expression",
                    "getDirectCallee() - Returns FunctionDecl if direct call"
                ],
                "used_for": ["Function calls"],
                "c_equivalent": "C function call (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct mapping for standalone functions. Method calls require transformation.",
                "example_cpp": "printf(\"hello\"), add(3, 4)",
                "example_c": "printf(\"hello\"), add(3, 4)"
            },
            {
                "name": "ImplicitCastExpr",
                "purpose": "Represents an implicit type conversion inserted by compiler",
                "inherits_from": "CastExpr → Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getCastKind() - Type of cast (LValueToRValue, IntegralCast, etc.)",
                    "getSubExpr() - Expression being cast",
                    "getType() - Target type"
                ],
                "used_for": ["LValue to RValue conversion", "Integral promotions", "Array to pointer decay"],
                "c_equivalent": "Usually implicit in C as well",
                "complexity": 1,
                "translation_notes": "Often transparent. LValueToRValue is automatic in C. Emit subexpression.",
                "example_cpp": "int x = a; // 'a' has implicit LValueToRValue cast",
                "example_c": "int x = a; // Same, implicit"
            },
            {
                "name": "CompoundStmt",
                "purpose": "Represents a compound statement (block) { ... }",
                "inherits_from": "Stmt",
                "key_methods": [
                    "body() - Iterator over child statements",
                    "size() - Number of statements in block"
                ],
                "used_for": ["Function bodies", "Block statements in loops/if"],
                "c_equivalent": "C compound statement (same syntax)",
                "complexity": 1,
                "translation_notes": "Emit braces and recursively translate child statements.",
                "example_cpp": "{ stmt1; stmt2; }",
                "example_c": "{ stmt1; stmt2; }"
            },
            {
                "name": "DeclStmt",
                "purpose": "Represents a statement that declares variables",
                "inherits_from": "Stmt",
                "key_methods": [
                    "decl_begin(), decl_end() - Iterators over declarations",
                    "isSingleDecl() - True if single declaration"
                ],
                "used_for": ["Variable declarations in statement context"],
                "c_equivalent": "C declaration statement",
                "complexity": 1,
                "translation_notes": "Emit each declaration with semicolon.",
                "example_cpp": "int x = 5;",
                "example_c": "int x = 5;"
            },
            {
                "name": "ReturnStmt",
                "purpose": "Represents a return statement",
                "inherits_from": "Stmt",
                "key_methods": [
                    "getRetValue() - Returns expression being returned (or nullptr for void)"
                ],
                "used_for": ["Function return statements"],
                "c_equivalent": "C return statement (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct mapping. Translate return expression.",
                "example_cpp": "return result;",
                "example_c": "return result;"
            },
            {
                "name": "IfStmt",
                "purpose": "Represents an if statement (with optional else)",
                "inherits_from": "Stmt",
                "key_methods": [
                    "getCond() - Condition expression",
                    "getThen() - Then branch statement",
                    "getElse() - Else branch statement (or nullptr)"
                ],
                "used_for": ["Conditional execution"],
                "c_equivalent": "C if statement (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct mapping. Translate condition, then, and else branches.",
                "example_cpp": "if (x > 0) { ... } else { ... }",
                "example_c": "if (x > 0) { ... } else { ... }"
            },
            {
                "name": "WhileStmt",
                "purpose": "Represents a while loop",
                "inherits_from": "Stmt",
                "key_methods": [
                    "getCond() - Loop condition",
                    "getBody() - Loop body statement"
                ],
                "used_for": ["While loops"],
                "c_equivalent": "C while loop (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct mapping.",
                "example_cpp": "while (i < 10) { ... }",
                "example_c": "while (i < 10) { ... }"
            },
            {
                "name": "ForStmt",
                "purpose": "Represents a for loop",
                "inherits_from": "Stmt",
                "key_methods": [
                    "getInit() - Initialization statement",
                    "getCond() - Loop condition",
                    "getInc() - Increment expression",
                    "getBody() - Loop body"
                ],
                "used_for": ["For loops"],
                "c_equivalent": "C for loop (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct mapping. All parts are optional.",
                "example_cpp": "for (int i = 0; i < 10; i++) { ... }",
                "example_c": "for (int i = 0; i < 10; i++) { ... }"
            },
            {
                "name": "SwitchStmt",
                "purpose": "Represents a switch statement",
                "inherits_from": "Stmt",
                "key_methods": [
                    "getCond() - Switch condition expression",
                    "getBody() - Switch body (CompoundStmt with cases)"
                ],
                "used_for": ["Switch statements"],
                "c_equivalent": "C switch statement (same syntax)",
                "complexity": 2,
                "translation_notes": "Direct mapping. Enum constants need translation.",
                "example_cpp": "switch (x) { case 1: ... }",
                "example_c": "switch (x) { case 1: ... }"
            },
            {
                "name": "CaseStmt",
                "purpose": "Represents a case label in switch statement",
                "inherits_from": "SwitchCase → Stmt",
                "key_methods": [
                    "getLHS() - Case value expression",
                    "getRHS() - End of range (for case X ... Y:)",
                    "getSubStmt() - Statement after case label"
                ],
                "used_for": ["Case labels in switch"],
                "c_equivalent": "C case label (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct mapping. Translate case value expression.",
                "example_cpp": "case 42:",
                "example_c": "case 42:"
            },
            {
                "name": "DefaultStmt",
                "purpose": "Represents a default label in switch statement",
                "inherits_from": "SwitchCase → Stmt",
                "key_methods": [
                    "getSubStmt() - Statement after default label"
                ],
                "used_for": ["Default label in switch"],
                "c_equivalent": "C default label (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct mapping.",
                "example_cpp": "default:",
                "example_c": "default:"
            },
            {
                "name": "BreakStmt",
                "purpose": "Represents a break statement",
                "inherits_from": "Stmt",
                "key_methods": [],
                "used_for": ["Breaking out of loops or switch"],
                "c_equivalent": "C break statement (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct mapping.",
                "example_cpp": "break;",
                "example_c": "break;"
            },
            {
                "name": "ContinueStmt",
                "purpose": "Represents a continue statement",
                "inherits_from": "Stmt",
                "key_methods": [],
                "used_for": ["Continuing to next loop iteration"],
                "c_equivalent": "C continue statement (same syntax)",
                "complexity": 1,
                "translation_notes": "Direct mapping.",
                "example_cpp": "continue;",
                "example_c": "continue;"
            }
        ]
    }

def create_class_nodes_catalog():
    """Catalog of AST nodes for classes and structs"""
    return {
        "category": "class_struct",
        "description": "AST nodes for C++ classes, structs, and member functions",
        "nodes": [
            {
                "name": "RecordDecl",
                "purpose": "Represents a C struct declaration",
                "inherits_from": "TagDecl → TypeDecl → NamedDecl → Decl",
                "key_methods": [
                    "field_begin(), field_end() - Iterators over fields",
                    "isStruct() - True for struct",
                    "isUnion() - True for union"
                ],
                "used_for": ["C structs", "C unions"],
                "c_equivalent": "C struct (direct mapping)",
                "complexity": 2,
                "translation_notes": "Direct mapping for pure C structs.",
                "example_cpp": "struct Point { int x; int y; };",
                "example_c": "struct Point { int x; int y; };"
            },
            {
                "name": "CXXRecordDecl",
                "purpose": "Represents a C++ class or struct declaration",
                "inherits_from": "RecordDecl → TagDecl → TypeDecl → NamedDecl → Decl",
                "key_methods": [
                    "bases() - Iterator over base classes",
                    "methods() - Iterator over member functions",
                    "ctors() - Iterator over constructors",
                    "hasDefinition() - True if class is defined",
                    "isAbstract() - True if has pure virtual methods"
                ],
                "used_for": ["C++ classes", "C++ structs with methods"],
                "c_equivalent": "C struct (methods become separate functions)",
                "complexity": 3,
                "translation_notes": "Translate to C struct. Methods become functions with 'this' parameter.",
                "example_cpp": "class Counter { int count; void inc(); };",
                "example_c": "struct Counter { int count; }; void Counter_inc(struct Counter* this);"
            },
            {
                "name": "FieldDecl",
                "purpose": "Represents a field (member variable) in a struct/class",
                "inherits_from": "DeclaratorDecl → ValueDecl → NamedDecl → Decl",
                "key_methods": [
                    "getType() - Field type",
                    "getAccess() - Access specifier (public/private/protected)"
                ],
                "used_for": ["Struct/class fields"],
                "c_equivalent": "C struct field",
                "complexity": 1,
                "translation_notes": "Direct mapping. All fields become public in C struct.",
                "example_cpp": "private: int count;",
                "example_c": "int count;"
            },
            {
                "name": "CXXMethodDecl",
                "purpose": "Represents a C++ member function",
                "inherits_from": "FunctionDecl → DeclaratorDecl → ValueDecl → NamedDecl → Decl",
                "key_methods": [
                    "isVirtual() - True if virtual method",
                    "isStatic() - True if static method",
                    "isConst() - True if const method",
                    "getParent() - Returns CXXRecordDecl of containing class"
                ],
                "used_for": ["Member functions"],
                "c_equivalent": "C function with explicit 'this' parameter",
                "complexity": 3,
                "translation_notes": "Add 'struct ClassName* this' as first parameter. Name becomes ClassName_methodName.",
                "example_cpp": "void Counter::increment() { count++; }",
                "example_c": "void Counter_increment(struct Counter* this) { this->count++; }"
            },
            {
                "name": "CXXConstructorDecl",
                "purpose": "Represents a C++ constructor",
                "inherits_from": "CXXMethodDecl → FunctionDecl → DeclaratorDecl → ValueDecl → NamedDecl → Decl",
                "key_methods": [
                    "inits() - Iterator over member initializers",
                    "isDefaultConstructor() - True if default constructor",
                    "isCopyConstructor() - True if copy constructor"
                ],
                "used_for": ["Constructors"],
                "c_equivalent": "C initialization function",
                "complexity": 3,
                "translation_notes": "Translate to ClassName__ctor function with 'this' parameter. Initialize fields.",
                "example_cpp": "Counter::Counter(int n) : count(n) {}",
                "example_c": "void Counter__ctor(struct Counter* this, int n) { this->count = n; }"
            },
            {
                "name": "CXXDestructorDecl",
                "purpose": "Represents a C++ destructor",
                "inherits_from": "CXXMethodDecl → FunctionDecl → DeclaratorDecl → ValueDecl → NamedDecl → Decl",
                "key_methods": [
                    "isVirtual() - True if virtual destructor"
                ],
                "used_for": ["Destructors"],
                "c_equivalent": "C cleanup function",
                "complexity": 3,
                "translation_notes": "Translate to ClassName__dtor function. Call cleanup for fields.",
                "example_cpp": "~Counter() { /* cleanup */ }",
                "example_c": "void Counter__dtor(struct Counter* this) { /* cleanup */ }"
            },
            {
                "name": "MemberExpr",
                "purpose": "Represents a member access expression (obj.field or ptr->field)",
                "inherits_from": "Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getBase() - Base expression (object being accessed)",
                    "getMemberDecl() - The field or method being accessed",
                    "isArrow() - True for -> operator"
                ],
                "used_for": ["Field access", "Method access"],
                "c_equivalent": "C field access (. or ->)",
                "complexity": 2,
                "translation_notes": "For field access, direct mapping. For methods, see CXXMemberCallExpr.",
                "example_cpp": "obj.count, ptr->count",
                "example_c": "obj.count, ptr->count"
            },
            {
                "name": "CXXMemberCallExpr",
                "purpose": "Represents a call to a member function",
                "inherits_from": "CallExpr → Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getImplicitObjectArgument() - Returns object expression (this)",
                    "getMethodDecl() - Returns CXXMethodDecl being called"
                ],
                "used_for": ["Method calls"],
                "c_equivalent": "C function call with object as first argument",
                "complexity": 3,
                "translation_notes": "Translate obj.method(args) to ClassName_method(&obj, args).",
                "example_cpp": "counter.increment()",
                "example_c": "Counter_increment(&counter)"
            },
            {
                "name": "CXXThisExpr",
                "purpose": "Represents the 'this' pointer in member functions",
                "inherits_from": "Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getType() - Type of 'this' (pointer to class)"
                ],
                "used_for": ["'this' references in methods"],
                "c_equivalent": "C function parameter 'this'",
                "complexity": 2,
                "translation_notes": "Replace with 'this' parameter name.",
                "example_cpp": "this->count",
                "example_c": "this->count"
            },
            {
                "name": "CXXOperatorCallExpr",
                "purpose": "Represents a call to an overloaded operator",
                "inherits_from": "CallExpr → Expr → ValueStmt → Stmt",
                "key_methods": [
                    "getOperator() - Returns operator kind (OO_Plus, OO_EqualEqual, etc.)",
                    "getNumArgs() - Number of operands"
                ],
                "used_for": ["Overloaded operators (operator+, operator==, etc.)"],
                "c_equivalent": "C function call",
                "complexity": 4,
                "translation_notes": "Translate to function call: ClassName_operator_add(lhs, rhs).",
                "example_cpp": "a + b // where + is overloaded",
                "example_c": "Vector_operator_add(&a, &b)"
            }
        ]
    }

def create_advanced_nodes_catalog():
    """Catalog of AST nodes for advanced C++ features"""
    return {
        "category": "advanced",
        "description": "AST nodes for templates, inheritance, enums, and advanced type system",
        "nodes": [
            {
                "name": "EnumDecl",
                "purpose": "Represents an enum declaration (scoped or unscoped)",
                "inherits_from": "TagDecl → TypeDecl → NamedDecl → Decl",
                "key_methods": [
                    "enumerators() - Iterator over enum constants",
                    "isScoped() - True for enum class",
                    "getIntegerType() - Underlying integer type"
                ],
                "used_for": ["Enum declarations"],
                "c_equivalent": "C enum (unscoped) or enum with prefixed names (scoped)",
                "complexity": 2,
                "translation_notes": "Unscoped: direct mapping. Scoped: prefix constants with EnumName__.",
                "example_cpp": "enum class State { Idle, Running };",
                "example_c": "enum State { State__Idle, State__Running };"
            },
            {
                "name": "EnumConstantDecl",
                "purpose": "Represents a single enumerator constant",
                "inherits_from": "ValueDecl → NamedDecl → Decl",
                "key_methods": [
                    "getInitVal() - Returns integer value",
                    "getInitExpr() - Returns initializer expression"
                ],
                "used_for": ["Enum constants"],
                "c_equivalent": "C enum constant",
                "complexity": 1,
                "translation_notes": "For scoped enums, prefix with enum name.",
                "example_cpp": "Idle, Running",
                "example_c": "State__Idle, State__Running"
            },
            {
                "name": "CXXBaseSpecifier",
                "purpose": "Represents a base class in inheritance hierarchy",
                "inherits_from": "Not a Decl - standalone class",
                "key_methods": [
                    "getType() - Type of base class",
                    "isVirtual() - True for virtual inheritance",
                    "getAccessSpecifier() - public/protected/private"
                ],
                "used_for": ["Base class specifications in inheritance"],
                "c_equivalent": "Embedded struct or struct composition",
                "complexity": 4,
                "translation_notes": "Embed base class struct as first field. Adjust field offsets.",
                "example_cpp": "class Derived : public Base",
                "example_c": "struct Derived { struct Base base; /* derived fields */ };"
            },
            {
                "name": "ClassTemplateDecl",
                "purpose": "Represents a class template declaration",
                "inherits_from": "RedeclarableTemplateDecl → TemplateDecl → NamedDecl → Decl",
                "key_methods": [
                    "getTemplateParameters() - Returns template parameter list",
                    "specializations() - Iterator over specializations",
                    "getTemplatedDecl() - Returns CXXRecordDecl"
                ],
                "used_for": ["Class templates"],
                "c_equivalent": "Multiple concrete structs (one per instantiation)",
                "complexity": 5,
                "translation_notes": "Monomorphization: create separate struct for each instantiation. Name: ClassName_T1_T2.",
                "example_cpp": "template<typename T> class Box { T value; };",
                "example_c": "struct Box_int { int value; }; struct Box_float { float value; };"
            },
            {
                "name": "FunctionTemplateDecl",
                "purpose": "Represents a function template declaration",
                "inherits_from": "RedeclarableTemplateDecl → TemplateDecl → NamedDecl → Decl",
                "key_methods": [
                    "getTemplateParameters() - Returns template parameter list",
                    "specializations() - Iterator over specializations",
                    "getTemplatedDecl() - Returns FunctionDecl"
                ],
                "used_for": ["Function templates"],
                "c_equivalent": "Multiple concrete functions (one per instantiation)",
                "complexity": 5,
                "translation_notes": "Monomorphization: create separate function for each instantiation. Name: funcName_T1_T2.",
                "example_cpp": "template<typename T> T max(T a, T b);",
                "example_c": "int max_int(int a, int b); float max_float(float a, float b);"
            },
            {
                "name": "TemplateTypeParmDecl",
                "purpose": "Represents a template type parameter",
                "inherits_from": "TypeDecl → NamedDecl → Decl",
                "key_methods": [
                    "hasDefaultArgument() - True if has default type",
                    "getDefaultArgument() - Returns default type"
                ],
                "used_for": ["Template type parameters (typename T, class T)"],
                "c_equivalent": "Replaced with concrete type in monomorphization",
                "complexity": 5,
                "translation_notes": "Substitute with actual type during instantiation.",
                "example_cpp": "typename T, class U",
                "example_c": "int, float // after substitution"
            },
            {
                "name": "ClassTemplateSpecializationDecl",
                "purpose": "Represents an instantiation of a class template",
                "inherits_from": "CXXRecordDecl → RecordDecl → TagDecl → TypeDecl → NamedDecl → Decl",
                "key_methods": [
                    "getTemplateArgs() - Returns template arguments",
                    "getSpecializedTemplate() - Returns ClassTemplateDecl"
                ],
                "used_for": ["Template instantiations (Box<int>, Box<float>)"],
                "c_equivalent": "Concrete struct with substituted types",
                "complexity": 5,
                "translation_notes": "This is the result of monomorphization. Generate concrete struct.",
                "example_cpp": "Box<int> intBox;",
                "example_c": "struct Box_int { int value; }; struct Box_int intBox;"
            },
            {
                "name": "NamespaceDecl",
                "purpose": "Represents a namespace declaration",
                "inherits_from": "NamedDecl → Decl",
                "key_methods": [
                    "decls() - Iterator over declarations in namespace",
                    "getNameAsString() - Namespace name"
                ],
                "used_for": ["Namespace declarations"],
                "c_equivalent": "Name prefix for all declarations",
                "complexity": 3,
                "translation_notes": "Prefix all names with namespace: namespace_name_symbol_name.",
                "example_cpp": "namespace math { int add(int a, int b); }",
                "example_c": "int math_add(int a, int b);"
            },
            {
                "name": "QualType",
                "purpose": "Represents a type with qualifiers (const, volatile)",
                "inherits_from": "Not a Decl - type wrapper",
                "key_methods": [
                    "getTypePtr() - Returns underlying Type*",
                    "isConstQualified() - True if const",
                    "isVolatileQualified() - True if volatile"
                ],
                "used_for": ["All types in Clang AST"],
                "c_equivalent": "C type with qualifiers",
                "complexity": 2,
                "translation_notes": "Preserve const/volatile qualifiers. Extract underlying type.",
                "example_cpp": "const int, volatile float*",
                "example_c": "const int, volatile float*"
            },
            {
                "name": "BuiltinType",
                "purpose": "Represents a built-in type (int, float, char, etc.)",
                "inherits_from": "Type",
                "key_methods": [
                    "getKind() - Returns kind (Int, Float, Char, etc.)",
                    "getName() - Returns type name as string"
                ],
                "used_for": ["Primitive types"],
                "c_equivalent": "C built-in types (same)",
                "complexity": 1,
                "translation_notes": "Direct mapping. Handle bool -> int.",
                "example_cpp": "int, float, double, bool",
                "example_c": "int, float, double, int // bool -> int"
            },
            {
                "name": "PointerType",
                "purpose": "Represents a pointer type",
                "inherits_from": "Type",
                "key_methods": [
                    "getPointeeType() - Returns type being pointed to"
                ],
                "used_for": ["Pointer types"],
                "c_equivalent": "C pointer type (same)",
                "complexity": 1,
                "translation_notes": "Direct mapping.",
                "example_cpp": "int*, char**",
                "example_c": "int*, char**"
            },
            {
                "name": "ReferenceType",
                "purpose": "Represents a reference type (C++ only)",
                "inherits_from": "Type",
                "key_methods": [
                    "getPointeeType() - Returns type being referenced"
                ],
                "used_for": ["Reference types (T&, T&&)"],
                "c_equivalent": "C pointer type",
                "complexity": 2,
                "translation_notes": "Convert references to pointers. T& -> T*.",
                "example_cpp": "int&, const std::string&",
                "example_c": "int*, const char*"
            },
            {
                "name": "RecordType",
                "purpose": "Represents a struct/class/union type",
                "inherits_from": "Type",
                "key_methods": [
                    "getDecl() - Returns RecordDecl or CXXRecordDecl"
                ],
                "used_for": ["Struct/class types"],
                "c_equivalent": "C struct type",
                "complexity": 2,
                "translation_notes": "Map to C struct type. Use translated struct name.",
                "example_cpp": "Counter, std::vector<int>",
                "example_c": "struct Counter, struct vector_int"
            },
            {
                "name": "TemplateSpecializationType",
                "purpose": "Represents a template specialization type",
                "inherits_from": "Type",
                "key_methods": [
                    "getTemplateName() - Template being specialized",
                    "getArgs() - Template arguments"
                ],
                "used_for": ["Template instantiation types (Box<int>)"],
                "c_equivalent": "Concrete struct type after monomorphization",
                "complexity": 5,
                "translation_notes": "Map to monomorphized struct name.",
                "example_cpp": "Box<int>, std::vector<float>",
                "example_c": "struct Box_int, struct vector_float"
            }
        ]
    }

def main():
    # Create output directory if it doesn't exist
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Generate catalogs
    catalogs = {
        "basic-ast-nodes.json": create_basic_nodes_catalog(),
        "class-ast-nodes.json": create_class_nodes_catalog(),
        "advanced-ast-nodes.json": create_advanced_nodes_catalog()
    }

    # Write JSON files
    for filename, catalog in catalogs.items():
        filepath = OUTPUT_DIR / filename
        with open(filepath, 'w') as f:
            json.dump(catalog, f, indent=2)
        print(f"Created: {filepath}")
        print(f"  - {len(catalog['nodes'])} nodes in category '{catalog['category']}'")

    print("\nAll catalogs generated successfully!")

if __name__ == "__main__":
    main()
