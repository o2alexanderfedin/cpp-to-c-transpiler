/**
 * @file CNodeBuilder.h
 * @brief Helper library for creating Clang C AST nodes with clean, readable API
 *
 * CNodeBuilder encapsulates verbose Clang node creation, reducing boilerplate
 * from 15+ lines to 1 line per node. This enables maintainable C AST construction
 * for the C++ to C transpiler.
 *
 * Design Principles:
 * - SOLID: Single Responsibility (node creation only), Open/Closed (easy to extend)
 * - KISS: Each method does one thing with clear naming
 * - DRY: Common patterns (SourceLocation, TypeSourceInfo) extracted
 * - YAGNI: Only helpers needed for Epic #3 translation
 *
 * Usage Example:
 * @code
 *   CNodeBuilder builder(Context);
 *   VarDecl *x = builder.intVar("x", 42);  // 1 line instead of 15+
 * @endcode
 *
 * @see Epic #2: CNodeBuilder Helper Library
 * @see https://github.com/o2alexanderfedin/cpp-to-c-transpiler/issues/2
 */

#ifndef CNODEBUILDER_H
#define CNODEBUILDER_H

#include "llvm/Config/llvm-config.h"  // For LLVM_VERSION_MAJOR
#include "clang/AST/ASTContext.h"
#include "clang/AST/Decl.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Type.h"

namespace clang {

/**
 * @class CNodeBuilder
 * @brief Helper class for creating Clang C AST nodes with minimal boilerplate
 *
 * This class provides a clean, fluent API for constructing C AST nodes.
 * All nodes are owned by the ASTContext (no manual memory management needed).
 *
 * Story #9: Type helpers (intType, structType, ptrType, voidType, charType)
 */
class CNodeBuilder {
private:
    /// Reference to ASTContext for node allocation
    ASTContext &Ctx;

public:
    /**
     * @brief Construct a new CNodeBuilder
     * @param Ctx ASTContext reference for node creation
     *
     * The ASTContext owns all created nodes - no manual cleanup needed.
     */
    explicit CNodeBuilder(ASTContext &Ctx) : Ctx(Ctx) {}

    // ========================================================================
    // Type Helpers (Story #9)
    // ========================================================================

    /**
     * @brief Create int type (C int)
     * @return QualType representing int
     *
     * Example:
     * @code
     *   QualType intTy = builder.intType();
     * @endcode
     */
    QualType intType() {
        return Ctx.IntTy;
    }

    /**
     * @brief Create void type (C void)
     * @return QualType representing void
     *
     * Used for function return types and void pointers.
     *
     * Example:
     * @code
     *   QualType voidTy = builder.voidType();
     * @endcode
     */
    QualType voidType() {
        return Ctx.VoidTy;
    }

    /**
     * @brief Create char type (C char)
     * @return QualType representing char
     *
     * Used for strings and character arrays.
     *
     * Example:
     * @code
     *   QualType charTy = builder.charType();
     * @endcode
     */
    QualType charType() {
        return Ctx.CharTy;
    }

    /**
     * @brief Create pointer type (T*)
     * @param pointee The type being pointed to
     * @return QualType representing pointer to pointee
     *
     * Example:
     * @code
     *   QualType intPtrTy = builder.ptrType(builder.intType());
     * @endcode
     */
    QualType ptrType(QualType pointee) {
        return Ctx.getPointerType(pointee);
    }

    /**
     * @brief Create struct type by name
     * @param name Name of the struct
     * @return QualType representing struct type
     *
     * Creates an incomplete type reference to a struct.
     * The struct declaration must exist or be created separately.
     *
     * Example:
     * @code
     *   QualType pointTy = builder.structType("Point");
     * @endcode
     *
     * @note This creates a type reference, not the struct definition itself.
     *       Use structDecl() (Story #13) to define the struct.
     */
    QualType structType(llvm::StringRef name) {
        // Create incomplete record type
        // The actual RecordDecl will be created in Story #13
        IdentifierInfo &II = Ctx.Idents.get(name);

        // Create a tag declaration for the struct
        RecordDecl *RD = RecordDecl::Create(
            Ctx,
#if LLVM_VERSION_MAJOR >= 16
            TagTypeKind::Struct,
#else
            TTK_Struct,
#endif
            Ctx.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            &II
        );

        // Return the type
        return Ctx.getRecordType(RD);
    }

    // ========================================================================
    // Variable Declaration Helpers (Story #10)
    // ========================================================================

    /**
     * @brief Create int variable with initializer
     * @param name Variable name
     * @param initVal Initial value
     * @return VarDecl* for int variable
     *
     * Example:
     * @code
     *   VarDecl *x = builder.intVar("x", 42);  // int x = 42;
     * @endcode
     */
    VarDecl* intVar(llvm::StringRef name, int initVal) {
        QualType intTy = intType();
        IdentifierInfo &II = Ctx.Idents.get(name);

        VarDecl *VD = VarDecl::Create(
            Ctx,
            Ctx.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            &II,
            intTy,
            Ctx.getTrivialTypeSourceInfo(intTy),
            SC_None
        );

        // Create initializer
        IntegerLiteral *IL = IntegerLiteral::Create(
            Ctx,
            llvm::APInt(32, initVal),
            intTy,
            SourceLocation()
        );
        VD->setInit(IL);

        return VD;
    }

    /**
     * @brief Create int variable without initializer
     * @param name Variable name
     * @return VarDecl* for int variable
     *
     * Example:
     * @code
     *   VarDecl *x = builder.intVar("x");  // int x;
     * @endcode
     */
    VarDecl* intVar(llvm::StringRef name) {
        QualType intTy = intType();
        IdentifierInfo &II = Ctx.Idents.get(name);

        return VarDecl::Create(
            Ctx,
            Ctx.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            &II,
            intTy,
            Ctx.getTrivialTypeSourceInfo(intTy),
            SC_None
        );
    }

    /**
     * @brief Create struct variable
     * @param type Struct type
     * @param name Variable name
     * @return VarDecl* for struct variable
     *
     * Example:
     * @code
     *   VarDecl *p = builder.structVar(pointTy, "p");  // struct Point p;
     * @endcode
     */
    VarDecl* structVar(QualType type, llvm::StringRef name) {
        IdentifierInfo &II = Ctx.Idents.get(name);

        return VarDecl::Create(
            Ctx,
            Ctx.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            &II,
            type,
            Ctx.getTrivialTypeSourceInfo(type),
            SC_None
        );
    }

    /**
     * @brief Create pointer variable
     * @param pointee Type being pointed to
     * @param name Variable name
     * @return VarDecl* for pointer variable
     *
     * Example:
     * @code
     *   VarDecl *ptr = builder.ptrVar(intType(), "ptr");  // int *ptr;
     * @endcode
     */
    VarDecl* ptrVar(QualType pointee, llvm::StringRef name) {
        QualType ptrTy = ptrType(pointee);
        IdentifierInfo &II = Ctx.Idents.get(name);

        return VarDecl::Create(
            Ctx,
            Ctx.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            &II,
            ptrTy,
            Ctx.getTrivialTypeSourceInfo(ptrTy),
            SC_None
        );
    }

    /**
     * @brief Create generic variable declaration
     * @param type Variable type
     * @param name Variable name
     * @param init Optional initializer expression
     * @return VarDecl* for variable
     *
     * Example:
     * @code
     *   VarDecl *v = builder.var(charType(), "c", builder.intLit('A'));
     * @endcode
     */
    VarDecl* var(QualType type, llvm::StringRef name, Expr* init = nullptr) {
        IdentifierInfo &II = Ctx.Idents.get(name);

        VarDecl *VD = VarDecl::Create(
            Ctx,
            Ctx.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            &II,
            type,
            Ctx.getTrivialTypeSourceInfo(type),
            SC_None
        );

        if (init) {
            VD->setInit(init);
        }

        return VD;
    }

    // ========================================================================
    // Expression Helpers (Story #11)
    // ========================================================================

    /**
     * @brief Create integer literal
     * @param value Integer value
     * @return IntegerLiteral* expression
     *
     * Example:
     * @code
     *   Expr *lit = builder.intLit(42);
     * @endcode
     */
    IntegerLiteral* intLit(int value) {
        return IntegerLiteral::Create(
            Ctx,
            llvm::APInt(32, value),
            intType(),
            SourceLocation()
        );
    }

    /**
     * @brief Create string literal
     * @param str String content
     * @return StringLiteral* expression
     *
     * Example:
     * @code
     *   Expr *str = builder.stringLit("Hello");
     * @endcode
     */
    StringLiteral* stringLit(llvm::StringRef str) {
        return StringLiteral::Create(
            Ctx,
            str,
#if LLVM_VERSION_MAJOR >= 16
            StringLiteralKind::Ordinary,
#else
            StringLiteral::Ordinary,
#endif
            false,
            Ctx.getConstantArrayType(
                charType(),
                llvm::APInt(32, str.size() + 1),
                nullptr,
#if LLVM_VERSION_MAJOR >= 16
                ArraySizeModifier::Normal,
#else
                ArrayType::ArraySizeModifier::Normal,
#endif
                0
            ),
            SourceLocation()
        );
    }

    /**
     * @brief Create NULL pointer literal
     * @return Expr* representing NULL
     *
     * Example:
     * @code
     *   Expr *null = builder.nullPtr();
     * @endcode
     */
    Expr* nullPtr() {
        return IntegerLiteral::Create(
            Ctx,
            llvm::APInt(32, 0),
            intType(),
            SourceLocation()
        );
    }

    /**
     * @brief Create variable reference
     * @param var VarDecl to reference
     * @return DeclRefExpr* expression
     *
     * Example:
     * @code
     *   Expr *ref = builder.ref(xVar);
     * @endcode
     */
    DeclRefExpr* ref(VarDecl* var) {
        return DeclRefExpr::Create(
            Ctx,
            NestedNameSpecifierLoc(),
            SourceLocation(),
            var,
            false,
            SourceLocation(),
            var->getType(),
            VK_LValue
        );
    }

    /**
     * @brief Create function reference
     * @param func FunctionDecl to reference
     * @return DeclRefExpr* expression
     *
     * Example:
     * @code
     *   Expr *funcRef = builder.ref(printfDecl);
     * @endcode
     */
    DeclRefExpr* ref(FunctionDecl* func) {
        return DeclRefExpr::Create(
            Ctx,
            NestedNameSpecifierLoc(),
            SourceLocation(),
            func,
            false,
            SourceLocation(),
            func->getType(),
            VK_LValue
        );
    }

    /**
     * @brief Create function call by name
     * @param funcName Function name
     * @param args Argument expressions
     * @return CallExpr* expression
     *
     * Example:
     * @code
     *   CallExpr *call = builder.call("printf", {strLit, varRef});
     * @endcode
     */
    CallExpr* call(llvm::StringRef funcName, llvm::ArrayRef<Expr*> args) {
        // Create function reference
        IdentifierInfo &II = Ctx.Idents.get(funcName);
        DeclarationName DN(&II);

        // Create a builtin function type (simplified)
        QualType funcType = Ctx.getFunctionType(intType(), {}, {});

        FunctionDecl *FD = FunctionDecl::Create(
            Ctx,
            Ctx.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            DN,
            funcType,
            nullptr,
            SC_Extern
        );

        DeclRefExpr *funcRef = ref(FD);

        return CallExpr::Create(
            Ctx,
            funcRef,
            args,
            intType(),
            VK_PRValue,
            SourceLocation(),
            FPOptionsOverride()
        );
    }

    /**
     * @brief Create function call from declaration
     * @param func FunctionDecl
     * @param args Argument expressions
     * @return CallExpr* expression
     *
     * Example:
     * @code
     *   CallExpr *call = builder.call(funcDecl, {arg1, arg2});
     * @endcode
     */
    CallExpr* call(FunctionDecl* func, llvm::ArrayRef<Expr*> args) {
        DeclRefExpr *funcRef = ref(func);

        return CallExpr::Create(
            Ctx,
            funcRef,
            args,
            func->getReturnType(),
            VK_PRValue,
            SourceLocation(),
            FPOptionsOverride()
        );
    }

    /**
     * @brief Create struct member access (.)
     * @param base Base expression
     * @param field Field name
     * @return MemberExpr* expression
     *
     * Example:
     * @code
     *   Expr *access = builder.member(structRef, "x");  // s.x
     * @endcode
     */
    MemberExpr* member(Expr* base, llvm::StringRef field) {
        // Get the record type from base
        QualType baseTy = base->getType();
        const RecordType *RT = baseTy->getAs<RecordType>();
        if (!RT) return nullptr;

        RecordDecl *RD = RT->getDecl();

        // Find the field
        FieldDecl *FD = nullptr;
        for (auto *Field : RD->fields()) {
            if (Field->getName() == field) {
                FD = Field;
                break;
            }
        }

        if (!FD) return nullptr;

        return MemberExpr::Create(
            Ctx,
            base,
            false,  // not arrow
            SourceLocation(),
            NestedNameSpecifierLoc(),
            SourceLocation(),
            FD,
            DeclAccessPair::make(FD, AS_public),
            DeclarationNameInfo(),
            nullptr,
            FD->getType(),
            VK_LValue,
            OK_Ordinary,
            NOUR_None
        );
    }

    /**
     * @brief Create pointer member access (->)
     * @param base Base pointer expression
     * @param field Field name
     * @return MemberExpr* expression
     *
     * Example:
     * @code
     *   Expr *access = builder.arrowMember(ptrRef, "x");  // p->x
     * @endcode
     */
    MemberExpr* arrowMember(Expr* base, llvm::StringRef field) {
        // Dereference pointer to get record type
        QualType baseTy = base->getType();
        const PointerType *PT = baseTy->getAs<PointerType>();
        if (!PT) return nullptr;

        QualType pointeeTy = PT->getPointeeType();
        const RecordType *RT = pointeeTy->getAs<RecordType>();
        if (!RT) return nullptr;

        RecordDecl *RD = RT->getDecl();

        // Find the field
        FieldDecl *FD = nullptr;
        for (auto *Field : RD->fields()) {
            if (Field->getName() == field) {
                FD = Field;
                break;
            }
        }

        if (!FD) return nullptr;

        return MemberExpr::Create(
            Ctx,
            base,
            true,  // is arrow
            SourceLocation(),
            NestedNameSpecifierLoc(),
            SourceLocation(),
            FD,
            DeclAccessPair::make(FD, AS_public),
            DeclarationNameInfo(),
            nullptr,
            FD->getType(),
            VK_LValue,
            OK_Ordinary,
            NOUR_None
        );
    }

    /**
     * @brief Create assignment expression
     * @param lhs Left-hand side
     * @param rhs Right-hand side
     * @return BinaryOperator* expression
     *
     * Example:
     * @code
     *   Expr *assign = builder.assign(varRef, intLit(5));  // x = 5
     * @endcode
     */
    BinaryOperator* assign(Expr* lhs, Expr* rhs) {
        return BinaryOperator::Create(
            Ctx,
            lhs,
            rhs,
            BO_Assign,
            lhs->getType(),
            VK_PRValue,
            OK_Ordinary,
            SourceLocation(),
            FPOptionsOverride()
        );
    }

    /**
     * @brief Create address-of expression (&)
     * @param expr Expression to take address of
     * @return UnaryOperator* expression
     *
     * Example:
     * @code
     *   Expr *addr = builder.addrOf(varRef);  // &x
     * @endcode
     */
    UnaryOperator* addrOf(Expr* expr) {
        return UnaryOperator::Create(
            Ctx,
            expr,
            UO_AddrOf,
            ptrType(expr->getType()),
            VK_PRValue,
            OK_Ordinary,
            SourceLocation(),
            false,
            FPOptionsOverride()
        );
    }

    /**
     * @brief Create dereference expression (*)
     * @param expr Expression to dereference
     * @return UnaryOperator* expression
     *
     * Example:
     * @code
     *   Expr *deref = builder.deref(ptrRef);  // *p
     * @endcode
     */
    UnaryOperator* deref(Expr* expr) {
        QualType exprTy = expr->getType();
        const PointerType *PT = exprTy->getAs<PointerType>();
        if (!PT) return nullptr;

        return UnaryOperator::Create(
            Ctx,
            expr,
            UO_Deref,
            PT->getPointeeType(),
            VK_LValue,
            OK_Ordinary,
            SourceLocation(),
            false,
            FPOptionsOverride()
        );
    }

    // ========================================================================
    // Statement Helpers (Story #12)
    // ========================================================================

    /**
     * @brief Create compound statement (block)
     * @param stmts Array of statements
     * @return CompoundStmt* statement
     *
     * Example:
     * @code
     *   Stmt *block = builder.block({stmt1, stmt2, stmt3});  // { ... }
     * @endcode
     */
    CompoundStmt* block(llvm::ArrayRef<Stmt*> stmts) {
        return CompoundStmt::Create(
            Ctx,
            stmts,
            FPOptionsOverride(),
            SourceLocation(),
            SourceLocation()
        );
    }

    /**
     * @brief Create return statement
     * @param expr Optional return expression
     * @return ReturnStmt* statement
     *
     * Example:
     * @code
     *   Stmt *ret = builder.returnStmt(intLit(0));  // return 0;
     * @endcode
     */
    ReturnStmt* returnStmt(Expr* expr = nullptr) {
        return ReturnStmt::Create(
            Ctx,
            SourceLocation(),
            expr,
            nullptr
        );
    }

    /**
     * @brief Create declaration statement
     * @param decl Declaration
     * @return DeclStmt* statement
     *
     * Example:
     * @code
     *   Stmt *declStmt = builder.declStmt(varDecl);
     * @endcode
     */
    DeclStmt* declStmt(Decl* decl) {
        return new (Ctx) DeclStmt(
            DeclGroupRef(decl),
            SourceLocation(),
            SourceLocation()
        );
    }

    /**
     * @brief Create expression statement
     * @param expr Expression
     * @return Stmt* statement
     *
     * Example:
     * @code
     *   Stmt *exprStmt = builder.exprStmt(callExpr);
     * @endcode
     */
    Stmt* exprStmt(Expr* expr) {
        return expr;
    }

    /**
     * @brief Create if statement
     * @param cond Condition expression
     * @param thenStmt Then branch
     * @param elseStmt Optional else branch
     * @return IfStmt* statement
     *
     * Example:
     * @code
     *   Stmt *ifStmt = builder.ifStmt(cond, thenBlock, elseBlock);
     * @endcode
     */
    IfStmt* ifStmt(Expr* cond, Stmt* thenStmt, Stmt* elseStmt = nullptr) {
        return IfStmt::Create(
            Ctx,
            SourceLocation(),
            IfStatementKind::Ordinary,
            nullptr,
            nullptr,
            cond,
            SourceLocation(),
            SourceLocation(),
            thenStmt,
            SourceLocation(),
            elseStmt
        );
    }

    /**
     * @brief Create while loop
     * @param cond Condition expression
     * @param body Loop body
     * @return WhileStmt* statement
     *
     * Example:
     * @code
     *   Stmt *loop = builder.whileStmt(cond, bodyBlock);
     * @endcode
     */
    WhileStmt* whileStmt(Expr* cond, Stmt* body) {
        return WhileStmt::Create(
            Ctx,
            nullptr,
            cond,
            body,
            SourceLocation(),
            SourceLocation(),
            SourceLocation()
        );
    }

    /**
     * @brief Create for loop
     * @param init Initialization statement
     * @param cond Condition expression
     * @param inc Increment expression
     * @param body Loop body
     * @return ForStmt* statement
     *
     * Example:
     * @code
     *   Stmt *loop = builder.forStmt(init, cond, inc, bodyBlock);
     * @endcode
     */
    ForStmt* forStmt(Stmt* init, Expr* cond, Expr* inc, Stmt* body) {
        return new (Ctx) ForStmt(
            Ctx,
            init,
            cond,
            nullptr,
            inc,
            body,
            SourceLocation(),
            SourceLocation(),
            SourceLocation()
        );
    }

    /**
     * @brief Create break statement
     * @return BreakStmt* statement
     *
     * Example:
     * @code
     *   Stmt *brk = builder.breakStmt();  // break;
     * @endcode
     */
    BreakStmt* breakStmt() {
        return new (Ctx) BreakStmt(SourceLocation());
    }

    /**
     * @brief Create continue statement
     * @return ContinueStmt* statement
     *
     * Example:
     * @code
     *   Stmt *cont = builder.continueStmt();  // continue;
     * @endcode
     */
    ContinueStmt* continueStmt() {
        return new (Ctx) ContinueStmt(SourceLocation());
    }

    // ========================================================================
    // Declaration Helpers (Story #13)
    // ========================================================================

    /**
     * @brief Create struct declaration
     * @param name Struct name
     * @param fields Array of field declarations
     * @return RecordDecl* declaration
     *
     * Example:
     * @code
     *   RecordDecl *s = builder.structDecl("Point", {xField, yField});
     * @endcode
     */
    RecordDecl* structDecl(llvm::StringRef name, llvm::ArrayRef<FieldDecl*> fields) {
        IdentifierInfo &II = Ctx.Idents.get(name);

        RecordDecl *RD = RecordDecl::Create(
            Ctx,
#if LLVM_VERSION_MAJOR >= 16
            TagTypeKind::Struct,
#else
            TTK_Struct,
#endif
            Ctx.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            &II
        );

        RD->startDefinition();

        // Add fields and set their parent context
        for (FieldDecl *FD : fields) {
            FD->setDeclContext(RD);  // Set parent before adding
            RD->addDecl(FD);
        }

        RD->completeDefinition();

        return RD;
    }

    /**
     * @brief Create field declaration
     * @param type Field type
     * @param name Field name
     * @return FieldDecl* declaration
     *
     * Example:
     * @code
     *   FieldDecl *field = builder.fieldDecl(intType(), "x");
     * @endcode
     */
    FieldDecl* fieldDecl(QualType type, llvm::StringRef name) {
        IdentifierInfo &II = Ctx.Idents.get(name);

        return FieldDecl::Create(
            Ctx,
            nullptr,  // Parent will be set when added to struct
            SourceLocation(),
            SourceLocation(),
            &II,
            type,
            Ctx.getTrivialTypeSourceInfo(type),
            nullptr,
            false,
            ICIS_NoInit
        );
    }

    /**
     * @brief Create forward struct declaration
     * @param name Struct name
     * @return RecordDecl* declaration
     *
     * Example:
     * @code
     *   RecordDecl *fwd = builder.forwardStructDecl("Node");
     * @endcode
     */
    RecordDecl* forwardStructDecl(llvm::StringRef name) {
        IdentifierInfo &II = Ctx.Idents.get(name);

        return RecordDecl::Create(
            Ctx,
#if LLVM_VERSION_MAJOR >= 16
            TagTypeKind::Struct,
#else
            TTK_Struct,
#endif
            Ctx.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            &II
        );
    }

    /**
     * @brief Create function declaration
     * @param name Function name
     * @param retType Return type
     * @param params Parameter declarations
     * @param body Optional function body
     * @return FunctionDecl* declaration
     *
     * Example:
     * @code
     *   FunctionDecl *func = builder.funcDecl("foo", intType(), {p1, p2}, body);
     * @endcode
     */
    FunctionDecl* funcDecl(llvm::StringRef name, QualType retType,
                          llvm::ArrayRef<ParmVarDecl*> params,
                          Stmt* body = nullptr) {
        IdentifierInfo &II = Ctx.Idents.get(name);
        DeclarationName DN(&II);

        // Create function type
        llvm::SmallVector<QualType, 4> paramTypes;
        for (ParmVarDecl *P : params) {
            paramTypes.push_back(P->getType());
        }

        QualType funcType = Ctx.getFunctionType(retType, paramTypes, {});

        FunctionDecl *FD = FunctionDecl::Create(
            Ctx,
            Ctx.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            DN,
            funcType,
            Ctx.getTrivialTypeSourceInfo(funcType),
            SC_None
        );

        // Set parameters
        FD->setParams(params);

        // Set body if provided
        if (body) {
            FD->setBody(body);
        }

        return FD;
    }

    /**
     * @brief Create function parameter
     * @param type Parameter type
     * @param name Parameter name
     * @return ParmVarDecl* declaration
     *
     * Example:
     * @code
     *   ParmVarDecl *param = builder.param(intType(), "x");
     * @endcode
     */
    ParmVarDecl* param(QualType type, llvm::StringRef name) {
        IdentifierInfo &II = Ctx.Idents.get(name);

        return ParmVarDecl::Create(
            Ctx,
            nullptr,  // Parent will be set when added to function
            SourceLocation(),
            SourceLocation(),
            &II,
            type,
            Ctx.getTrivialTypeSourceInfo(type),
            SC_None,
            nullptr
        );
    }
};

} // namespace clang

#endif // CNODEBUILDER_H
