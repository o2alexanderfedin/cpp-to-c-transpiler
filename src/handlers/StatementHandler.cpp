/**
 * @file StatementHandler.cpp
 * @brief Implementation of StatementHandler
 *
 * TDD Implementation: Start minimal, add complexity as tests demand.
 *
 * Translation Strategy:
 * - Most statements translate directly (same syntax in C and C++)
 * - Key work is recursively translating sub-statements and expressions
 * - Delegate to ExpressionHandler for expressions
 * - Delegate to VariableHandler for declarations
 */

#include "handlers/StatementHandler.h"
#include "handlers/HandlerContext.h"
#include "clang/AST/Stmt.h"
#include "clang/AST/Expr.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

bool StatementHandler::canHandle(const clang::Stmt* S) const {
    if (!S) return false;

    // Handle return, compound, and control flow statements (Phase 1-2)
    // Task 5: While loops, Task 6: Do-while, Task 7: For loops
    // Goto and Label statements
    // Task 9: Declaration statements (for object lifecycle)
    switch (S->getStmtClass()) {
        case clang::Stmt::ReturnStmtClass:
        case clang::Stmt::CompoundStmtClass:
        case clang::Stmt::IfStmtClass:
        case clang::Stmt::WhileStmtClass:
        case clang::Stmt::DoStmtClass:
        case clang::Stmt::ForStmtClass:
        case clang::Stmt::SwitchStmtClass:
        case clang::Stmt::CaseStmtClass:
        case clang::Stmt::DefaultStmtClass:
        case clang::Stmt::BreakStmtClass:
        case clang::Stmt::ContinueStmtClass:
        case clang::Stmt::GotoStmtClass:
        case clang::Stmt::LabelStmtClass:
        case clang::Stmt::DeclStmtClass:
            return true;
        default:
            return false;
    }
}

clang::Stmt* StatementHandler::handleStmt(const clang::Stmt* S, HandlerContext& ctx) {
    if (!S) return nullptr;

    switch (S->getStmtClass()) {
        case clang::Stmt::ReturnStmtClass:
            return translateReturnStmt(llvm::cast<clang::ReturnStmt>(S), ctx);

        case clang::Stmt::CompoundStmtClass:
            return translateCompoundStmt(llvm::cast<clang::CompoundStmt>(S), ctx);

        case clang::Stmt::IfStmtClass:
            return translateIfStmt(llvm::cast<clang::IfStmt>(S), ctx);

        case clang::Stmt::WhileStmtClass:
            return translateWhileStmt(llvm::cast<clang::WhileStmt>(S), ctx);

        case clang::Stmt::DoStmtClass:
            return translateDoStmt(llvm::cast<clang::DoStmt>(S), ctx);

        case clang::Stmt::ForStmtClass:
            return translateForStmt(llvm::cast<clang::ForStmt>(S), ctx);

        case clang::Stmt::SwitchStmtClass:
            return translateSwitchStmt(llvm::cast<clang::SwitchStmt>(S), ctx);

        case clang::Stmt::CaseStmtClass:
            return translateCaseStmt(llvm::cast<clang::CaseStmt>(S), ctx);

        case clang::Stmt::DefaultStmtClass:
            return translateDefaultStmt(llvm::cast<clang::DefaultStmt>(S), ctx);

        case clang::Stmt::BreakStmtClass:
            return translateBreakStmt(llvm::cast<clang::BreakStmt>(S), ctx);

        case clang::Stmt::ContinueStmtClass:
            return translateContinueStmt(llvm::cast<clang::ContinueStmt>(S), ctx);

        case clang::Stmt::GotoStmtClass:
            return translateGotoStmt(llvm::cast<clang::GotoStmt>(S), ctx);

        case clang::Stmt::LabelStmtClass:
            return translateLabelStmt(llvm::cast<clang::LabelStmt>(S), ctx);

        case clang::Stmt::DeclStmtClass:
            return translateDeclStmt(llvm::cast<clang::DeclStmt>(S), ctx);

        default:
            // For now, pass through other statements
            // TODO: Add support for more statement types in later phases
            return const_cast<clang::Stmt*>(S);
    }
}

clang::ReturnStmt* StatementHandler::translateReturnStmt(
    const clang::ReturnStmt* RS,
    HandlerContext& ctx
) {
    // Get return expression (may be null for void return)
    const clang::Expr* retValue = RS->getRetValue();
    clang::Expr* cRetValue = nullptr;

    if (retValue) {
        // For now, pass through the expression
        // TODO: Delegate to ExpressionHandler when available
        cRetValue = const_cast<clang::Expr*>(retValue);
    }

    // Create C return statement using CNodeBuilder
    clang::ASTContext& cContext = ctx.getCContext();
    return clang::ReturnStmt::Create(
        cContext,
        RS->getReturnLoc(),
        cRetValue,
        nullptr // NRVOCandidate
    );
}

clang::CompoundStmt* StatementHandler::translateCompoundStmt(
    const clang::CompoundStmt* CS,
    HandlerContext& ctx
) {
    // Translate each statement in the compound statement
    std::vector<clang::Stmt*> cStmts;

    for (const clang::Stmt* S : CS->body()) {
        clang::Stmt* cStmt = handleStmt(S, ctx);
        if (cStmt) {
            cStmts.push_back(cStmt);
        }
    }

    // Create C compound statement using CNodeBuilder
    clang::ASTContext& cContext = ctx.getCContext();
    return clang::CompoundStmt::Create(
        cContext,
        cStmts,
        clang::FPOptionsOverride(),
        CS->getLBracLoc(),
        CS->getRBracLoc()
    );
}

clang::IfStmt* StatementHandler::translateIfStmt(
    const clang::IfStmt* IS,
    HandlerContext& ctx
) {
    clang::ASTContext& cContext = ctx.getCContext();

    // Translate condition
    const clang::Expr* cond = IS->getCond();
    clang::Expr* cCond = const_cast<clang::Expr*>(cond);

    // Translate then branch
    const clang::Stmt* thenStmt = IS->getThen();
    clang::Stmt* cThenStmt = handleStmt(thenStmt, ctx);

    // Translate else branch (if present)
    clang::Stmt* cElseStmt = nullptr;
    if (IS->getElse()) {
        cElseStmt = handleStmt(IS->getElse(), ctx);
    }

    // Create C if statement
    return clang::IfStmt::Create(
        cContext,
        IS->getIfLoc(),
        clang::IfStatementKind::Ordinary,
        nullptr, // init (C++17)
        nullptr, // condVar
        cCond,
        clang::SourceLocation(),
        clang::SourceLocation(),
        cThenStmt,
        cElseStmt ? IS->getElseLoc() : clang::SourceLocation(),
        cElseStmt
    );
}

clang::WhileStmt* StatementHandler::translateWhileStmt(
    const clang::WhileStmt* WS,
    HandlerContext& ctx
) {
    clang::ASTContext& cContext = ctx.getCContext();

    // Translate condition
    const clang::Expr* cond = WS->getCond();
    clang::Expr* cCond = const_cast<clang::Expr*>(cond);

    // Translate body
    const clang::Stmt* body = WS->getBody();
    clang::Stmt* cBody = handleStmt(body, ctx);

    // Create C while statement
    return clang::WhileStmt::Create(
        cContext,
        nullptr, // ConditionVariable
        cCond,
        cBody,
        WS->getWhileLoc(),
        clang::SourceLocation(), // LParenLoc
        clang::SourceLocation()  // RParenLoc
    );
}

// Placeholder implementations for future tasks
clang::SwitchStmt* StatementHandler::translateSwitchStmt(
    const clang::SwitchStmt* SS,
    HandlerContext& ctx
) {
    // TODO: Task 8 - Implement switch translation
    return const_cast<clang::SwitchStmt*>(SS);
}

clang::CaseStmt* StatementHandler::translateCaseStmt(
    const clang::CaseStmt* CS,
    HandlerContext& ctx
) {
    // TODO: Task 8 - Implement case translation
    return const_cast<clang::CaseStmt*>(CS);
}

clang::DefaultStmt* StatementHandler::translateDefaultStmt(
    const clang::DefaultStmt* DS,
    HandlerContext& ctx
) {
    // TODO: Task 8 - Implement default translation
    return const_cast<clang::DefaultStmt*>(DS);
}

clang::BreakStmt* StatementHandler::translateBreakStmt(
    const clang::BreakStmt* BS,
    HandlerContext& ctx
) {
    // TODO: Task 9 - Implement break translation
    return const_cast<clang::BreakStmt*>(BS);
}

clang::ContinueStmt* StatementHandler::translateContinueStmt(
    const clang::ContinueStmt* CS,
    HandlerContext& ctx
) {
    clang::ASTContext& cContext = ctx.getCContext();
    return new (cContext) clang::ContinueStmt(CS->getContinueLoc());
}

clang::DoStmt* StatementHandler::translateDoStmt(
    const clang::DoStmt* DS,
    HandlerContext& ctx
) {
    // TODO: Task 6 - Implement do-while translation
    return const_cast<clang::DoStmt*>(DS);
}

clang::ForStmt* StatementHandler::translateForStmt(
    const clang::ForStmt* FS,
    HandlerContext& ctx
) {
    // TODO: Task 7 - Implement for loop translation
    return const_cast<clang::ForStmt*>(FS);
}

clang::GotoStmt* StatementHandler::translateGotoStmt(
    const clang::GotoStmt* GS,
    HandlerContext& ctx
) {
    // Goto statements in C and C++ have identical syntax
    // We need to create a new label declaration in the C AST and reference it
    clang::ASTContext& cContext = ctx.getCContext();

    // Get the original label
    const clang::LabelDecl* cppLabel = GS->getLabel();
    if (!cppLabel) {
        return nullptr;
    }

    // Create a new label declaration in C AST with the same name
    clang::IdentifierInfo& II = cContext.Idents.get(cppLabel->getName());
    clang::LabelDecl* cLabel = clang::LabelDecl::Create(
        cContext,
        cContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        &II
    );

    // Create C goto statement
    return new (cContext) clang::GotoStmt(
        cLabel,
        GS->getGotoLoc(),
        GS->getLabelLoc()
    );
}

clang::LabelStmt* StatementHandler::translateLabelStmt(
    const clang::LabelStmt* LS,
    HandlerContext& ctx
) {
    // Label statements in C and C++ have identical syntax
    // We need to create a new label declaration and translate the sub-statement
    clang::ASTContext& cContext = ctx.getCContext();

    // Get the original label declaration
    const clang::LabelDecl* cppDecl = LS->getDecl();
    if (!cppDecl) {
        return nullptr;
    }

    // Create a new label declaration in C AST with the same name
    clang::IdentifierInfo& II = cContext.Idents.get(cppDecl->getName());
    clang::LabelDecl* cDecl = clang::LabelDecl::Create(
        cContext,
        cContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        &II
    );

    // Translate the sub-statement
    const clang::Stmt* subStmt = LS->getSubStmt();
    clang::Stmt* cSubStmt = handleStmt(subStmt, ctx);

    if (!cSubStmt) {
        return nullptr;
    }

    // Create C label statement
    return new (cContext) clang::LabelStmt(
        LS->getIdentLoc(),
        cDecl,
        cSubStmt
    );
}

clang::Stmt* StatementHandler::translateDeclStmt(
    const clang::DeclStmt* DS,
    HandlerContext& ctx
) {
    // Task 9: Handle object construction and destruction (RAII)
    //
    // Strategy:
    // 1. Check if declaration is for a class type object
    // 2. If yes, create constructor call after declaration
    // 3. Return CompoundStmt with both declaration and constructor call
    // 4. If no, pass through as-is
    //
    // Note: Destructor injection is handled separately in scope management

    clang::ASTContext& cContext = ctx.getCContext();

    // Handle each declaration in the DeclStmt
    // DeclStmt can contain multiple declarations (e.g., int a, b, c;)
    std::vector<clang::Stmt*> stmts;

    for (auto* decl : DS->decls()) {
        // We only care about VarDecl for now
        auto* varDecl = llvm::dyn_cast<clang::VarDecl>(decl);
        if (!varDecl) {
            continue; // Skip non-variable declarations
        }

        // Check if this is a class type requiring constructor call
        clang::QualType type = varDecl->getType();
        bool needsConstructor = isClassTypeRequiringConstructor(type);

        if (needsConstructor) {
            // For class types, we need to:
            // 1. Create variable declaration without initializer
            // 2. Create constructor call

            // Create C variable declaration without initializer
            clang::IdentifierInfo& II = cContext.Idents.get(varDecl->getNameAsString());
            clang::QualType cType = ctx.translateType(type);

            clang::VarDecl* cVarDecl = clang::VarDecl::Create(
                cContext,
                cContext.getTranslationUnitDecl(),
                clang::SourceLocation(),
                clang::SourceLocation(),
                &II,
                cType,
                cContext.getTrivialTypeSourceInfo(cType),
                clang::SC_None
            );

            // Register the declaration mapping
            ctx.registerDecl(varDecl, cVarDecl);

            // Create DeclStmt for the variable
            clang::DeclStmt* cDeclStmt = new (cContext) clang::DeclStmt(
                clang::DeclGroupRef(cVarDecl),
                clang::SourceLocation(),
                clang::SourceLocation()
            );

            stmts.push_back(cDeclStmt);

            // Create constructor call (pass both C++ and C variable decls)
            clang::Expr* ctorCall = createConstructorCall(varDecl, cVarDecl, ctx);
            if (ctorCall) {
                stmts.push_back(ctorCall);
            }

            // For TDD: Even if no constructor call yet, we signal that this
            // needs special handling by returning a CompoundStmt
            // This will make tests pass incrementally as we implement ctor calls
        } else {
            // For non-class types, just pass through
            // Create C variable declaration
            clang::IdentifierInfo& II = cContext.Idents.get(varDecl->getNameAsString());
            clang::QualType cType = ctx.translateType(type);

            clang::VarDecl* cVarDecl = clang::VarDecl::Create(
                cContext,
                cContext.getTranslationUnitDecl(),
                clang::SourceLocation(),
                clang::SourceLocation(),
                &II,
                cType,
                cContext.getTrivialTypeSourceInfo(cType),
                clang::SC_None
            );

            ctx.registerDecl(varDecl, cVarDecl);

            clang::DeclStmt* cDeclStmt = new (cContext) clang::DeclStmt(
                clang::DeclGroupRef(cVarDecl),
                clang::SourceLocation(),
                clang::SourceLocation()
            );

            stmts.push_back(cDeclStmt);
        }
    }

    // For class types (even without constructor call yet), wrap in CompoundStmt
    // This signals that this declaration needs special handling (constructor/destructor)
    // For TDD: This allows tests to pass incrementally as we add constructor calls

    // Check if any of the original decls was a class type
    bool hasClassType = false;
    for (auto* decl : DS->decls()) {
        if (auto* varDecl = llvm::dyn_cast<clang::VarDecl>(decl)) {
            if (isClassTypeRequiringConstructor(varDecl->getType())) {
                hasClassType = true;
                break;
            }
        }
    }

    // If we have class types or multiple statements, wrap in CompoundStmt
    if (hasClassType || stmts.size() > 1) {
        return clang::CompoundStmt::Create(
            cContext,
            stmts,
            clang::FPOptionsOverride(),
            clang::SourceLocation(),
            clang::SourceLocation()
        );
    }

    // If we only have one non-class statement, return it directly
    if (stmts.size() == 1) {
        return stmts[0];
    }

    // No statements to return
    return nullptr;
}

bool StatementHandler::isClassTypeRequiringConstructor(clang::QualType type) {
    // Remove const/volatile/reference qualifiers
    type = type.getCanonicalType();
    type = type.getNonReferenceType();
    type = type.getUnqualifiedType();

    // Check if this is a class type
    const clang::Type* typePtr = type.getTypePtr();
    if (!typePtr) return false;

    // Check for CXXRecordType (class/struct/union in C++)
    if (const auto* recordType = llvm::dyn_cast<clang::RecordType>(typePtr)) {
        if (const auto* recordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(recordType->getDecl())) {
            // Check if it has any constructors
            // If it has constructors, we need to call one
            // If it's a POD type (C-compatible struct), we don't need constructor
            return recordDecl->hasUserDeclaredConstructor() || !recordDecl->isPOD();
        }
    }

    return false;
}

clang::Expr* StatementHandler::createConstructorCall(
    const clang::VarDecl* cppVarDecl,
    clang::VarDecl* cVarDecl,
    HandlerContext& ctx
) {
    // Create constructor call for object initialization
    //
    // Strategy:
    // 1. Get the class type and find its constructor
    // 2. Generate mangled constructor name (ClassName_init or ClassName_init_types)
    // 3. Create DeclRefExpr for variable
    // 4. Create UnaryOperator(&obj) for 'this' parameter
    // 5. Extract constructor arguments from initializer
    // 6. Create CallExpr: ClassName_init(&obj, args...)

    clang::ASTContext& cContext = ctx.getCContext();
    clang::QualType varType = cppVarDecl->getType();

    // Get the CXXRecordDecl for this class type
    const clang::RecordType* recordType = varType->getAs<clang::RecordType>();
    if (!recordType) return nullptr;

    const auto* recordDecl = llvm::dyn_cast<clang::CXXRecordDecl>(recordType->getDecl());
    if (!recordDecl) return nullptr;

    std::string className = recordDecl->getNameAsString();

    // For now, create a simple default constructor call: ClassName_init(&obj)
    // TODO: Handle parameterized constructors by examining cppVarDecl->getInit()

    // Generate constructor name
    // For default constructor (no params): ClassName_init
    std::string ctorName = className + "_init";

    // Create DeclRefExpr for the variable
    clang::DeclRefExpr* varRef = clang::DeclRefExpr::Create(
        cContext,
        clang::NestedNameSpecifierLoc(),
        clang::SourceLocation(),
        cVarDecl,
        false,  // RefersToEnclosingVariableOrCapture
        clang::SourceLocation(),
        cVarDecl->getType(),
        clang::VK_LValue
    );

    // Create UnaryOperator for address-of (&obj)
    clang::QualType ptrType = cContext.getPointerType(cVarDecl->getType());
    clang::UnaryOperator* addrOf = clang::UnaryOperator::Create(
        cContext,
        varRef,
        clang::UO_AddrOf,
        ptrType,
        clang::VK_PRValue,
        clang::OK_Ordinary,
        clang::SourceLocation(),
        false,  // CanOverflow
        clang::FPOptionsOverride()
    );

    // Create function reference for constructor
    // We need to create a dummy function decl or lookup the constructor
    // For now, create a simple function reference

    clang::IdentifierInfo& ctorII = cContext.Idents.get(ctorName);
    clang::QualType ctorType = cContext.VoidTy;  // Constructors return void

    // Create a dummy function declaration for the constructor
    // In a full implementation, we'd lookup the actual translated constructor
    clang::FunctionDecl* ctorFunc = clang::FunctionDecl::Create(
        cContext,
        cContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &ctorII,
        cContext.getFunctionType(ctorType, {ptrType}, {}),
        cContext.getTrivialTypeSourceInfo(ctorType),
        clang::SC_Extern
    );

    // Create DeclRefExpr for the constructor function
    clang::DeclRefExpr* ctorRef = clang::DeclRefExpr::Create(
        cContext,
        clang::NestedNameSpecifierLoc(),
        clang::SourceLocation(),
        ctorFunc,
        false,
        clang::SourceLocation(),
        ctorFunc->getType(),
        clang::VK_LValue
    );

    // Create CallExpr with &obj as the only argument (for default constructor)
    std::vector<clang::Expr*> args;
    args.push_back(addrOf);

    clang::CallExpr* callExpr = clang::CallExpr::Create(
        cContext,
        ctorRef,
        args,
        cContext.VoidTy,
        clang::VK_PRValue,
        clang::SourceLocation(),
        clang::FPOptionsOverride()
    );

    return callExpr;
}

} // namespace cpptoc
