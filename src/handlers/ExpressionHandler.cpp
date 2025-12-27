/**
 * @file ExpressionHandler.cpp
 * @brief Implementation of ExpressionHandler
 *
 * Implements recursive expression translation from C++ AST to C AST.
 * Preserves operator precedence and expression structure.
 */

#include "handlers/ExpressionHandler.h"
#include "handlers/HandlerContext.h"
#include "CNodeBuilder.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "llvm/Support/Casting.h"

namespace cpptoc {

// ============================================================================
// Public Interface
// ============================================================================

bool ExpressionHandler::canHandle(const clang::Expr* E) const {
    if (!E) return false;

    // Handle all basic expression types
    return llvm::isa<clang::IntegerLiteral>(E) ||
           llvm::isa<clang::FloatingLiteral>(E) ||
           llvm::isa<clang::StringLiteral>(E) ||
           llvm::isa<clang::CharacterLiteral>(E) ||
           llvm::isa<clang::BinaryOperator>(E) ||
           llvm::isa<clang::UnaryOperator>(E) ||
           llvm::isa<clang::DeclRefExpr>(E) ||
           llvm::isa<clang::ParenExpr>(E) ||
           llvm::isa<clang::ImplicitCastExpr>(E) ||
           llvm::isa<clang::CStyleCastExpr>(E) ||
           llvm::isa<clang::ArraySubscriptExpr>(E) ||
           llvm::isa<clang::InitListExpr>(E) ||
           llvm::isa<clang::CXXNullPtrLiteralExpr>(E) ||
           llvm::isa<clang::MemberExpr>(E) ||
           llvm::isa<clang::CXXThisExpr>(E) ||
           llvm::isa<clang::CXXMemberCallExpr>(E);
}

clang::Expr* ExpressionHandler::handleExpr(const clang::Expr* E, HandlerContext& ctx) {
    if (!E) return nullptr;

    // Dispatch based on expression type
    if (auto* IL = llvm::dyn_cast<clang::IntegerLiteral>(E)) {
        return translateIntegerLiteral(IL, ctx);
    }
    if (auto* FL = llvm::dyn_cast<clang::FloatingLiteral>(E)) {
        return translateFloatingLiteral(FL, ctx);
    }
    if (auto* SL = llvm::dyn_cast<clang::StringLiteral>(E)) {
        return translateStringLiteral(SL, ctx);
    }
    if (auto* CL = llvm::dyn_cast<clang::CharacterLiteral>(E)) {
        return translateCharacterLiteral(CL, ctx);
    }
    if (auto* BO = llvm::dyn_cast<clang::BinaryOperator>(E)) {
        return translateBinaryOperator(BO, ctx);
    }
    if (auto* UO = llvm::dyn_cast<clang::UnaryOperator>(E)) {
        return translateUnaryOperator(UO, ctx);
    }
    if (auto* DRE = llvm::dyn_cast<clang::DeclRefExpr>(E)) {
        return translateDeclRefExpr(DRE, ctx);
    }
    if (auto* PE = llvm::dyn_cast<clang::ParenExpr>(E)) {
        return translateParenExpr(PE, ctx);
    }
    if (auto* ICE = llvm::dyn_cast<clang::ImplicitCastExpr>(E)) {
        return translateImplicitCastExpr(ICE, ctx);
    }
    if (auto* CCE = llvm::dyn_cast<clang::CStyleCastExpr>(E)) {
        return translateCStyleCastExpr(CCE, ctx);
    }
    if (auto* ASE = llvm::dyn_cast<clang::ArraySubscriptExpr>(E)) {
        return translateArraySubscriptExpr(ASE, ctx);
    }
    if (auto* ILE = llvm::dyn_cast<clang::InitListExpr>(E)) {
        return translateInitListExpr(ILE, ctx);
    }
    if (auto* NPE = llvm::dyn_cast<clang::CXXNullPtrLiteralExpr>(E)) {
        return translateNullPtrLiteral(NPE, ctx);
    }
    if (auto* ME = llvm::dyn_cast<clang::MemberExpr>(E)) {
        return translateMemberExpr(ME, ctx);
    }
    if (auto* TE = llvm::dyn_cast<clang::CXXThisExpr>(E)) {
        return translateCXXThisExpr(TE, ctx);
    }
    if (auto* MCE = llvm::dyn_cast<clang::CXXMemberCallExpr>(E)) {
        return translateCXXMemberCallExpr(MCE, ctx);
    }

    // Unsupported expression type
    return nullptr;
}

// ============================================================================
// Literal Translations
// ============================================================================

clang::Expr* ExpressionHandler::translateIntegerLiteral(
    const clang::IntegerLiteral* IL,
    HandlerContext& ctx
) {
    // Direct translation - integer literals are the same in C and C++
    clang::ASTContext& cCtx = ctx.getCContext();

    return clang::IntegerLiteral::Create(
        cCtx,
        IL->getValue(),
        IL->getType(),
        IL->getLocation()
    );
}

clang::Expr* ExpressionHandler::translateFloatingLiteral(
    const clang::FloatingLiteral* FL,
    HandlerContext& ctx
) {
    // Direct translation - floating literals are the same in C and C++
    clang::ASTContext& cCtx = ctx.getCContext();

    return clang::FloatingLiteral::Create(
        cCtx,
        FL->getValue(),
        FL->isExact(),
        FL->getType(),
        FL->getLocation()
    );
}

clang::Expr* ExpressionHandler::translateStringLiteral(
    const clang::StringLiteral* SL,
    HandlerContext& ctx
) {
    // Direct translation - string literals are the same in C and C++
    clang::ASTContext& cCtx = ctx.getCContext();

    return clang::StringLiteral::Create(
        cCtx,
        SL->getString(),
        SL->getKind(),
        SL->isPascal(),
        SL->getType(),
        SL->getBeginLoc()
    );
}

clang::Expr* ExpressionHandler::translateCharacterLiteral(
    const clang::CharacterLiteral* CL,
    HandlerContext& ctx
) {
    // Direct translation - character literals are the same in C and C++
    clang::ASTContext& cCtx = ctx.getCContext();

    return new (cCtx) clang::CharacterLiteral(
        CL->getValue(),
        CL->getKind(),
        CL->getType(),
        CL->getLocation()
    );
}

// ============================================================================
// Operator Translations
// ============================================================================

clang::Expr* ExpressionHandler::translateBinaryOperator(
    const clang::BinaryOperator* BO,
    HandlerContext& ctx
) {
    // Recursively translate LHS and RHS
    clang::Expr* LHS = handleExpr(BO->getLHS(), ctx);
    clang::Expr* RHS = handleExpr(BO->getRHS(), ctx);

    if (!LHS || !RHS) {
        return nullptr;
    }

    clang::ASTContext& cCtx = ctx.getCContext();

    // Create C binary operator with same opcode
    return clang::BinaryOperator::Create(
        cCtx,
        LHS,
        RHS,
        BO->getOpcode(),
        BO->getType(),
        BO->getValueKind(),
        BO->getObjectKind(),
        BO->getOperatorLoc(),
        BO->getFPFeatures()
    );
}

clang::Expr* ExpressionHandler::translateUnaryOperator(
    const clang::UnaryOperator* UO,
    HandlerContext& ctx
) {
    // Recursively translate subexpression
    clang::Expr* SubExpr = handleExpr(UO->getSubExpr(), ctx);

    if (!SubExpr) {
        return nullptr;
    }

    clang::ASTContext& cCtx = ctx.getCContext();

    // Create C unary operator with same opcode
    return clang::UnaryOperator::Create(
        cCtx,
        SubExpr,
        UO->getOpcode(),
        UO->getType(),
        UO->getValueKind(),
        UO->getObjectKind(),
        UO->getOperatorLoc(),
        UO->canOverflow(),
        clang::FPOptionsOverride()
    );
}

// ============================================================================
// Reference Translations
// ============================================================================

clang::Expr* ExpressionHandler::translateDeclRefExpr(
    const clang::DeclRefExpr* DRE,
    HandlerContext& ctx
) {
    // Get the referenced declaration
    const clang::ValueDecl* cppDecl = DRE->getDecl();

    // Look up the C equivalent declaration
    clang::ASTContext& cCtx = ctx.getCContext();

    // Try to find the translated declaration in the symbol table
    clang::Decl* cDecl = ctx.lookupDecl(cppDecl);

    // For testing purposes, if the declaration isn't in the symbol table yet,
    // we'll create a placeholder reference using the C++ declaration directly
    // This allows expression tests to work independently of variable translation
    const clang::ValueDecl* valueDecl = cppDecl;
    if (cDecl) {
        auto* cValueDecl = llvm::dyn_cast<clang::ValueDecl>(cDecl);
        if (cValueDecl) {
            valueDecl = cValueDecl;
        }
    }

    // Get non-const pointers for API requirements
    clang::NamedDecl* foundDecl = const_cast<clang::NamedDecl*>(DRE->getFoundDecl());
    clang::ValueDecl* mutableValueDecl = const_cast<clang::ValueDecl*>(valueDecl);

    // Create the DeclRefExpr
    clang::Expr* result = clang::DeclRefExpr::Create(
        cCtx,
        DRE->getQualifierLoc(),
        DRE->getTemplateKeywordLoc(),
        mutableValueDecl,
        DRE->refersToEnclosingVariableOrCapture(),
        DRE->getNameInfo(),
        valueDecl->getType(),
        DRE->getValueKind(),
        foundDecl
    );

    // Task 7: Reference Usage Translation
    // If the C++ declaration is a reference type, we need to dereference it in C
    // C++ references are automatically dereferenced, but in C we use pointers
    // So: C++ "ref" becomes C "*ref"
    if (cppDecl->getType()->isReferenceType()) {
        // Get the pointee type (what the reference refers to)
        clang::QualType pointeeType = cppDecl->getType()->getPointeeType();

        // Wrap the DeclRefExpr in a dereference operator
        result = clang::UnaryOperator::Create(
            cCtx,
            result,                         // Subexpression (the pointer)
            clang::UO_Deref,                // Dereference operator
            pointeeType,                    // Result type (pointee type)
            clang::VK_LValue,               // Value kind
            clang::OK_Ordinary,             // Object kind
            DRE->getLocation(),             // Source location
            false,                          // Can overflow (not relevant for deref)
            clang::FPOptionsOverride()      // FP options
        );
    }

    return result;
}

// ============================================================================
// Structural Translations
// ============================================================================

clang::Expr* ExpressionHandler::translateParenExpr(
    const clang::ParenExpr* PE,
    HandlerContext& ctx
) {
    // Recursively translate the subexpression
    clang::Expr* SubExpr = handleExpr(PE->getSubExpr(), ctx);

    if (!SubExpr) {
        return nullptr;
    }

    clang::ASTContext& cCtx = ctx.getCContext();

    // Create C parenthesized expression
    return new (cCtx) clang::ParenExpr(
        PE->getLParen(),
        PE->getRParen(),
        SubExpr
    );
}

clang::Expr* ExpressionHandler::translateImplicitCastExpr(
    const clang::ImplicitCastExpr* ICE,
    HandlerContext& ctx
) {
    // Recursively translate the subexpression
    clang::Expr* SubExpr = handleExpr(ICE->getSubExpr(), ctx);

    if (!SubExpr) {
        return nullptr;
    }

    // For most implicit casts, we can just return the subexpression
    // C compiler will handle implicit conversions
    // For more complex cases, we might need to preserve the cast
    switch (ICE->getCastKind()) {
        case clang::CK_LValueToRValue:
        case clang::CK_NoOp:
        case clang::CK_ArrayToPointerDecay:
        case clang::CK_FunctionToPointerDecay:
            // These casts can be omitted in C
            return SubExpr;

        default:
            // For other casts, preserve the implicit cast
            // (though in practice, C compiler will re-insert them)
            return SubExpr;
    }
}

// ============================================================================
// Array Access Translations
// ============================================================================

clang::Expr* ExpressionHandler::translateArraySubscriptExpr(
    const clang::ArraySubscriptExpr* ASE,
    HandlerContext& ctx
) {
    // Recursively translate base and index expressions
    clang::Expr* Base = handleExpr(ASE->getBase(), ctx);
    clang::Expr* Idx = handleExpr(ASE->getIdx(), ctx);

    if (!Base || !Idx) {
        return nullptr;
    }

    clang::ASTContext& cCtx = ctx.getCContext();

    // Create C array subscript expression
    // Array subscript syntax is identical in C and C++
    // ArraySubscriptExpr expects (lhs, rhs, type, VK, OK, rbracket)
    // where lhs is the base and rhs is the index
    return new (cCtx) clang::ArraySubscriptExpr(
        Base,
        Idx,
        ASE->getType(),
        ASE->getValueKind(),
        ASE->getObjectKind(),
        ASE->getRBracketLoc()
    );
}

// ============================================================================
// Initializer List Translation
// ============================================================================

clang::Expr* ExpressionHandler::translateInitListExpr(
    const clang::InitListExpr* ILE,
    HandlerContext& ctx
) {
    // Initializer lists are identical in C and C++
    // Recursively translate all initialization expressions
    clang::ASTContext& cCtx = ctx.getCContext();

    // Translate each initializer expression
    llvm::SmallVector<clang::Expr*, 8> translatedInits;
    for (unsigned i = 0; i < ILE->getNumInits(); ++i) {
        clang::Expr* init = handleExpr(ILE->getInit(i), ctx);
        if (!init) {
            return nullptr;  // Translation failed
        }
        translatedInits.push_back(init);
    }

    // Create C InitListExpr
    // Note: InitListExpr constructor takes an array of initializers
    clang::InitListExpr* result = new (cCtx) clang::InitListExpr(
        cCtx,
        ILE->getLBraceLoc(),
        translatedInits,
        ILE->getRBraceLoc()
    );

    // Set the type of the initializer list
    result->setType(ILE->getType());

    return result;
}

// ============================================================================
// Cast Expression Translations
// ============================================================================

clang::Expr* ExpressionHandler::translateCStyleCastExpr(
    const clang::CStyleCastExpr* CCE,
    HandlerContext& ctx
) {
    // C-style casts are identical in C and C++
    // Recursively translate the subexpression
    clang::Expr* SubExpr = handleExpr(CCE->getSubExpr(), ctx);

    if (!SubExpr) {
        return nullptr;
    }

    clang::ASTContext& cCtx = ctx.getCContext();

    // Create C CStyleCastExpr
    // We need to create the cast using CStyleCastExpr::Create
    return clang::CStyleCastExpr::Create(
        cCtx,
        CCE->getType(),                    // Target type
        CCE->getValueKind(),               // Value kind
        CCE->getCastKind(),                // Cast kind
        SubExpr,                           // Subexpression
        nullptr,                           // Base path (for pointer-to-member casts)
        CCE->getFPFeatures(),              // Floating point features
        CCE->getTypeInfoAsWritten(),       // Type info as written
        CCE->getLParenLoc(),               // Left paren location
        CCE->getRParenLoc()                // Right paren location
    );
}

// ============================================================================
// Null Pointer Translation (Phase 42, Task 6)
// ============================================================================

clang::Expr* ExpressionHandler::translateNullPtrLiteral(
    const clang::CXXNullPtrLiteralExpr* NPE,
    HandlerContext& ctx
) {
    // C++11 nullptr → C NULL (represented as (void*)0)
    // We create a C-style cast of 0 to void*
    clang::ASTContext& cCtx = ctx.getCContext();

    // Create integer literal with value 0
    llvm::APInt zero(32, 0);
    clang::IntegerLiteral* zeroLiteral = clang::IntegerLiteral::Create(
        cCtx,
        zero,
        cCtx.IntTy,
        NPE->getLocation()
    );

    // Cast 0 to void* to create NULL equivalent
    // This matches C's NULL definition: ((void*)0)
    clang::QualType voidPtrType = cCtx.getPointerType(cCtx.VoidTy);

    return clang::CStyleCastExpr::Create(
        cCtx,
        voidPtrType,                    // Target type: void*
        clang::VK_PRValue,              // Value kind
        clang::CK_NullToPointer,        // Cast kind
        zeroLiteral,                    // Subexpression: 0
        nullptr,                        // Base path
        clang::FPOptionsOverride(),     // FP options
        cCtx.getTrivialTypeSourceInfo(voidPtrType),  // Type source info
        NPE->getLocation(),             // L paren
        NPE->getLocation()              // R paren
    );
}

// ============================================================================
// Member Expression Translation (Phase 43, Tasks 3 & 4)
// ============================================================================

clang::Expr* ExpressionHandler::translateMemberExpr(
    const clang::MemberExpr* ME,
    HandlerContext& ctx
) {
    // Member expressions are identical in C and C++
    // Both dot (.) and arrow (->) operators work the same way
    // Syntax: base.member or ptr->member
    // We preserve the operator type (isArrow()) and recursively translate the base

    clang::ASTContext& cCtx = ctx.getCContext();

    // Recursively translate the base expression (the object or pointer)
    clang::Expr* Base = handleExpr(ME->getBase(), ctx);
    if (!Base) {
        return nullptr;
    }

    // Get the member declaration
    // In C++ AST, this is already a FieldDecl or VarDecl
    // For C-style structs, we use it directly
    // Note: For future class support, we'll need to map member decls
    clang::ValueDecl* MemberDecl = ME->getMemberDecl();

    // Handle template arguments if present
    // For C-style structs (Phase 43), template arguments should not be present
    // For future template support, we'll need to translate template args
    const clang::TemplateArgumentListInfo* TemplateArgs = nullptr;
    if (ME->hasExplicitTemplateArgs()) {
        // For now, we don't support template arguments in member access
        // This will be needed for template member functions in later phases
        // For C-style structs, this should never be hit
        return nullptr;
    }

    // Create C MemberExpr with same structure
    // MemberExpr::Create parameters:
    // - ASTContext
    // - Base expression
    // - IsArrow (true for ->, false for .)
    // - OperatorLoc
    // - NestedNameSpecifierLoc
    // - TemplateKeywordLoc
    // - MemberDecl
    // - FoundDecl (for overloaded members)
    // - MemberNameInfo
    // - TemplateArgs (nullptr for C-style structs)
    // - Type
    // - ValueKind
    // - ObjectKind
    // - NonOdrUseReason

    return clang::MemberExpr::Create(
        cCtx,
        Base,                           // Base expression
        ME->isArrow(),                  // Is arrow operator (-> vs .)
        ME->getOperatorLoc(),           // Operator location
        ME->getQualifierLoc(),          // Nested name specifier
        ME->getTemplateKeywordLoc(),    // Template keyword location
        MemberDecl,                     // Member declaration
        ME->getFoundDecl(),             // Found declaration
        ME->getMemberNameInfo(),        // Member name info
        TemplateArgs,                   // Template arguments (nullptr for C structs)
        ME->getType(),                  // Result type
        ME->getValueKind(),             // Value kind (lvalue/rvalue)
        ME->getObjectKind(),            // Object kind
        ME->isNonOdrUse()               // Non-ODR use
    );
}

// ============================================================================
// This Expression Translation (Phase 44, Task 6)
// ============================================================================

clang::Expr* ExpressionHandler::translateCXXThisExpr(
    const clang::CXXThisExpr* TE,
    HandlerContext& ctx
) {
    // C++ 'this' keyword → C DeclRefExpr referring to 'this' parameter
    //
    // In C++, 'this' is an implicit pointer to the current object.
    // In C, we make it explicit as the first parameter of methods.
    //
    // Translation strategy:
    // 1. Get current function from context (set by MethodHandler/ConstructorHandler)
    // 2. Get first parameter (which should be 'this' for non-static methods)
    // 3. Create DeclRefExpr referring to that parameter
    //
    // Example:
    // C++: void Counter::increment() { this->count++; }
    // C:   void Counter_increment(struct Counter* this) { this->count++; }

    clang::ASTContext& cCtx = ctx.getCContext();

    // Get current function from context
    clang::FunctionDecl* currentFunc = ctx.getCurrentFunction();
    if (!currentFunc) {
        // No current function - this shouldn't happen in well-formed code
        // 'this' can only appear inside method bodies
        return nullptr;
    }

    // Get first parameter (should be 'this')
    // For methods translated to C functions, 'this' is always the first parameter
    if (currentFunc->param_empty()) {
        // No parameters - this must be a static method
        // Static methods don't have 'this' parameter
        return nullptr;
    }

    clang::ParmVarDecl* thisParam = currentFunc->getParamDecl(0);

    // Verify it's actually named 'this'
    // This is a sanity check - if we're translating correctly,
    // the first parameter should always be named 'this' for non-static methods
    if (thisParam->getName() != "this") {
        // First parameter is not 'this' - might be a regular function or static method
        return nullptr;
    }

    // Create DeclRefExpr referring to 'this' parameter
    // DeclRefExpr::Create parameters:
    // - ASTContext
    // - NestedNameSpecifierLoc (none for simple parameter reference)
    // - TemplateKeywordLoc (invalid for parameter reference)
    // - ValueDecl (the 'this' parameter)
    // - RefersToEnclosingVariableOrCapture (false for parameters)
    // - NameInfo (location and name)
    // - QualType (type of the parameter)
    // - ValueKind (LValue for parameter references)
    // - NonOdrUseReason (for ODR-use tracking)

    clang::DeclarationNameInfo nameInfo(
        thisParam->getDeclName(),
        TE->getLocation()
    );

    return clang::DeclRefExpr::Create(
        cCtx,
        clang::NestedNameSpecifierLoc(),      // No nested name specifier
        clang::SourceLocation(),              // No template keyword
        thisParam,                            // The 'this' parameter
        false,                                // Not refersToEnclosingVariableOrCapture
        nameInfo,                             // Name and location
        thisParam->getType(),                 // Type: struct ClassName*
        clang::VK_LValue                      // Value kind: lvalue
    );
}

// ============================================================================
// Method Call Translation (Phase 44, Task 8)
// ============================================================================

clang::Expr* ExpressionHandler::translateCXXMemberCallExpr(
    const clang::CXXMemberCallExpr* MCE,
    HandlerContext& ctx
) {
    // C++ method call → C function call or vtable dispatch
    //
    // Translation strategy for VIRTUAL calls (Phase 45 Task 7):
    // 1. Detect virtual call using isVirtualCall()
    // 2. Generate COM-style vtable dispatch: obj->lpVtbl->methodName(obj, args...)
    // 3. Handle value objects: obj.method() → (&obj)->lpVtbl->methodName(&obj, ...)
    // 4. Handle pointer objects: ptr->method() → ptr->lpVtbl->methodName(ptr, ...)
    //
    // Translation strategy for NON-VIRTUAL calls:
    // 1. Get the C++ method being called
    // 2. Look up the corresponding C function in context
    // 3. Get the implicit object argument (the object being called on)
    // 4. Translate object expression and determine if we need &
    // 5. Create CallExpr with C function
    // 6. Insert object as first argument
    // 7. Translate and add remaining arguments
    //
    // Examples:
    // Virtual calls:
    // C++: ptr->draw()              → C: ptr->lpVtbl->draw(ptr)
    // C++: obj.draw()               → C: (&obj)->lpVtbl->draw(&obj)
    //
    // Non-virtual calls:
    // C++: obj.method(args...)      → C: ClassName_method(&obj, args...)
    // C++: ptr->method(args...)     → C: ClassName_method(ptr, args...)
    // C++: this->method(args...)    → C: ClassName_method(this, args...)

    clang::ASTContext& cCtx = ctx.getCContext();

    // 1. Get the method being called
    const clang::CXXMethodDecl* method = MCE->getMethodDecl();
    if (!method) {
        // No method declaration - shouldn't happen in well-formed code
        return nullptr;
    }

    // Phase 45 Task 7: Check if this is a virtual call
    bool isVirtual = isVirtualCall(MCE);

    // For virtual calls, we need to use vtable dispatch
    if (isVirtual) {
        return translateVirtualCall(MCE, method, ctx);
    }

    // For non-virtual calls, use direct function call (existing logic below)

    // 2. Look up the corresponding C function
    clang::FunctionDecl* cFunc = ctx.lookupMethod(method);
    if (!cFunc) {
        // Method not registered - can't translate
        // This happens when the method hasn't been translated yet
        return nullptr;
    }

    // 3. Get the implicit object argument (the object being called on)
    const clang::Expr* objectExpr = MCE->getImplicitObjectArgument();
    if (!objectExpr) {
        // No object - might be a static method call
        // For static methods, we don't add 'this' parameter
        // Just translate arguments and create call
        llvm::SmallVector<clang::Expr*, 8> translatedArgs;
        for (unsigned i = 0; i < MCE->getNumArgs(); ++i) {
            clang::Expr* arg = handleExpr(MCE->getArg(i), ctx);
            if (!arg) {
                return nullptr;  // Argument translation failed
            }
            translatedArgs.push_back(arg);
        }

        // Create function reference
        clang::DeclRefExpr* funcRef = clang::DeclRefExpr::Create(
            cCtx,
            clang::NestedNameSpecifierLoc(),
            clang::SourceLocation(),
            cFunc,
            false,
            clang::DeclarationNameInfo(cFunc->getDeclName(), MCE->getExprLoc()),
            cFunc->getType(),
            clang::VK_LValue
        );

        // Create call expression
        return clang::CallExpr::Create(
            cCtx,
            funcRef,
            translatedArgs,
            MCE->getType(),
            MCE->getValueKind(),
            MCE->getExprLoc(),
            clang::FPOptionsOverride()
        );
    }

    // 4. Translate object expression and determine if we need &
    clang::Expr* translatedObject = handleExpr(objectExpr, ctx);
    if (!translatedObject) {
        return nullptr;  // Object translation failed
    }

    // Determine if we need to take address of object
    // Rules:
    // - If object is already a pointer (ptr->method), use it directly
    // - If object is a value (obj.method), take its address (&obj)
    // - Special case: 'this' is already a pointer, use directly

    bool needsAddressOf = false;
    clang::QualType objectType = objectExpr->getType();

    // Check if the object expression is a pointer or reference
    if (objectType->isPointerType()) {
        // ptr->method() - object is already a pointer
        needsAddressOf = false;
    } else if (objectType->isReferenceType()) {
        // ref.method() - references become pointers in C, no & needed
        needsAddressOf = false;
    } else {
        // obj.method() - object is a value, need to take its address
        needsAddressOf = true;
    }

    // Wrap object in UnaryOperator(&) if needed
    clang::Expr* objectArg = translatedObject;
    if (needsAddressOf) {
        // Get the pointer type (what we get when we take address)
        clang::QualType ptrType = cCtx.getPointerType(translatedObject->getType());

        objectArg = clang::UnaryOperator::Create(
            cCtx,
            translatedObject,               // Subexpression (the object)
            clang::UO_AddrOf,               // Address-of operator
            ptrType,                        // Result type (pointer)
            clang::VK_PRValue,              // Value kind (prvalue for &)
            clang::OK_Ordinary,             // Object kind
            MCE->getExprLoc(),              // Source location
            false,                          // Can overflow (not relevant)
            clang::FPOptionsOverride()      // FP options
        );
    }

    // 5. Translate remaining arguments
    llvm::SmallVector<clang::Expr*, 8> allArgs;

    // First argument: the object (this)
    allArgs.push_back(objectArg);

    // Remaining arguments: translate each one
    for (unsigned i = 0; i < MCE->getNumArgs(); ++i) {
        clang::Expr* arg = handleExpr(MCE->getArg(i), ctx);
        if (!arg) {
            return nullptr;  // Argument translation failed
        }
        allArgs.push_back(arg);
    }

    // 6. Create function reference (callee expression)
    clang::DeclRefExpr* funcRef = clang::DeclRefExpr::Create(
        cCtx,
        clang::NestedNameSpecifierLoc(),      // No nested name specifier
        clang::SourceLocation(),              // No template keyword
        cFunc,                                // The C function
        false,                                // Not refersToEnclosingVariableOrCapture
        clang::DeclarationNameInfo(
            cFunc->getDeclName(),
            MCE->getExprLoc()
        ),                                    // Name and location
        cFunc->getType(),                     // Type: function type
        clang::VK_LValue                      // Value kind: lvalue for function
    );

    // 7. Create CallExpr
    // CallExpr::Create parameters:
    // - ASTContext
    // - Callee (function reference)
    // - Args (array of arguments)
    // - Type (return type)
    // - ValueKind
    // - RParenLoc
    // - FPFeatures
    clang::CallExpr* callExpr = clang::CallExpr::Create(
        cCtx,
        funcRef,                          // Callee (function reference)
        allArgs,                          // Arguments (object + original args)
        MCE->getType(),                   // Return type
        MCE->getValueKind(),              // Value kind
        MCE->getExprLoc(),                // Location
        clang::FPOptionsOverride()        // FP options
    );

    return callExpr;
}

// ============================================================================
// Virtual Call Translation (Phase 45 Task 7)
// ============================================================================

clang::Expr* ExpressionHandler::translateVirtualCall(
    const clang::CXXMemberCallExpr* MCE,
    const clang::CXXMethodDecl* method,
    HandlerContext& ctx
) {
    // Phase 45 Task 7: Translate virtual call to COM-style vtable dispatch
    // Pattern: obj->lpVtbl->methodName(obj, args...)
    //
    // Steps:
    // 1. Get and translate the object expression
    // 2. Ensure we have a pointer (take address of value objects)
    // 3. Create lpVtbl member access: obj->lpVtbl
    // 4. Create method access from vtable: obj->lpVtbl->methodName
    // 5. Create call with object as first argument
    // 6. Translate and add remaining arguments

    clang::ASTContext& cCtx = ctx.getCContext();

    // Step 1: Get the implicit object argument
    const clang::Expr* objectExpr = MCE->getImplicitObjectArgument();
    if (!objectExpr) {
        // Virtual static methods don't exist, this shouldn't happen
        return nullptr;
    }

    // Translate the object expression
    clang::Expr* translatedObject = handleExpr(objectExpr, ctx);
    if (!translatedObject) {
        return nullptr;
    }

    // Step 2: Ensure we have a pointer for vtable access
    // Rules:
    // - ptr->method() → ptr (already a pointer)
    // - obj.method() → &obj (need address)
    // - ref.method() → ref (references become pointers in C)

    clang::QualType objectType = objectExpr->getType();
    clang::Expr* objectPtr = translatedObject;

    if (!objectType->isPointerType() && !objectType->isReferenceType()) {
        // Value object: need to take address
        clang::QualType ptrType = cCtx.getPointerType(translatedObject->getType());
        objectPtr = clang::UnaryOperator::Create(
            cCtx,
            translatedObject,
            clang::UO_AddrOf,
            ptrType,
            clang::VK_PRValue,
            clang::OK_Ordinary,
            MCE->getExprLoc(),
            false,
            clang::FPOptionsOverride()
        );
    }

    // Step 3: Create lpVtbl member access: obj->lpVtbl
    // We need to create a FieldDecl for lpVtbl
    // The lpVtbl field should already exist in the C struct (added by RecordHandler)
    // For now, we'll create a MemberExpr accessing lpVtbl

    // Get the class record
    const clang::CXXRecordDecl* cxxRecord = method->getParent();
    if (!cxxRecord) {
        return nullptr;
    }

    // Create lpVtbl field reference
    // Note: The actual lpVtbl FieldDecl should be looked up from the translated struct
    // For testing purposes, we'll create a synthetic one
    clang::IdentifierInfo& lpVtblII = cCtx.Idents.get("lpVtbl");

    // Get vtable struct type: const struct ClassName_vtable *
    std::string vtableStructName = cxxRecord->getNameAsString() + "_vtable";
    clang::RecordDecl* vtableStruct = cCtx.buildImplicitRecord(vtableStructName.c_str());
    clang::QualType vtableStructType = cCtx.getRecordType(vtableStruct);
    clang::QualType constVtableStructType = vtableStructType.withConst();
    clang::QualType lpVtblType = cCtx.getPointerType(constVtableStructType);

    // Create lpVtbl field (this should match the field added by RecordHandler)
    clang::FieldDecl* lpVtblField = clang::FieldDecl::Create(
        cCtx,
        vtableStruct,  // Parent record
        clang::SourceLocation(),
        clang::SourceLocation(),
        &lpVtblII,
        lpVtblType,
        cCtx.getTrivialTypeSourceInfo(lpVtblType),
        nullptr,  // No bitwidth
        false,    // Not mutable
        clang::ICIS_NoInit
    );

    // Create member expression: obj->lpVtbl
    clang::MemberExpr* lpVtblAccess = clang::MemberExpr::Create(
        cCtx,
        objectPtr,                       // Base: the object pointer
        true,                            // IsArrow: -> operator
        MCE->getExprLoc(),               // Operator location
        clang::NestedNameSpecifierLoc(), // No nested name
        clang::SourceLocation(),         // No template keyword
        lpVtblField,                     // Member: lpVtbl field
        clang::DeclAccessPair::make(lpVtblField, clang::AS_public),
        clang::DeclarationNameInfo(&lpVtblII, MCE->getExprLoc()),
        nullptr,                         // No template args
        lpVtblType,                      // Result type: vtable pointer
        clang::VK_LValue,
        clang::OK_Ordinary,
        clang::NOUR_None
    );

    // Step 4: Create method access from vtable: obj->lpVtbl->methodName
    // The vtable struct should have a field for each virtual method
    // Field name matches the method name

    std::string methodName = method->getNameAsString();

    // Handle destructors specially
    if (llvm::isa<clang::CXXDestructorDecl>(method)) {
        methodName = "destructor";
    }

    clang::IdentifierInfo& methodII = cCtx.Idents.get(methodName);

    // Create method function pointer type
    // Type: return_type (*)(struct ClassName*, args...)
    llvm::SmallVector<clang::QualType, 8> paramTypes;

    // First parameter: this pointer
    clang::QualType thisType = cCtx.getPointerType(
        cCtx.getRecordType(cCtx.buildImplicitRecord(cxxRecord->getNameAsString().c_str()))
    );
    paramTypes.push_back(thisType);

    // Remaining parameters
    for (const auto* param : method->parameters()) {
        paramTypes.push_back(param->getType());
    }

    clang::FunctionProtoType::ExtProtoInfo EPI;
    clang::QualType funcType = cCtx.getFunctionType(method->getReturnType(), paramTypes, EPI);
    clang::QualType funcPtrType = cCtx.getPointerType(funcType);

    // Create field for method in vtable
    clang::FieldDecl* methodField = clang::FieldDecl::Create(
        cCtx,
        vtableStruct,
        clang::SourceLocation(),
        clang::SourceLocation(),
        &methodII,
        funcPtrType,
        cCtx.getTrivialTypeSourceInfo(funcPtrType),
        nullptr,
        false,
        clang::ICIS_NoInit
    );

    // Create member expression: lpVtbl->methodName
    clang::MemberExpr* methodAccess = clang::MemberExpr::Create(
        cCtx,
        lpVtblAccess,                    // Base: lpVtbl pointer
        true,                            // IsArrow: -> operator
        MCE->getExprLoc(),
        clang::NestedNameSpecifierLoc(),
        clang::SourceLocation(),
        methodField,
        clang::DeclAccessPair::make(methodField, clang::AS_public),
        clang::DeclarationNameInfo(&methodII, MCE->getExprLoc()),
        nullptr,
        funcPtrType,                     // Result type: function pointer
        clang::VK_LValue,
        clang::OK_Ordinary,
        clang::NOUR_None
    );

    // Step 5: Build arguments - object first, then original arguments
    llvm::SmallVector<clang::Expr*, 8> allArgs;

    // First argument: the object pointer (same as used for lpVtbl access)
    allArgs.push_back(objectPtr);

    // Step 6: Translate remaining arguments
    for (unsigned i = 0; i < MCE->getNumArgs(); ++i) {
        clang::Expr* arg = handleExpr(MCE->getArg(i), ctx);
        if (!arg) {
            return nullptr;
        }
        allArgs.push_back(arg);
    }

    // Create the call expression
    // Callee is the method access expression (function pointer from vtable)
    clang::CallExpr* callExpr = clang::CallExpr::Create(
        cCtx,
        methodAccess,                // Callee: lpVtbl->methodName (function pointer)
        allArgs,                     // Arguments: object + original args
        MCE->getType(),              // Return type
        MCE->getValueKind(),
        MCE->getExprLoc(),
        clang::FPOptionsOverride()
    );

    return callExpr;
}

// ============================================================================
// Virtual Call Detection
// ============================================================================

bool ExpressionHandler::isVirtualCall(const clang::CXXMemberCallExpr* MCE) const {
    // Guard: MCE cannot be nullptr
    if (!MCE) {
        return false;
    }

    // Get the method declaration being called
    const clang::CXXMethodDecl* method = MCE->getMethodDecl();

    // Guard: Cannot determine if nullptr
    if (!method) {
        return false;
    }

    // Check if the method is virtual
    // Note: In C++, a method is virtual if:
    // 1. It's explicitly declared with 'virtual' keyword, or
    // 2. It overrides a virtual method from a base class
    // The isVirtual() method checks both conditions
    return method->isVirtual();
}

} // namespace cpptoc
