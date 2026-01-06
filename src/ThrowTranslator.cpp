// ThrowTranslator.cpp - Implementation of throw expression translator
// Story #79: Implement Throw Expression Translation
// Phase 5: AST-based implementation (COMPLETE - returns C AST nodes, not strings)

#include "ThrowTranslator.h"
#include "NameMangler.h"
#include "dispatch/CppToCVisitorDispatcher.h"
#include "mapping/ExprMapper.h"
#include "mapping/DeclMapper.h"
#include "CNodeBuilder.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/ExprCXX.h"
#include "clang/AST/Type.h"
#include "llvm/Support/raw_ostream.h"
#include <sstream>

namespace clang {

// ============================================================================
// Phase 5: AST-based methods (NEW - returns C AST nodes)
// ============================================================================

// Generate complete throw translation as C AST
CompoundStmt* ThrowTranslator::generateThrowCode(
    const CXXThrowExpr *throwExpr,
    const ::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    if (!throwExpr) {
        return nullptr;
    }

    CNodeBuilder builder(cCtx);

    // Check for re-throw (throw; with no expression)
    const Expr *subExpr = throwExpr->getSubExpr();
    if (!subExpr) {
        CallExpr* rethrowCall = generateRethrowCode(cCtx);
        return builder.block({rethrowCall});
    }

    // Get the exception type
    QualType exceptionType = subExpr->getType();

    // 1. Generate exception object allocation
    std::string exceptionVarName = "__ex";
    VarDecl* exceptionVar = generateExceptionAllocation(
        exceptionType, cCtx, exceptionVarName
    );

    // 2. Generate constructor call
    CallExpr* ctorCall = generateConstructorCall(
        throwExpr, exceptionVar, disp, cppCtx, cCtx
    );

    // 3. Extract type info
    StringLiteral* typeInfoLiteral = extractTypeInfo(exceptionType, cCtx);

    // 4. Generate cxx_throw call
    CallExpr* throwCall = generateCxxThrowCall(exceptionVar, typeInfoLiteral, cCtx);

    // 5. Create compound statement with all three statements
    std::vector<Stmt*> stmts;
    stmts.push_back(builder.declStmt(exceptionVar));
    if (ctorCall) {
        stmts.push_back(ctorCall);
    }
    stmts.push_back(throwCall);

    return builder.block(stmts);
}

// Generate re-throw as C AST
CallExpr* ThrowTranslator::generateRethrowCode(ASTContext& cCtx) const {
    CNodeBuilder builder(cCtx);

    // Re-throw uses current exception from frame
    // cxx_throw(frame.exception_object, frame.exception_type);

    // Create FunctionDecl for cxx_throw
    FunctionDecl* cxxThrowDecl = createCxxThrowDecl(cCtx);

    // Create reference to frame.exception_object and frame.exception_type
    // For now, we'll create placeholder null pointers
    // TODO: Implement proper frame member access when frame struct is available
    Expr* exceptionObj = builder.nullPtr();
    Expr* exceptionType = builder.nullPtr();

    std::vector<Expr*> args = {exceptionObj, exceptionType};
    return builder.call(cxxThrowDecl, args);
}

// Generate exception object allocation as C AST
VarDecl* ThrowTranslator::generateExceptionAllocation(
    QualType exceptionType,
    ASTContext& cCtx,
    const std::string& exceptionVarName
) const {
    CNodeBuilder builder(cCtx);

    // Get type name for struct
    std::string typeName;
    if (const RecordType *RT = exceptionType->getAs<RecordType>()) {
        if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(RT->getDecl())) {
            typeName = RD->getNameAsString();
        } else {
            typeName = exceptionType.getAsString();
        }
    } else {
        typeName = exceptionType.getAsString();
    }

    // Create pointer type: struct Type*
    QualType structType = builder.structType(typeName);
    QualType ptrType = builder.ptrType(structType);

    // Create malloc call: malloc(sizeof(struct Type))
    FunctionDecl* mallocDecl = createMallocDecl(cCtx);

    // sizeof(struct Type) - create a UnaryExprOrTypeTraitExpr
    UnaryExprOrTypeTraitExpr* sizeofExpr = new (cCtx) UnaryExprOrTypeTraitExpr(
        UETT_SizeOf,
        cCtx.getTrivialTypeSourceInfo(structType),
        cCtx.getSizeType(),
        SourceLocation(),
        SourceLocation()
    );

    std::vector<Expr*> mallocArgs = {sizeofExpr};
    CallExpr* mallocCall = builder.call(mallocDecl, mallocArgs);

    // Cast malloc result to struct Type*
    CStyleCastExpr* cast = CStyleCastExpr::Create(
        cCtx,
        ptrType,
        VK_PRValue,
        CK_BitCast,
        mallocCall,
        nullptr,
        FPOptionsOverride(),
        cCtx.getTrivialTypeSourceInfo(ptrType),
        SourceLocation(),
        SourceLocation()
    );

    // Create variable: struct Type *__ex = (struct Type*)malloc(sizeof(struct Type));
    VarDecl* varDecl = builder.var(ptrType, exceptionVarName, cast);

    return varDecl;
}

// Generate exception constructor call as C AST
CallExpr* ThrowTranslator::generateConstructorCall(
    const CXXThrowExpr *throwExpr,
    VarDecl* exceptionVar,
    const ::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    CNodeBuilder builder(cCtx);

    const Expr *subExpr = throwExpr->getSubExpr();
    if (!subExpr) {
        return nullptr;
    }

    // Recursively unwrap expression to find constructor
    const Expr *currentExpr = subExpr;
    const CXXConstructExpr *ctorExpr = nullptr;

    // Unwrap all wrapper expressions to find the constructor
    while (currentExpr && !ctorExpr) {
        // Try direct cast
        ctorExpr = dyn_cast<CXXConstructExpr>(currentExpr);
        if (ctorExpr) break;

        // Unwrap CXXFunctionalCastExpr (e.g., Error("msg"))
        if (const CXXFunctionalCastExpr *funcCast = dyn_cast<CXXFunctionalCastExpr>(currentExpr)) {
            currentExpr = funcCast->getSubExpr();
            continue;
        }

        // Unwrap MaterializeTemporaryExpr
        if (const MaterializeTemporaryExpr *matExpr = dyn_cast<MaterializeTemporaryExpr>(currentExpr)) {
            currentExpr = matExpr->getSubExpr();
            continue;
        }

        // Unwrap CXXBindTemporaryExpr
        if (const CXXBindTemporaryExpr *bindExpr = dyn_cast<CXXBindTemporaryExpr>(currentExpr)) {
            currentExpr = bindExpr->getSubExpr();
            continue;
        }

        // Unwrap implicit casts
        if (const ImplicitCastExpr *castExpr = dyn_cast<ImplicitCastExpr>(currentExpr)) {
            currentExpr = castExpr->getSubExpr();
            continue;
        }

        // Can't unwrap further
        break;
    }

    if (!ctorExpr) {
        // Fallback: simple assignment or copy
        // TODO: Implement assignment when needed
        llvm::errs() << "[ThrowTranslator] WARNING: No constructor found, skipping initialization\n";
        return nullptr;
    }

    // Get constructor declaration and translate it
    const CXXConstructorDecl *ctorDecl = ctorExpr->getConstructor();
    FunctionDecl* cCtorDecl = getConstructorDecl(ctorDecl, disp, cppCtx, cCtx);

    // Translate constructor arguments
    std::vector<Expr*> cArgs = translateArguments(ctorExpr, disp, cppCtx, cCtx);

    // Prepend exceptionVar as first argument (this pointer)
    std::vector<Expr*> allArgs;
    allArgs.push_back(builder.ref(exceptionVar));
    allArgs.insert(allArgs.end(), cArgs.begin(), cArgs.end());

    // Create constructor call: Error__ctor(__ex, "message")
    return builder.call(cCtorDecl, allArgs);
}

// Extract type info string literal as C AST
StringLiteral* ThrowTranslator::extractTypeInfo(
    QualType exceptionType,
    ASTContext& cCtx
) const {
    CNodeBuilder builder(cCtx);

    // Use simplified type name for now (in production, use Itanium mangling)
    std::string typeName = getMangledTypeName(exceptionType);

    return builder.stringLit(typeName);
}

// Generate cxx_throw runtime call as C AST
CallExpr* ThrowTranslator::generateCxxThrowCall(
    VarDecl* exceptionVar,
    StringLiteral* typeInfoLiteral,
    ASTContext& cCtx
) const {
    CNodeBuilder builder(cCtx);

    // Create FunctionDecl for cxx_throw
    FunctionDecl* cxxThrowDecl = createCxxThrowDecl(cCtx);

    // Create arguments: cxx_throw(exception_obj, type_info)
    std::vector<Expr*> args;
    args.push_back(builder.ref(exceptionVar));
    args.push_back(typeInfoLiteral);

    // Create call expression
    return builder.call(cxxThrowDecl, args);
}

// ============================================================================
// Private helper methods (Phase 5: AST-based)
// ============================================================================

// Get mangled type name for exception type
std::string ThrowTranslator::getMangledTypeName(QualType type) const {
    // Remove const, volatile, reference
    QualType actualType = type.getCanonicalType();
    actualType.removeLocalConst();
    actualType.removeLocalVolatile();

    if (actualType->isReferenceType()) {
        actualType = actualType.getNonReferenceType();
    }

    // Use NameMangler API for consistent name generation
    if (const RecordType *RT = actualType->getAs<RecordType>()) {
        if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(RT->getDecl())) {
            return cpptoc::mangle_class(RD);
        }
    }

    return actualType.getAsString();
}

// Translate constructor arguments to C AST
std::vector<Expr*> ThrowTranslator::translateArguments(
    const CXXConstructExpr *ctorExpr,
    const ::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    std::vector<Expr*> cArgs;

    cpptoc::ExprMapper& exprMapper = disp.getExprMapper();

    unsigned numArgs = ctorExpr->getNumArgs();
    for (unsigned i = 0; i < numArgs; ++i) {
        const Expr *cppArg = ctorExpr->getArg(i);

        // Dispatch the argument through the dispatcher
        Expr* cppArgNonConst = const_cast<Expr*>(cppArg);
        bool handled = disp.dispatch(cppCtx, cCtx, cppArgNonConst);

        if (!handled) {
            llvm::errs() << "[ThrowTranslator] WARNING: Constructor argument " << i
                         << " not handled by dispatcher: " << cppArg->getStmtClassName() << "\n";
            continue;
        }

        // Retrieve the translated C expression from ExprMapper
        Expr* cArg = exprMapper.getCreated(cppArg);

        if (!cArg) {
            llvm::errs() << "[ThrowTranslator] WARNING: Constructor argument " << i
                         << " dispatched but not in ExprMapper\n";
            continue;
        }

        cArgs.push_back(cArg);
    }

    return cArgs;
}

// Create FunctionDecl for malloc
FunctionDecl* ThrowTranslator::createMallocDecl(ASTContext& cCtx) const {
    CNodeBuilder builder(cCtx);

    // void* malloc(size_t size)
    QualType voidPtrType = builder.ptrType(builder.voidType());
    QualType sizeTType = cCtx.getSizeType();

    ParmVarDecl* sizeParam = builder.param(sizeTType, "size");

    FunctionDecl* mallocDecl = builder.funcDecl(
        "malloc",
        voidPtrType,
        {sizeParam},
        nullptr,  // no body
        CC_C,
        false,    // not variadic
        cCtx.getTranslationUnitDecl()
    );

    return mallocDecl;
}

// Create FunctionDecl for cxx_throw
FunctionDecl* ThrowTranslator::createCxxThrowDecl(ASTContext& cCtx) const {
    CNodeBuilder builder(cCtx);

    // void cxx_throw(void* exception_obj, const char* type_info)
    QualType voidPtrType = builder.ptrType(builder.voidType());
    QualType constCharPtrType = builder.ptrType(cCtx.getConstType(builder.charType()));

    ParmVarDecl* exceptionObjParam = builder.param(voidPtrType, "exception_object");
    ParmVarDecl* typeInfoParam = builder.param(constCharPtrType, "type_info");

    FunctionDecl* cxxThrowDecl = builder.funcDecl(
        "cxx_throw",
        builder.voidType(),
        {exceptionObjParam, typeInfoParam},
        nullptr,  // no body
        CC_C,
        false,    // not variadic
        cCtx.getTranslationUnitDecl()
    );

    return cxxThrowDecl;
}

// Get FunctionDecl for constructor
FunctionDecl* ThrowTranslator::getConstructorDecl(
    const CXXConstructorDecl* ctorDecl,
    const ::CppToCVisitorDispatcher& disp,
    const ASTContext& cppCtx,
    ASTContext& cCtx
) const {
    // Try to get from DeclMapper first (constructors are Decls)
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    clang::Decl* cDecl = declMapper.getCreated(ctorDecl);
    FunctionDecl* cCtorDecl = dyn_cast_or_null<FunctionDecl>(cDecl);

    if (cCtorDecl) {
        return cCtorDecl;
    }

    // If not in mapper, we need to trigger translation
    // Dispatch the constructor declaration
    CXXConstructorDecl* ctorDeclNonConst = const_cast<CXXConstructorDecl*>(ctorDecl);
    bool handled = disp.dispatch(cppCtx, cCtx, ctorDeclNonConst);

    if (!handled) {
        llvm::errs() << "[ThrowTranslator] ERROR: Constructor not handled by dispatcher\n";
        // Fallback: create a placeholder function decl
        CNodeBuilder builder(cCtx);
        std::string ctorName = cpptoc::mangle_constructor(ctorDecl);
        ParmVarDecl* thisParam = builder.param(
            builder.ptrType(builder.voidType()),
            "this"
        );
        return builder.funcDecl(
            ctorName,
            builder.voidType(),
            {thisParam},
            nullptr,
            CC_C,
            false,
            cCtx.getTranslationUnitDecl()
        );
    }

    // Retrieve from mapper after dispatch
    cDecl = declMapper.getCreated(ctorDecl);
    cCtorDecl = dyn_cast_or_null<FunctionDecl>(cDecl);
    assert(cCtorDecl && "Constructor must be in DeclMapper after successful dispatch");

    return cCtorDecl;
}

} // namespace clang
