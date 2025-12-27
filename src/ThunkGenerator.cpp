/**
 * @file ThunkGenerator.cpp
 * @brief Implementation of ThunkGenerator
 *
 * Phase 46, Group 2, Task 5: Thunk Function Generation
 */

#include "ThunkGenerator.h"
#include "MultipleInheritanceAnalyzer.h"
#include "CNodeBuilder.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/DeclCXX.h"
#include "clang/AST/Expr.h"
#include "clang/AST/Stmt.h"
#include <sstream>

using namespace clang;

// ============================================================================
// Constructor
// ============================================================================

ThunkGenerator::ThunkGenerator(ASTContext& ctx, ASTContext& astContext)
    : Ctx(ctx), ASTCtx(astContext) {}

// ============================================================================
// Public API: generateThunk
// ============================================================================

FunctionDecl* ThunkGenerator::generateThunk(
    const CXXRecordDecl* derived,
    const CXXMethodDecl* method,
    const CXXRecordDecl* nonPrimaryBase,
    uint64_t baseOffset
) {
    // Validate inputs
    if (!derived || !method || !nonPrimaryBase) {
        return nullptr;
    }

    // Don't generate thunk for primary base (offset == 0)
    if (baseOffset == 0) {
        return nullptr;
    }

    // Don't generate thunk for non-virtual methods
    if (!method->isVirtual()) {
        return nullptr;
    }

    // Create thunk name
    std::string thunkName = getThunkName(derived, method, nonPrimaryBase);
    if (thunkName.empty()) {
        return nullptr;
    }

    // Create thunk parameters (this + original params)
    std::string derivedTypeName = derived->getNameAsString();
    auto thunkParams = createThunkParams(method, derivedTypeName);

    // Create thunk body (adjust this + call real impl)
    CompoundStmt* thunkBody = createThunkBody(derived, method, baseOffset, thunkParams);
    if (!thunkBody) {
        return nullptr;
    }

    // Build thunk function
    CNodeBuilder builder(Ctx);

    // Get return type
    QualType returnType = method->getReturnType();

    // Create function declaration
    FunctionDecl* thunk = builder.funcDecl(
        thunkName,
        returnType,
        thunkParams,
        thunkBody
    );

    return thunk;
}

// ============================================================================
// Public API: generateAllThunks
// ============================================================================

std::vector<FunctionDecl*> ThunkGenerator::generateAllThunks(
    const CXXRecordDecl* derived
) {
    std::vector<FunctionDecl*> thunks;

    if (!derived) {
        return thunks;
    }

    // Use MultipleInheritanceAnalyzer to identify non-primary bases
    MultipleInheritanceAnalyzer analyzer(Ctx);
    auto nonPrimaryBases = analyzer.getNonPrimaryBases(derived);

    // For each non-primary base
    for (const auto* base : nonPrimaryBases) {
        // Calculate base offset
        uint64_t offset = analyzer.calculateBaseOffset(derived, base);

        // For each virtual method in the base
        for (const auto* baseMethod : base->methods()) {
            if (!baseMethod->isVirtual()) {
                continue;
            }

            // Find the overriding method in derived class
            const CXXMethodDecl* overridingMethod = nullptr;

            // Check if derived class overrides this method
            for (const auto* derivedMethod : derived->methods()) {
                if (!derivedMethod->isVirtual()) {
                    continue;
                }

                // Check if it overrides the base method
                // Simple name matching for now (could be improved with override analysis)
                if (derivedMethod->getNameAsString() == baseMethod->getNameAsString()) {
                    overridingMethod = derivedMethod;
                    break;
                }
            }

            // Generate thunk if method is overridden
            if (overridingMethod) {
                if (auto* thunk = generateThunk(derived, overridingMethod, base, offset)) {
                    thunks.push_back(thunk);
                }
            }
        }
    }

    return thunks;
}

// ============================================================================
// Public API: getThunkName
// ============================================================================

std::string ThunkGenerator::getThunkName(
    const CXXRecordDecl* derived,
    const CXXMethodDecl* method,
    const CXXRecordDecl* base
) {
    if (!derived || !method || !base) {
        return "";
    }

    // Pattern: ClassName_methodName_BaseName_thunk
    std::ostringstream oss;
    oss << derived->getNameAsString()
        << "_" << method->getNameAsString()
        << "_" << base->getNameAsString()
        << "_thunk";

    return oss.str();
}

// ============================================================================
// Private: getRealImplName
// ============================================================================

std::string ThunkGenerator::getRealImplName(
    const CXXRecordDecl* derived,
    const CXXMethodDecl* method
) {
    if (!derived || !method) {
        return "";
    }

    // Pattern: ClassName_methodName_impl
    std::ostringstream oss;
    oss << derived->getNameAsString()
        << "_" << method->getNameAsString()
        << "_impl";

    return oss.str();
}

// ============================================================================
// Private: createThunkParams
// ============================================================================

std::vector<ParmVarDecl*> ThunkGenerator::createThunkParams(
    const CXXMethodDecl* method,
    const std::string& derivedTypeName
) {
    std::vector<ParmVarDecl*> params;

    CNodeBuilder builder(Ctx);

    // First parameter: struct DerivedClass* this
    QualType derivedType = builder.structType(derivedTypeName);
    QualType thisType = builder.ptrType(derivedType);

    ParmVarDecl* thisParam = builder.param(thisType, "this");
    params.push_back(thisParam);

    // Add remaining parameters from original method
    for (unsigned i = 0; i < method->getNumParams(); ++i) {
        const ParmVarDecl* origParam = method->getParamDecl(i);

        // Create parameter with same type and name
        QualType paramType = origParam->getType();
        std::string paramName = origParam->getNameAsString();

        if (paramName.empty()) {
            // Generate name if parameter is unnamed
            std::ostringstream oss;
            oss << "param" << i;
            paramName = oss.str();
        }

        ParmVarDecl* param = builder.param(paramType, paramName);
        params.push_back(param);
    }

    return params;
}

// ============================================================================
// Private: createThunkBody
// ============================================================================

CompoundStmt* ThunkGenerator::createThunkBody(
    const CXXRecordDecl* derived,
    const CXXMethodDecl* method,
    uint64_t baseOffset,
    const std::vector<ParmVarDecl*>& thunkParams
) {
    if (!derived || !method || thunkParams.empty()) {
        return nullptr;
    }

    CNodeBuilder builder(Ctx);
    std::vector<Stmt*> stmts;

    // Get 'this' parameter (first parameter)
    ParmVarDecl* thisParam = thunkParams[0];

    // Step 1: Create adjusted this pointer
    // struct Derived* adjusted = (struct Derived*)((char*)this - offset);

    // Cast this to char*: (char*)this
    QualType charPtrType = builder.ptrType(builder.charType());
    CastExpr* thisToCharPtr = CStyleCastExpr::Create(
        Ctx,
        charPtrType,
        VK_PRValue,
        CK_BitCast,
        builder.ref(thisParam),
        nullptr,
        FPOptionsOverride(),
        Ctx.getTrivialTypeSourceInfo(charPtrType),
        SourceLocation(),
        SourceLocation()
    );

    // Subtract offset: (char*)this - offset
    IntegerLiteral* offsetLit = builder.intLit(static_cast<int>(baseOffset));
    BinaryOperator* subtraction = BinaryOperator::Create(
        Ctx,
        thisToCharPtr,
        offsetLit,
        BO_Sub,
        charPtrType,
        VK_PRValue,
        OK_Ordinary,
        SourceLocation(),
        FPOptionsOverride()
    );

    // Cast back to Derived*: (struct Derived*)((char*)this - offset)
    QualType derivedType = builder.structType(derived->getNameAsString());
    QualType derivedPtrType = builder.ptrType(derivedType);
    CastExpr* adjustedThis = CStyleCastExpr::Create(
        Ctx,
        derivedPtrType,
        VK_PRValue,
        CK_BitCast,
        subtraction,
        nullptr,
        FPOptionsOverride(),
        Ctx.getTrivialTypeSourceInfo(derivedPtrType),
        SourceLocation(),
        SourceLocation()
    );

    // Create local variable: struct Derived* adjusted = ...
    VarDecl* adjustedVar = builder.var(derivedPtrType, "adjusted", adjustedThis);

    // Add declaration statement
    stmts.push_back(builder.declStmt(adjustedVar));

    // Step 2: Call real implementation
    // RealImpl(adjusted, param1, param2, ...)

    std::string realImplName = getRealImplName(derived, method);

    // Build argument list
    std::vector<Expr*> args;

    // First argument: adjusted this pointer
    args.push_back(builder.ref(adjustedVar));

    // Remaining arguments: forward parameters
    for (size_t i = 1; i < thunkParams.size(); ++i) {
        args.push_back(builder.ref(thunkParams[i]));
    }

    // Create call expression
    CallExpr* call = builder.call(realImplName, args);

    // Step 3: Return or just call
    if (method->getReturnType()->isVoidType()) {
        // void method: just call
        stmts.push_back(call);
    } else {
        // non-void method: return call result
        stmts.push_back(builder.returnStmt(call));
    }

    // Create compound statement (block)
    return builder.block(stmts);
}
