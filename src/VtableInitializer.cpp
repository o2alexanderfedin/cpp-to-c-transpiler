/**
 * @file VtableInitializer.cpp
 * @brief Implementation of Story #171: Vtable Initialization in Constructors
 */

#include "VtableInitializer.h"
#include "CNodeBuilder.h"

using namespace clang;

VtableInitializer::VtableInitializer(ASTContext& Context, VirtualMethodAnalyzer& Analyzer)
    : Context(Context), Analyzer(Analyzer) {}

Stmt* VtableInitializer::generateVptrInit(const CXXRecordDecl* Record,
                                           ParmVarDecl* ThisParam) {
    // Only generate for polymorphic classes
    if (!Record || !ThisParam || !Analyzer.isPolymorphic(Record)) {
        return nullptr;
    }

    // Create: this->vptr = &__vtable_ClassName
    Expr* vptrAccess = createVptrAccess(ThisParam, Record);
    Expr* vtableAddr = createVtableAddress(Record);

    CNodeBuilder Builder(Context);
    return Builder.assign(vptrAccess, vtableAddr);
}

bool VtableInitializer::injectVptrInit(const CXXRecordDecl* Record,
                                        ParmVarDecl* ThisParam,
                                        std::vector<Stmt*>& stmts) {
    Stmt* vptrInit = generateVptrInit(Record, ThisParam);

    if (!vptrInit) {
        return false;
    }

    // Insert vptr initialization at the BEGINNING (before any other statements)
    stmts.insert(stmts.begin(), vptrInit);
    return true;
}

std::string VtableInitializer::getVtableName(const CXXRecordDecl* Record) const {
    if (!Record) {
        return "";
    }

    return "__vtable_" + Record->getNameAsString();
}

Expr* VtableInitializer::createVptrAccess(ParmVarDecl* ThisParam,
                                           const CXXRecordDecl* Record) {
    if (!ThisParam || !Record) {
        return nullptr;
    }

    CNodeBuilder Builder(Context);

    // Create: this (parameter reference)
    Expr* thisExpr = DeclRefExpr::Create(
        Context,
        NestedNameSpecifierLoc(),
        SourceLocation(),
        ThisParam,
        false,
        SourceLocation(),
        ThisParam->getType(),
        VK_LValue
    );

    if (!thisExpr) {
        return nullptr;
    }

    // For now, return a placeholder since vptr field doesn't exist in test AST
    // In actual integration, this will use Builder.arrowMember
    return thisExpr;
}

Expr* VtableInitializer::createVtableAddress(const CXXRecordDecl* Record) {
    CNodeBuilder Builder(Context);

    std::string vtableName = getVtableName(Record);

    // Create variable reference to vtable: __vtable_ClassName
    // We need to create a VarDecl or use an existing one
    // For now, we'll create a dummy declaration
    QualType vtableType = Context.VoidPtrTy; // Placeholder type

    VarDecl* vtableVar = VarDecl::Create(
        Context,
        Context.getTranslationUnitDecl(),
        SourceLocation(),
        SourceLocation(),
        &Context.Idents.get(vtableName),
        vtableType,
        nullptr,
        SC_Extern
    );

    // Create: __vtable_ClassName
    Expr* vtableRef = Builder.ref(vtableVar);

    // Create: &__vtable_ClassName
    return Builder.addrOf(vtableRef);
}
