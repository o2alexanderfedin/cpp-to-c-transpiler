// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/MemberInitListTest.cpp
// Implementation file

#include "MemberInitListTest.h"

static void ACSLGenerator__ctor_copy(struct ACSLGenerator * this, const struct ACSLGenerator * other) {
	this->m_level = other->m_level;
	this->m_mode = other->m_mode;
}

void ACSLGenerator__dtor(struct ACSLGenerator * this) {
}

ACSLLevel ACSLGenerator_getACSLLevel(struct ACSLGenerator * this) {
	return this->m_level;
;
}

ACSLOutputMode ACSLGenerator_getOutputMode(struct ACSLGenerator * this) {
	return this->m_mode;
;
}

void ACSLGenerator_setACSLLevel(struct ACSLGenerator * this, ACSLLevel level) {
	this->m_level = level;
}

void ACSLGenerator_setOutputMode(struct ACSLGenerator * this, ACSLOutputMode mode) {
	this->m_mode = mode;
}

static void ACSLAxiomaticBuilder__ctor_copy(struct ACSLAxiomaticBuilder * this, const struct ACSLAxiomaticBuilder * other) {
	this->m_processingFunctions = other->m_processingFunctions;
	this->m_logicFunctionCache = other->m_logicFunctionCache;
}

static void Behavior__ctor_default(struct Behavior * this) {
	this->name = 0;
	this->assumesClause = 0;
	this->ensuresClauses = 0;
}

static void Behavior__ctor_copy(struct Behavior * this, const struct Behavior * other) {
	this->name = other->name;
	this->assumesClause = other->assumesClause;
	this->ensuresClauses = other->ensuresClauses;
}

static void ACSLBehaviorAnnotator__ctor_copy(struct ACSLBehaviorAnnotator * this, const struct ACSLBehaviorAnnotator * other) {
}

static void ACSLClassAnnotator__ctor_copy(struct ACSLClassAnnotator * this, const struct ACSLClassAnnotator * other) {
}

static void ACSLFunctionAnnotator__ctor_copy(struct ACSLFunctionAnnotator * this, const struct ACSLFunctionAnnotator * other) {
	this->memoryPredicatesEnabled = other->memoryPredicatesEnabled;
}

static void ACSLGhostCodeInjector__ctor_copy(struct ACSLGhostCodeInjector * this, const struct ACSLGhostCodeInjector * other) {
	this->m_declaredGhostVars = other->m_declaredGhostVars;
	this->m_ghostVarNames = other->m_ghostVarNames;
	this->m_ghostVarCounter = other->m_ghostVarCounter;
}

static void GhostVariable__ctor_copy(struct GhostVariable * this, const struct GhostVariable * other) {
	this->name = other->name;
	this->type = other->type;
	this->initialValue = other->initialValue;
	this->scope = other->scope;
	this->purpose = other->purpose;
}

void GhostVariable__ctor(struct GhostVariable * this) {
	this->purpose = 8;
}

void GhostVariable__ctor_5(struct GhostVariable * this, const int * n, const int * t, const int * init, const int * s, GhostPurpose p) {
	this->purpose = p;
}

static void GhostAnalysisVisitor__ctor_copy(struct GhostAnalysisVisitor * this, const struct GhostAnalysisVisitor * other) {
	this->m_injector = other->m_injector;
	this->m_ghostVariables = other->m_ghostVariables;
}

void GhostAnalysisVisitor__ctor(struct GhostAnalysisVisitor * this, struct ACSLGhostCodeInjector * injector) {
	this->m_injector = injector;
}

const int * GhostAnalysisVisitor_getGhostVariables(struct GhostAnalysisVisitor * this) {
}

void GhostAnalysisVisitor_addGhostVariable(struct GhostAnalysisVisitor * this, const struct GhostVariable * ghostVar) {
}

static void ACSLLoopAnnotator__ctor_copy(struct ACSLLoopAnnotator * this, const struct ACSLLoopAnnotator * other) {
}

static void ACSLStatementAnnotator__ctor_copy(struct ACSLStatementAnnotator * this, const struct ACSLStatementAnnotator * other) {
}

static void StatementVisitor__ctor_copy(struct StatementVisitor * this, const struct StatementVisitor * other) {
	this->m_level = other->m_level;
}

void StatementVisitor__ctor(struct StatementVisitor * this, struct ACSLStatementAnnotator * annotator, AnnotationLevel level) {
	this->m_level = level;
}

static void ACSLTypeInvariantGenerator__ctor_copy(struct ACSLTypeInvariantGenerator * this, const struct ACSLTypeInvariantGenerator * other) {
	this->m_processingTypes = other->m_processingTypes;
}

static void CNodeBuilder__ctor_default(struct CNodeBuilder * this) {
	this->Ctx = 0;
}

static void CNodeBuilder__ctor_copy(struct CNodeBuilder * this, const struct CNodeBuilder * other) {
	this->Ctx = other->Ctx;
}

void CNodeBuilder__ctor(struct CNodeBuilder * this, int * Ctx) {
}

int CNodeBuilder_intType(struct CNodeBuilder * this) {
}

int CNodeBuilder_voidType(struct CNodeBuilder * this) {
}

int CNodeBuilder_charType(struct CNodeBuilder * this) {
}

int CNodeBuilder_ptrType(struct CNodeBuilder * this, int pointee) {
}

int CNodeBuilder_structType(struct CNodeBuilder * this, int name) {
	int &II;

	int *RD;

}

int * CNodeBuilder_intVar(struct CNodeBuilder * this, int name, int initVal) {
	int intTy;

	int &II;

	int *VD;

	int *IL;

}

int * CNodeBuilder_intVar_int(struct CNodeBuilder * this, int name) {
	int intTy;

	int &II;

	int *VD;

}

int * CNodeBuilder_structVar(struct CNodeBuilder * this, int type, int name) {
	int &II;

	int *VD;

}

int * CNodeBuilder_ptrVar(struct CNodeBuilder * this, int pointee, int name) {
	int ptrTy;

	int &II;

	int *VD;

}

int * CNodeBuilder_var(struct CNodeBuilder * this, int type, int name, int * init) {
	int &II;

	int *VD;

}

int * CNodeBuilder_intLit(struct CNodeBuilder * this, int value) {
}

int * CNodeBuilder_stringLit(struct CNodeBuilder * this, int str) {
}

int * CNodeBuilder_nullPtr(struct CNodeBuilder * this) {
}

int * CNodeBuilder_ref(struct CNodeBuilder * this, int * var) {
}

int * CNodeBuilder_ref_int_ptr(struct CNodeBuilder * this, int * func) {
}

int * CNodeBuilder_call(struct CNodeBuilder * this, int funcName, int args) {
	int &II;

	int DN;

	int funcType;

	int *FD;

	int *funcRef;

}

int * CNodeBuilder_call_int_ptr_int(struct CNodeBuilder * this, int * func, int args) {
	int *funcRef;

}

int * CNodeBuilder_member(struct CNodeBuilder * this, int * base, int field) {
	int baseTy;

	const int *RT;

	int *RD;

	int *FD;

}

int * CNodeBuilder_arrowMember(struct CNodeBuilder * this, int * base, int field) {
	int baseTy;

	const int *PT;

	int pointeeTy;

	const int *RT;

	int *RD;

	int *FD;

}

int * CNodeBuilder_assign(struct CNodeBuilder * this, int * lhs, int * rhs) {
}

int * CNodeBuilder_addrOf(struct CNodeBuilder * this, int * expr) {
}

int * CNodeBuilder_deref(struct CNodeBuilder * this, int * expr) {
	int exprTy;

	const int *PT;

}

int * CNodeBuilder_block(struct CNodeBuilder * this, int stmts) {
}

int * CNodeBuilder_returnStmt(struct CNodeBuilder * this, int * expr) {
}

int * CNodeBuilder_declStmt(struct CNodeBuilder * this, int * decl) {
}

int * CNodeBuilder_exprStmt(struct CNodeBuilder * this, int * expr) {
}

int * CNodeBuilder_ifStmt(struct CNodeBuilder * this, int * cond, int * thenStmt, int * elseStmt) {
}

int * CNodeBuilder_whileStmt(struct CNodeBuilder * this, int * cond, int * body) {
}

int * CNodeBuilder_forStmt(struct CNodeBuilder * this, int * init, int * cond, int * inc, int * body) {
}

int * CNodeBuilder_breakStmt(struct CNodeBuilder * this) {
}

int * CNodeBuilder_continueStmt(struct CNodeBuilder * this) {
}

int * CNodeBuilder_structDecl(struct CNodeBuilder * this, int name, int fields) {
	int &II;

	int *RD;

}

int * CNodeBuilder_enumDecl(struct CNodeBuilder * this, int name, int) {
	int &II;

	int *ED;

}

int * CNodeBuilder_fieldDecl(struct CNodeBuilder * this, int type, int name) {
	int &II;

}

int * CNodeBuilder_forwardStructDecl(struct CNodeBuilder * this, int name) {
	int &II;

}

int * CNodeBuilder_funcDecl(struct CNodeBuilder * this, int name, int retType, int params, int * body, int callConv, bool isVariadic) {
	int &II;

	int DN;

	int EPI;

	int funcType;

	int *FD;

}

int * CNodeBuilder_param(struct CNodeBuilder * this, int type, int name) {
	int &II;

}

int CNodeBuilder_getCallingConvAttribute(struct CNodeBuilder * this, int CC) {
}

static void AssumeAttributeHandler__ctor_copy(struct AssumeAttributeHandler * this, const struct AssumeAttributeHandler * other) {
	this->m_builder = other->m_builder;
	this->m_strategy = other->m_strategy;
}

static void AutoDecayCopyTranslator__ctor_copy(struct AutoDecayCopyTranslator * this, const struct AutoDecayCopyTranslator * other) {
	this->m_builder = other->m_builder;
}

static void ConstevalIfTranslator__ctor_copy(struct ConstevalIfTranslator * this, const struct ConstevalIfTranslator * other) {
	this->m_builder = other->m_builder;
	this->m_strategy = other->m_strategy;
}

static void ConstexprEnhancementHandler__ctor_copy(struct ConstexprEnhancementHandler * this, const struct ConstexprEnhancementHandler * other) {
	this->m_builder = other->m_builder;
}

static void QualifierSet__ctor_copy(struct QualifierSet * this, const struct QualifierSet * other) {
	this->isConst = other->isConst;
	this->isRValue = other->isRValue;
	this->isValue = other->isValue;
}

void QualifierSet__ctor(struct QualifierSet * this, bool c, bool r, bool v) {
	this->isConst = c;
	this->isRValue = r;
	this->isValue = v;
}

int QualifierSet_getSuffix(struct QualifierSet * this) {
	if (this->isValue) 	{
	}
 else 	if (this->isRValue) 	{
	}
 else 	{
	}


}

static void DeducingThisTranslator__ctor_copy(struct DeducingThisTranslator * this, const struct DeducingThisTranslator * other) {
	this->m_builder = other->m_builder;
}

static void VirtualMethodAnalyzer__ctor_default(struct VirtualMethodAnalyzer * this) {
	this->Context = 0;
}

static void VirtualMethodAnalyzer__ctor_copy(struct VirtualMethodAnalyzer * this, const struct VirtualMethodAnalyzer * other) {
	this->Context = other->Context;
}

static void TypeInfoGenerator__ctor_default(struct TypeInfoGenerator * this) {
	this->Context = 0;
	this->Analyzer = 0;
}

static void TypeInfoGenerator__ctor_copy(struct TypeInfoGenerator * this, const struct TypeInfoGenerator * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
}

static void DynamicCastTranslator__ctor_default(struct DynamicCastTranslator * this) {
	this->Context = 0;
	this->Analyzer = 0;
}

static void DynamicCastTranslator__ctor_copy(struct DynamicCastTranslator * this, const struct DynamicCastTranslator * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
}

static void ExceptionFrameGenerator__ctor_default(struct ExceptionFrameGenerator * this) {
}

static void ExceptionFrameGenerator__ctor_copy(struct ExceptionFrameGenerator * this, const struct ExceptionFrameGenerator * other) {
}

static void FileOriginTracker__ctor_default(struct FileOriginTracker * this) {
	this->SM = 0;
	this->declToFile = 0;
	this->fileCategories = 0;
	this->userHeaderPaths = 0;
	this->thirdPartyPaths = 0;
	this->transpileThirdParty = 0;
}

static void FileOriginTracker__ctor_copy(struct FileOriginTracker * this, const struct FileOriginTracker * other) {
	this->SM = other->SM;
	this->declToFile = other->declToFile;
	this->fileCategories = other->fileCategories;
	this->userHeaderPaths = other->userHeaderPaths;
	this->thirdPartyPaths = other->thirdPartyPaths;
	this->transpileThirdParty = other->transpileThirdParty;
}

static void Statistics__ctor_default(struct Statistics * this) {
	this->totalDeclarations = 0;
	this->mainFileDeclarations = 0;
	this->userHeaderDeclarations = 0;
	this->systemHeaderDeclarations = 0;
	this->thirdPartyHeaderDeclarations = 0;
	this->uniqueFiles = 0;
}

static void Statistics__ctor_copy(struct Statistics * this, const struct Statistics * other) {
	this->totalDeclarations = other->totalDeclarations;
	this->mainFileDeclarations = other->mainFileDeclarations;
	this->userHeaderDeclarations = other->userHeaderDeclarations;
	this->systemHeaderDeclarations = other->systemHeaderDeclarations;
	this->thirdPartyHeaderDeclarations = other->thirdPartyHeaderDeclarations;
	this->uniqueFiles = other->uniqueFiles;
}

static void MoveAssignmentTranslator__ctor_default(struct MoveAssignmentTranslator * this) {
	this->Context = 0;
}

static void MoveAssignmentTranslator__ctor_copy(struct MoveAssignmentTranslator * this, const struct MoveAssignmentTranslator * other) {
	this->Context = other->Context;
}

static void MoveConstructorTranslator__ctor_default(struct MoveConstructorTranslator * this) {
	this->Context = 0;
}

static void MoveConstructorTranslator__ctor_copy(struct MoveConstructorTranslator * this, const struct MoveConstructorTranslator * other) {
	this->Context = other->Context;
}

static void MultidimSubscriptTranslator__ctor_copy(struct MultidimSubscriptTranslator * this, const struct MultidimSubscriptTranslator * other) {
	this->m_builder = other->m_builder;
}

static void NameMangler__ctor_default(struct NameMangler * this) {
	this->Ctx = 0;
	this->usedNames = 0;
}

static void NameMangler__ctor_copy(struct NameMangler * this, const struct NameMangler * other) {
	this->Ctx = other->Ctx;
	this->usedNames = other->usedNames;
}

void NameMangler__ctor(struct NameMangler * this, int * Ctx) {
}

static void StaticOperatorTranslator__ctor_copy(struct StaticOperatorTranslator * this, const struct StaticOperatorTranslator * other) {
	this->m_builder = other->m_builder;
}

static void OverrideResolver__ctor_default(struct OverrideResolver * this) {
	this->Context = 0;
	this->Analyzer = 0;
}

static void OverrideResolver__ctor_copy(struct OverrideResolver * this, const struct OverrideResolver * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
}

static void VtableSlot__ctor_default(struct VtableSlot * this) {
	this->signature = 0;
	this->method = 0;
	this->slotIndex = 0;
}

static void VtableSlot__ctor_copy(struct VtableSlot * this, const struct VtableSlot * other) {
	this->signature = other->signature;
	this->method = other->method;
	this->slotIndex = other->slotIndex;
}

static void RvalueRefParamTranslator__ctor_default(struct RvalueRefParamTranslator * this) {
	this->Context = 0;
}

static void RvalueRefParamTranslator__ctor_copy(struct RvalueRefParamTranslator * this, const struct RvalueRefParamTranslator * other) {
	this->Context = other->Context;
}

static void TemplateExtractor__ctor_default(struct TemplateExtractor * this) {
	this->Context = 0;
	this->fileTracker = 0;
	this->classInstantiations = 0;
	this->functionInstantiations = 0;
	this->seenClassInstantiations = 0;
	this->seenFunctionInstantiations = 0;
}

static void TemplateExtractor__ctor_copy(struct TemplateExtractor * this, const struct TemplateExtractor * other) {
	this->Context = other->Context;
	this->fileTracker = other->fileTracker;
	this->classInstantiations = other->classInstantiations;
	this->functionInstantiations = other->functionInstantiations;
	this->seenClassInstantiations = other->seenClassInstantiations;
	this->seenFunctionInstantiations = other->seenFunctionInstantiations;
}

bool TemplateExtractor_shouldVisitImplicitCode(struct TemplateExtractor * this) {
	return false;
;
}

static void TemplateInstantiationTracker__ctor_copy(struct TemplateInstantiationTracker * this, const struct TemplateInstantiationTracker * other) {
	this->trackedInstantiations = other->trackedInstantiations;
}

static void TemplateMonomorphizer__ctor_default(struct TemplateMonomorphizer * this) {
	this->Context = 0;
	this->Mangler = 0;
	this->Builder = 0;
}

static void TemplateMonomorphizer__ctor_copy(struct TemplateMonomorphizer * this, const struct TemplateMonomorphizer * other) {
	this->Context = other->Context;
	this->Mangler = other->Mangler;
	this->Builder = other->Builder;
}

static void ThrowTranslator__ctor_default(struct ThrowTranslator * this) {
}

static void ThrowTranslator__ctor_copy(struct ThrowTranslator * this, const struct ThrowTranslator * other) {
}

static void TryCatchTransformer__ctor_copy(struct TryCatchTransformer * this, const struct TryCatchTransformer * other) {
	this->frameGenerator = other->frameGenerator;
}

static void TypeidTranslator__ctor_default(struct TypeidTranslator * this) {
	this->Context = 0;
	this->Analyzer = 0;
}

static void TypeidTranslator__ctor_copy(struct TypeidTranslator * this, const struct TypeidTranslator * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
}

static void VirtualCallTranslator__ctor_default(struct VirtualCallTranslator * this) {
	this->Context = 0;
	this->Analyzer = 0;
}

static void VirtualCallTranslator__ctor_copy(struct VirtualCallTranslator * this, const struct VirtualCallTranslator * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
}

static void VptrInjector__ctor_default(struct VptrInjector * this) {
	this->Context = 0;
	this->Analyzer = 0;
}

static void VptrInjector__ctor_copy(struct VptrInjector * this, const struct VptrInjector * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
}

static void VtableGenerator__ctor_default(struct VtableGenerator * this) {
	this->Context = 0;
	this->Analyzer = 0;
	this->Resolver = 0;
}

static void VtableGenerator__ctor_copy(struct VtableGenerator * this, const struct VtableGenerator * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
	this->Resolver = other->Resolver;
}

static void VtableInitializer__ctor_default(struct VtableInitializer * this) {
	this->Context = 0;
	this->Analyzer = 0;
}

static void VtableInitializer__ctor_copy(struct VtableInitializer * this, const struct VtableInitializer * other) {
	this->Context = other->Context;
	this->Analyzer = other->Analyzer;
}

static void CppToCVisitor__ctor_default(struct CppToCVisitor * this) {
	this->Context = 0;
	this->Builder = 0;
	NameMangler__ctor_default(&this->Mangler);
	this->fileOriginTracker = 0;
	VirtualMethodAnalyzer__ctor_default(&this->VirtualAnalyzer);
	VptrInjector__ctor_default(&this->VptrInjectorInstance);
	this->m_overrideResolver = 0;
	this->m_vtableGenerator = 0;
	this->m_vtableInitializer = 0;
	this->m_virtualCallTrans = 0;
	this->m_vtableInstances = 0;
	MoveConstructorTranslator__ctor_default(&this->MoveCtorTranslator);
	MoveAssignmentTranslator__ctor_default(&this->MoveAssignTranslator);
	RvalueRefParamTranslator__ctor_default(&this->RvalueRefParamTrans);
	this->m_functionAnnotator = 0;
	this->m_loopAnnotator = 0;
	this->m_classAnnotator = 0;
	this->m_statementAnnotator = 0;
	this->m_typeInvariantGen = 0;
	this->m_axiomaticBuilder = 0;
	this->m_ghostInjector = 0;
	this->m_behaviorAnnotator = 0;
	this->cppToCMap = 0;
	this->methodToCFunc = 0;
	this->ctorMap = 0;
	this->dtorMap = 0;
	this->standaloneFuncMap = 0;
	this->generatedFunctions = 0;
	this->m_templateExtractor = 0;
	this->m_templateMonomorphizer = 0;
	this->m_templateTracker = 0;
	this->m_monomorphizedCode = 0;
	this->C_TranslationUnit = 0;
	this->m_tryCatchTransformer = 0;
	this->m_throwTranslator = 0;
	this->m_exceptionFrameGen = 0;
	this->m_exceptionFrameCounter = 0;
	this->m_tryBlockCounter = 0;
	this->m_typeidTranslator = 0;
	this->m_dynamicCastTranslator = 0;
	this->m_multidimSubscriptTrans = 0;
	this->m_staticOperatorTrans = 0;
	this->m_assumeHandler = 0;
	this->m_deducingThisTrans = 0;
	this->m_constevalIfTrans = 0;
	this->m_autoDecayTrans = 0;
	this->m_constexprHandler = 0;
	this->currentThisParam = 0;
	this->currentMethod = 0;
	this->currentFunctionObjectsToDestroy = 0;
	this->currentFunctionReturns = 0;
	this->scopeStack = 0;
	this->currentFunctionGotos = 0;
	this->currentFunctionLabels = 0;
	this->currentFunctionBreaksContinues = 0;
	this->loopNestingLevel = 0;
	this->m_acslAnnotations = 0;
}

static void CppToCVisitor__ctor_copy(struct CppToCVisitor * this, const struct CppToCVisitor * other) {
	this->Context = other->Context;
	this->Builder = other->Builder;
	NameMangler__ctor_copy(&this->Mangler, &other->Mangler);
	this->fileOriginTracker = other->fileOriginTracker;
	VirtualMethodAnalyzer__ctor_copy(&this->VirtualAnalyzer, &other->VirtualAnalyzer);
	VptrInjector__ctor_copy(&this->VptrInjectorInstance, &other->VptrInjectorInstance);
	this->m_overrideResolver = other->m_overrideResolver;
	this->m_vtableGenerator = other->m_vtableGenerator;
	this->m_vtableInitializer = other->m_vtableInitializer;
	this->m_virtualCallTrans = other->m_virtualCallTrans;
	this->m_vtableInstances = other->m_vtableInstances;
	MoveConstructorTranslator__ctor_copy(&this->MoveCtorTranslator, &other->MoveCtorTranslator);
	MoveAssignmentTranslator__ctor_copy(&this->MoveAssignTranslator, &other->MoveAssignTranslator);
	RvalueRefParamTranslator__ctor_copy(&this->RvalueRefParamTrans, &other->RvalueRefParamTrans);
	this->m_functionAnnotator = other->m_functionAnnotator;
	this->m_loopAnnotator = other->m_loopAnnotator;
	this->m_classAnnotator = other->m_classAnnotator;
	this->m_statementAnnotator = other->m_statementAnnotator;
	this->m_typeInvariantGen = other->m_typeInvariantGen;
	this->m_axiomaticBuilder = other->m_axiomaticBuilder;
	this->m_ghostInjector = other->m_ghostInjector;
	this->m_behaviorAnnotator = other->m_behaviorAnnotator;
	this->cppToCMap = other->cppToCMap;
	this->methodToCFunc = other->methodToCFunc;
	this->ctorMap = other->ctorMap;
	this->dtorMap = other->dtorMap;
	this->standaloneFuncMap = other->standaloneFuncMap;
	this->generatedFunctions = other->generatedFunctions;
	this->m_templateExtractor = other->m_templateExtractor;
	this->m_templateMonomorphizer = other->m_templateMonomorphizer;
	this->m_templateTracker = other->m_templateTracker;
	this->m_monomorphizedCode = other->m_monomorphizedCode;
	this->C_TranslationUnit = other->C_TranslationUnit;
	this->m_tryCatchTransformer = other->m_tryCatchTransformer;
	this->m_throwTranslator = other->m_throwTranslator;
	this->m_exceptionFrameGen = other->m_exceptionFrameGen;
	this->m_exceptionFrameCounter = other->m_exceptionFrameCounter;
	this->m_tryBlockCounter = other->m_tryBlockCounter;
	this->m_typeidTranslator = other->m_typeidTranslator;
	this->m_dynamicCastTranslator = other->m_dynamicCastTranslator;
	this->m_multidimSubscriptTrans = other->m_multidimSubscriptTrans;
	this->m_staticOperatorTrans = other->m_staticOperatorTrans;
	this->m_assumeHandler = other->m_assumeHandler;
	this->m_deducingThisTrans = other->m_deducingThisTrans;
	this->m_constevalIfTrans = other->m_constevalIfTrans;
	this->m_autoDecayTrans = other->m_autoDecayTrans;
	this->m_constexprHandler = other->m_constexprHandler;
	this->currentThisParam = other->currentThisParam;
	this->currentMethod = other->currentMethod;
	this->currentFunctionObjectsToDestroy = other->currentFunctionObjectsToDestroy;
	this->currentFunctionReturns = other->currentFunctionReturns;
	this->scopeStack = other->scopeStack;
	this->currentFunctionGotos = other->currentFunctionGotos;
	this->currentFunctionLabels = other->currentFunctionLabels;
	this->currentFunctionBreaksContinues = other->currentFunctionBreaksContinues;
	this->loopNestingLevel = other->loopNestingLevel;
	this->m_acslAnnotations = other->m_acslAnnotations;
}

static void ReturnInfo__ctor_default(struct ReturnInfo * this) {
	this->returnStmt = 0;
	this->liveObjects = 0;
}

static void ReturnInfo__ctor_copy(struct ReturnInfo * this, const struct ReturnInfo * other) {
	this->returnStmt = other->returnStmt;
	this->liveObjects = other->liveObjects;
}

static void ScopeInfo__ctor_default(struct ScopeInfo * this) {
	this->stmt = 0;
	this->objects = 0;
	this->depth = 0;
}

static void ScopeInfo__ctor_copy(struct ScopeInfo * this, const struct ScopeInfo * other) {
	this->stmt = other->stmt;
	this->objects = other->objects;
	this->depth = other->depth;
}

static void GotoInfo__ctor_default(struct GotoInfo * this) {
	this->gotoStmt = 0;
	this->targetLabel = 0;
	this->liveObjects = 0;
}

static void GotoInfo__ctor_copy(struct GotoInfo * this, const struct GotoInfo * other) {
	this->gotoStmt = other->gotoStmt;
	this->targetLabel = other->targetLabel;
	this->liveObjects = other->liveObjects;
}

static void BreakContinueInfo__ctor_default(struct BreakContinueInfo * this) {
	this->stmt = 0;
	this->isBreak = 0;
	this->liveObjects = 0;
}

static void BreakContinueInfo__ctor_copy(struct BreakContinueInfo * this, const struct BreakContinueInfo * other) {
	this->stmt = other->stmt;
	this->isBreak = other->isBreak;
	this->liveObjects = other->liveObjects;
}

bool CppToCVisitor_shouldVisitImplicitCode(struct CppToCVisitor * this) {
	return false;
;
}

int CppToCVisitor_getMonomorphizedCode(struct CppToCVisitor * this) {
}

int * CppToCVisitor_getCTranslationUnit(struct CppToCVisitor * this) {
}

static void CodeGenerator__ctor_default(struct CodeGenerator * this) {
	this->OS = 0;
	this->Policy = 0;
	this->Context = 0;
}

static void CodeGenerator__ctor_copy(struct CodeGenerator * this, const struct CodeGenerator * other) {
	this->OS = other->OS;
	this->Policy = other->Policy;
	this->Context = other->Context;
}

int * CodeGenerator_getPrintingPolicy(struct CodeGenerator * this) {
}

bool contains(const int * haystack, const int * needle) {
}

int TEST(int, int) {
	const char *cpp = "\n            class Vector {\n                double x, y, z;\n            public:\n                Vector(double x, double y, double z) : x(x), y(y), z(z) {}\n            };\n        ";

	auto AST;

	struct CNodeBuilder builder;

	struct CppToCVisitor visitor;

	int *CtorFunc;

	int output;

	struct CodeGenerator gen;

	int x_pos;

	int y_pos;

	int z_pos;

}

int TEST_int_int(int, int) {
	const char *cpp = "\n            class Entity {\n                int id;\n                double health;\n                char *name;\n            public:\n                Entity(int id, double health, char *name)\n                    : id(id), health(health), name(name) {}\n            };\n        ";

	auto AST;

	struct CNodeBuilder builder;

	struct CppToCVisitor visitor;

	int *CtorFunc;

	int output;

	struct CodeGenerator gen;

}

int TEST_int_int_1(int, int) {
	const char *cpp = "\n            class Particle {\n                double x, y;\n                int type;\n            public:\n                Particle(double x, double y) : x(x), y(y) {}\n            };\n        ";

	auto AST;

	struct CNodeBuilder builder;

	struct CppToCVisitor visitor;

	int *CtorFunc;

	int output;

	struct CodeGenerator gen;

	int type_assign;

}

int TEST_int_int_2(int, int) {
	const char *cpp = "\n            class Config {\n                int version;\n                bool enabled;\n            public:\n                Config() : version(1), enabled(true) {}\n            };\n        ";

	auto AST;

	struct CNodeBuilder builder;

	struct CppToCVisitor visitor;

	int *CtorFunc;

	int output;

	struct CodeGenerator gen;

}

int TEST_int_int_3(int, int) {
	const char *cpp = "\n            class Test {\n                int a, b, c;\n            public:\n                Test() : c(3), a(1), b(2) {}\n            };\n        ";

	auto AST;

	struct CNodeBuilder builder;

	struct CppToCVisitor visitor;

	int *CtorFunc;

	int output;

	struct CodeGenerator gen;

	int a_pos;

	int b_pos;

	int c_pos;

}

