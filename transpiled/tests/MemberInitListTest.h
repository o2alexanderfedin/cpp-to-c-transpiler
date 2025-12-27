// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/MemberInitListTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

typedef enum {
    Basic = 0,
    Full = 1
} ACSLLevel;
typedef enum {
    Inline = 0,
    Separate = 1
} ACSLOutputMode;
struct ACSLGenerator {
	const struct ACSLGenerator_vtable * vptr;
	ACSLLevel m_level;
	ACSLOutputMode m_mode;
};
static void ACSLGenerator__ctor_copy(struct ACSLGenerator * this, const struct ACSLGenerator * other);
void ACSLGenerator__dtor(struct ACSLGenerator * this);
ACSLLevel ACSLGenerator_getACSLLevel(struct ACSLGenerator * this);
ACSLOutputMode ACSLGenerator_getOutputMode(struct ACSLGenerator * this);
void ACSLGenerator_setACSLLevel(struct ACSLGenerator * this, ACSLLevel level);
void ACSLGenerator_setOutputMode(struct ACSLGenerator * this, ACSLOutputMode mode);
struct ACSLAxiomaticBuilder {
	const struct ACSLGenerator_vtable * vptr;
	ACSLLevel m_level;
	ACSLOutputMode m_mode;
	int m_processingFunctions;
	int m_logicFunctionCache;
};
static void ACSLAxiomaticBuilder__ctor_copy(struct ACSLAxiomaticBuilder * this, const struct ACSLAxiomaticBuilder * other);
struct Behavior {
	int name;
	int assumesClause;
	int ensuresClauses;
};
static void Behavior__ctor_default(struct Behavior * this);
static void Behavior__ctor_copy(struct Behavior * this, const struct Behavior * other);
struct ACSLBehaviorAnnotator {
	const struct ACSLGenerator_vtable * vptr;
	ACSLLevel m_level;
	ACSLOutputMode m_mode;
};
static void ACSLBehaviorAnnotator__ctor_copy(struct ACSLBehaviorAnnotator * this, const struct ACSLBehaviorAnnotator * other);
struct ACSLClassAnnotator {
	const struct ACSLGenerator_vtable * vptr;
	ACSLLevel m_level;
	ACSLOutputMode m_mode;
};
static void ACSLClassAnnotator__ctor_copy(struct ACSLClassAnnotator * this, const struct ACSLClassAnnotator * other);
struct ACSLFunctionAnnotator {
	const struct ACSLGenerator_vtable * vptr;
	ACSLLevel m_level;
	ACSLOutputMode m_mode;
	bool memoryPredicatesEnabled;
};
static void ACSLFunctionAnnotator__ctor_copy(struct ACSLFunctionAnnotator * this, const struct ACSLFunctionAnnotator * other);
struct ACSLGhostCodeInjector {
	const struct ACSLGenerator_vtable * vptr;
	ACSLLevel m_level;
	ACSLOutputMode m_mode;
	int m_declaredGhostVars;
	int m_ghostVarNames;
	unsigned int m_ghostVarCounter;
};
static void ACSLGhostCodeInjector__ctor_copy(struct ACSLGhostCodeInjector * this, const struct ACSLGhostCodeInjector * other);
typedef enum {
    MaxTracking = 0,
    MinTracking = 1,
    SumTracking = 2,
    CountTracking = 3,
    PreviousValue = 4,
    ArrayCopy = 5,
    InvariantHelper = 6,
    AssertionHelper = 7,
    Custom = 8
} GhostPurpose;
struct GhostVariable {
	int name;
	int type;
	int initialValue;
	const int * scope;
	GhostPurpose purpose;
};
static void GhostVariable__ctor_copy(struct GhostVariable * this, const struct GhostVariable * other);
void GhostVariable__ctor(struct GhostVariable * this);
void GhostVariable__ctor_5(struct GhostVariable * this, const int * n, const int * t, const int * init, const int * s, GhostPurpose p);
struct GhostAnalysisVisitor {
	struct ACSLGhostCodeInjector * m_injector;
	int m_ghostVariables;
};
static void GhostAnalysisVisitor__ctor_copy(struct GhostAnalysisVisitor * this, const struct GhostAnalysisVisitor * other);
void GhostAnalysisVisitor__ctor(struct GhostAnalysisVisitor * this, struct ACSLGhostCodeInjector * injector);
const int * GhostAnalysisVisitor_getGhostVariables(struct GhostAnalysisVisitor * this);
void GhostAnalysisVisitor_addGhostVariable(struct GhostAnalysisVisitor * this, const struct GhostVariable * ghostVar);
struct ACSLLoopAnnotator {
	const struct ACSLGenerator_vtable * vptr;
	ACSLLevel m_level;
	ACSLOutputMode m_mode;
};
static void ACSLLoopAnnotator__ctor_copy(struct ACSLLoopAnnotator * this, const struct ACSLLoopAnnotator * other);
typedef enum {
    None = 0,
    Basic = 1,
    Full = 2
} AnnotationLevel;
struct ACSLStatementAnnotator {
	const struct ACSLGenerator_vtable * vptr;
	ACSLLevel m_level;
	ACSLOutputMode m_mode;
};
static void ACSLStatementAnnotator__ctor_copy(struct ACSLStatementAnnotator * this, const struct ACSLStatementAnnotator * other);
struct StatementVisitor {
	AnnotationLevel m_level;
};
static void StatementVisitor__ctor_copy(struct StatementVisitor * this, const struct StatementVisitor * other);
void StatementVisitor__ctor(struct StatementVisitor * this, struct ACSLStatementAnnotator * annotator, AnnotationLevel level);
struct ACSLTypeInvariantGenerator {
	const struct ACSLGenerator_vtable * vptr;
	ACSLLevel m_level;
	ACSLOutputMode m_mode;
	int m_processingTypes;
};
static void ACSLTypeInvariantGenerator__ctor_copy(struct ACSLTypeInvariantGenerator * this, const struct ACSLTypeInvariantGenerator * other);
struct CNodeBuilder {
	int & Ctx;
};
static void CNodeBuilder__ctor_default(struct CNodeBuilder * this);
static void CNodeBuilder__ctor_copy(struct CNodeBuilder * this, const struct CNodeBuilder * other);
void CNodeBuilder__ctor(struct CNodeBuilder * this, int * Ctx);
int CNodeBuilder_intType(struct CNodeBuilder * this);
int CNodeBuilder_voidType(struct CNodeBuilder * this);
int CNodeBuilder_charType(struct CNodeBuilder * this);
int CNodeBuilder_ptrType(struct CNodeBuilder * this, int pointee);
int CNodeBuilder_structType(struct CNodeBuilder * this, int name);
int * CNodeBuilder_intVar(struct CNodeBuilder * this, int name, int initVal);
int * CNodeBuilder_intVar_int(struct CNodeBuilder * this, int name);
int * CNodeBuilder_structVar(struct CNodeBuilder * this, int type, int name);
int * CNodeBuilder_ptrVar(struct CNodeBuilder * this, int pointee, int name);
int * CNodeBuilder_var(struct CNodeBuilder * this, int type, int name, int * init);
int * CNodeBuilder_intLit(struct CNodeBuilder * this, int value);
int * CNodeBuilder_stringLit(struct CNodeBuilder * this, int str);
int * CNodeBuilder_nullPtr(struct CNodeBuilder * this);
int * CNodeBuilder_ref(struct CNodeBuilder * this, int * var);
int * CNodeBuilder_ref_int_ptr(struct CNodeBuilder * this, int * func);
int * CNodeBuilder_call(struct CNodeBuilder * this, int funcName, int args);
int * CNodeBuilder_call_int_ptr_int(struct CNodeBuilder * this, int * func, int args);
int * CNodeBuilder_member(struct CNodeBuilder * this, int * base, int field);
int * CNodeBuilder_arrowMember(struct CNodeBuilder * this, int * base, int field);
int * CNodeBuilder_assign(struct CNodeBuilder * this, int * lhs, int * rhs);
int * CNodeBuilder_addrOf(struct CNodeBuilder * this, int * expr);
int * CNodeBuilder_deref(struct CNodeBuilder * this, int * expr);
int * CNodeBuilder_block(struct CNodeBuilder * this, int stmts);
int * CNodeBuilder_returnStmt(struct CNodeBuilder * this, int * expr);
int * CNodeBuilder_declStmt(struct CNodeBuilder * this, int * decl);
int * CNodeBuilder_exprStmt(struct CNodeBuilder * this, int * expr);
int * CNodeBuilder_ifStmt(struct CNodeBuilder * this, int * cond, int * thenStmt, int * elseStmt);
int * CNodeBuilder_whileStmt(struct CNodeBuilder * this, int * cond, int * body);
int * CNodeBuilder_forStmt(struct CNodeBuilder * this, int * init, int * cond, int * inc, int * body);
int * CNodeBuilder_breakStmt(struct CNodeBuilder * this);
int * CNodeBuilder_continueStmt(struct CNodeBuilder * this);
int * CNodeBuilder_structDecl(struct CNodeBuilder * this, int name, int fields);
int * CNodeBuilder_enumDecl(struct CNodeBuilder * this, int name, int);
int * CNodeBuilder_fieldDecl(struct CNodeBuilder * this, int type, int name);
int * CNodeBuilder_forwardStructDecl(struct CNodeBuilder * this, int name);
int * CNodeBuilder_funcDecl(struct CNodeBuilder * this, int name, int retType, int params, int * body, int callConv, bool isVariadic);
int * CNodeBuilder_param(struct CNodeBuilder * this, int type, int name);
int CNodeBuilder_getCallingConvAttribute(struct CNodeBuilder * this, int CC);
typedef enum {
    Strip = 0,
    Comment = 1,
    Builtin = 2
} AssumeStrategy;
struct AssumeAttributeHandler {
	clang::CNodeBuilder & m_builder;
	AssumeStrategy m_strategy;
};
static void AssumeAttributeHandler__ctor_copy(struct AssumeAttributeHandler * this, const struct AssumeAttributeHandler * other);
struct AutoDecayCopyTranslator {
	clang::CNodeBuilder & m_builder;
};
static void AutoDecayCopyTranslator__ctor_copy(struct AutoDecayCopyTranslator * this, const struct AutoDecayCopyTranslator * other);
typedef enum {
    Runtime = 0,
    Optimistic = 1,
    Both = 2
} ConstevalStrategy;
struct ConstevalIfTranslator {
	CNodeBuilder & m_builder;
	ConstevalStrategy m_strategy;
};
static void ConstevalIfTranslator__ctor_copy(struct ConstevalIfTranslator * this, const struct ConstevalIfTranslator * other);
typedef enum {
    CompileTime = 0,
    Runtime = 1,
    NotConstexpr = 2
} ConstexprStrategy;
struct ConstexprEnhancementHandler {
	clang::CNodeBuilder & m_builder;
};
static void ConstexprEnhancementHandler__ctor_copy(struct ConstexprEnhancementHandler * this, const struct ConstexprEnhancementHandler * other);
struct QualifierSet {
	bool isConst;
	bool isRValue;
	bool isValue;
};
static void QualifierSet__ctor_copy(struct QualifierSet * this, const struct QualifierSet * other);
void QualifierSet__ctor(struct QualifierSet * this, bool c, bool r, bool v);
int QualifierSet_getSuffix(struct QualifierSet * this);
struct DeducingThisTranslator {
	clang::CNodeBuilder & m_builder;
};
static void DeducingThisTranslator__ctor_copy(struct DeducingThisTranslator * this, const struct DeducingThisTranslator * other);
struct VirtualMethodAnalyzer {
	int & Context;
};
static void VirtualMethodAnalyzer__ctor_default(struct VirtualMethodAnalyzer * this);
static void VirtualMethodAnalyzer__ctor_copy(struct VirtualMethodAnalyzer * this, const struct VirtualMethodAnalyzer * other);
typedef enum {
    CLASS_TYPE_INFO = 0,
    SI_CLASS_TYPE_INFO = 1,
    VMI_CLASS_TYPE_INFO = 2
} TypeInfoClass;
struct TypeInfoGenerator {
	int & Context;
	struct VirtualMethodAnalyzer * Analyzer;
};
static void TypeInfoGenerator__ctor_default(struct TypeInfoGenerator * this);
static void TypeInfoGenerator__ctor_copy(struct TypeInfoGenerator * this, const struct TypeInfoGenerator * other);
struct DynamicCastTranslator {
	int & Context;
	VirtualMethodAnalyzer & Analyzer;
};
static void DynamicCastTranslator__ctor_default(struct DynamicCastTranslator * this);
static void DynamicCastTranslator__ctor_copy(struct DynamicCastTranslator * this, const struct DynamicCastTranslator * other);
struct ExceptionFrameGenerator {
};
static void ExceptionFrameGenerator__ctor_default(struct ExceptionFrameGenerator * this);
static void ExceptionFrameGenerator__ctor_copy(struct ExceptionFrameGenerator * this, const struct ExceptionFrameGenerator * other);
struct FileOriginTracker {
	int & SM;
	int declToFile;
	int fileCategories;
	int userHeaderPaths;
	int thirdPartyPaths;
	bool transpileThirdParty;
};
static void FileOriginTracker__ctor_default(struct FileOriginTracker * this);
static void FileOriginTracker__ctor_copy(struct FileOriginTracker * this, const struct FileOriginTracker * other);
typedef enum {
    MainFile = 0,
    UserHeader = 1,
    SystemHeader = 2,
    ThirdPartyHeader = 3
} FileCategory;
struct Statistics {
	int totalDeclarations;
	int mainFileDeclarations;
	int userHeaderDeclarations;
	int systemHeaderDeclarations;
	int thirdPartyHeaderDeclarations;
	int uniqueFiles;
};
static void Statistics__ctor_default(struct Statistics * this);
static void Statistics__ctor_copy(struct Statistics * this, const struct Statistics * other);
struct MoveAssignmentTranslator {
	int & Context;
};
static void MoveAssignmentTranslator__ctor_default(struct MoveAssignmentTranslator * this);
static void MoveAssignmentTranslator__ctor_copy(struct MoveAssignmentTranslator * this, const struct MoveAssignmentTranslator * other);
struct MoveConstructorTranslator {
	int & Context;
};
static void MoveConstructorTranslator__ctor_default(struct MoveConstructorTranslator * this);
static void MoveConstructorTranslator__ctor_copy(struct MoveConstructorTranslator * this, const struct MoveConstructorTranslator * other);
struct MultidimSubscriptTranslator {
	clang::CNodeBuilder & m_builder;
};
static void MultidimSubscriptTranslator__ctor_copy(struct MultidimSubscriptTranslator * this, const struct MultidimSubscriptTranslator * other);
struct NameMangler {
	int & Ctx;
	int usedNames;
};
static void NameMangler__ctor_default(struct NameMangler * this);
static void NameMangler__ctor_copy(struct NameMangler * this, const struct NameMangler * other);
void NameMangler__ctor(struct NameMangler * this, int * Ctx);
struct StaticOperatorTranslator {
	clang::CNodeBuilder & m_builder;
};
static void StaticOperatorTranslator__ctor_copy(struct StaticOperatorTranslator * this, const struct StaticOperatorTranslator * other);
struct OverrideResolver {
	int & Context;
	VirtualMethodAnalyzer & Analyzer;
};
static void OverrideResolver__ctor_default(struct OverrideResolver * this);
static void OverrideResolver__ctor_copy(struct OverrideResolver * this, const struct OverrideResolver * other);
struct VtableSlot {
	int signature;
	int * method;
	unsigned int slotIndex;
};
static void VtableSlot__ctor_default(struct VtableSlot * this);
static void VtableSlot__ctor_copy(struct VtableSlot * this, const struct VtableSlot * other);
struct RvalueRefParamTranslator {
	int & Context;
};
static void RvalueRefParamTranslator__ctor_default(struct RvalueRefParamTranslator * this);
static void RvalueRefParamTranslator__ctor_copy(struct RvalueRefParamTranslator * this, const struct RvalueRefParamTranslator * other);
struct TemplateExtractor {
	int & Context;
	struct FileOriginTracker * fileTracker;
	int classInstantiations;
	int functionInstantiations;
	int seenClassInstantiations;
	int seenFunctionInstantiations;
};
static void TemplateExtractor__ctor_default(struct TemplateExtractor * this);
static void TemplateExtractor__ctor_copy(struct TemplateExtractor * this, const struct TemplateExtractor * other);
bool TemplateExtractor_shouldVisitImplicitCode(struct TemplateExtractor * this);
struct TemplateInstantiationTracker {
	int trackedInstantiations;
};
static void TemplateInstantiationTracker__ctor_copy(struct TemplateInstantiationTracker * this, const struct TemplateInstantiationTracker * other);
struct TemplateMonomorphizer {
	int & Context;
	NameMangler & Mangler;
	clang::CNodeBuilder & Builder;
};
static void TemplateMonomorphizer__ctor_default(struct TemplateMonomorphizer * this);
static void TemplateMonomorphizer__ctor_copy(struct TemplateMonomorphizer * this, const struct TemplateMonomorphizer * other);
struct ThrowTranslator {
};
static void ThrowTranslator__ctor_default(struct ThrowTranslator * this);
static void ThrowTranslator__ctor_copy(struct ThrowTranslator * this, const struct ThrowTranslator * other);
struct TryCatchTransformer {
	int frameGenerator;
};
static void TryCatchTransformer__ctor_copy(struct TryCatchTransformer * this, const struct TryCatchTransformer * other);
struct TypeidTranslator {
	int & Context;
	VirtualMethodAnalyzer & Analyzer;
};
static void TypeidTranslator__ctor_default(struct TypeidTranslator * this);
static void TypeidTranslator__ctor_copy(struct TypeidTranslator * this, const struct TypeidTranslator * other);
struct VirtualCallTranslator {
	int & Context;
	VirtualMethodAnalyzer & Analyzer;
};
static void VirtualCallTranslator__ctor_default(struct VirtualCallTranslator * this);
static void VirtualCallTranslator__ctor_copy(struct VirtualCallTranslator * this, const struct VirtualCallTranslator * other);
struct VptrInjector {
	int & Context;
	VirtualMethodAnalyzer & Analyzer;
};
static void VptrInjector__ctor_default(struct VptrInjector * this);
static void VptrInjector__ctor_copy(struct VptrInjector * this, const struct VptrInjector * other);
struct VtableGenerator {
	int & Context;
	VirtualMethodAnalyzer & Analyzer;
	struct OverrideResolver * Resolver;
};
static void VtableGenerator__ctor_default(struct VtableGenerator * this);
static void VtableGenerator__ctor_copy(struct VtableGenerator * this, const struct VtableGenerator * other);
struct VtableInitializer {
	int & Context;
	VirtualMethodAnalyzer & Analyzer;
};
static void VtableInitializer__ctor_default(struct VtableInitializer * this);
static void VtableInitializer__ctor_copy(struct VtableInitializer * this, const struct VtableInitializer * other);
struct CppToCVisitor {
	int & Context;
	clang::CNodeBuilder & Builder;
	struct NameMangler Mangler;
	cpptoc::FileOriginTracker & fileOriginTracker;
	struct VirtualMethodAnalyzer VirtualAnalyzer;
	struct VptrInjector VptrInjectorInstance;
	int m_overrideResolver;
	int m_vtableGenerator;
	int m_vtableInitializer;
	int m_virtualCallTrans;
	int m_vtableInstances;
	struct MoveConstructorTranslator MoveCtorTranslator;
	struct MoveAssignmentTranslator MoveAssignTranslator;
	struct RvalueRefParamTranslator RvalueRefParamTrans;
	int m_functionAnnotator;
	int m_loopAnnotator;
	int m_classAnnotator;
	int m_statementAnnotator;
	int m_typeInvariantGen;
	int m_axiomaticBuilder;
	int m_ghostInjector;
	int m_behaviorAnnotator;
	int cppToCMap;
	int methodToCFunc;
	int ctorMap;
	int dtorMap;
	int standaloneFuncMap;
	int generatedFunctions;
	int m_templateExtractor;
	int m_templateMonomorphizer;
	int m_templateTracker;
	int m_monomorphizedCode;
	int * C_TranslationUnit;
	int m_tryCatchTransformer;
	int m_throwTranslator;
	int m_exceptionFrameGen;
	unsigned int m_exceptionFrameCounter;
	unsigned int m_tryBlockCounter;
	int m_typeidTranslator;
	int m_dynamicCastTranslator;
	int m_multidimSubscriptTrans;
	int m_staticOperatorTrans;
	int m_assumeHandler;
	int m_deducingThisTrans;
	int m_constevalIfTrans;
	int m_autoDecayTrans;
	int m_constexprHandler;
	int * currentThisParam;
	int * currentMethod;
	int currentFunctionObjectsToDestroy;
	int currentFunctionReturns;
	int scopeStack;
	int currentFunctionGotos;
	int currentFunctionLabels;
	int currentFunctionBreaksContinues;
	unsigned int loopNestingLevel;
	int m_acslAnnotations;
};
static void CppToCVisitor__ctor_default(struct CppToCVisitor * this);
static void CppToCVisitor__ctor_copy(struct CppToCVisitor * this, const struct CppToCVisitor * other);
struct ReturnInfo {
	int * returnStmt;
	int liveObjects;
};
static void ReturnInfo__ctor_default(struct ReturnInfo * this);
static void ReturnInfo__ctor_copy(struct ReturnInfo * this, const struct ReturnInfo * other);
struct ScopeInfo {
	int * stmt;
	int objects;
	unsigned int depth;
};
static void ScopeInfo__ctor_default(struct ScopeInfo * this);
static void ScopeInfo__ctor_copy(struct ScopeInfo * this, const struct ScopeInfo * other);
struct GotoInfo {
	int * gotoStmt;
	int * targetLabel;
	int liveObjects;
};
static void GotoInfo__ctor_default(struct GotoInfo * this);
static void GotoInfo__ctor_copy(struct GotoInfo * this, const struct GotoInfo * other);
struct BreakContinueInfo {
	int * stmt;
	bool isBreak;
	int liveObjects;
};
static void BreakContinueInfo__ctor_default(struct BreakContinueInfo * this);
static void BreakContinueInfo__ctor_copy(struct BreakContinueInfo * this, const struct BreakContinueInfo * other);
bool CppToCVisitor_shouldVisitImplicitCode(struct CppToCVisitor * this);
int CppToCVisitor_getMonomorphizedCode(struct CppToCVisitor * this);
int * CppToCVisitor_getCTranslationUnit(struct CppToCVisitor * this);
struct CodeGenerator {
	int & OS;
	int Policy;
	int & Context;
};
static void CodeGenerator__ctor_default(struct CodeGenerator * this);
static void CodeGenerator__ctor_copy(struct CodeGenerator * this, const struct CodeGenerator * other);
int * CodeGenerator_getPrintingPolicy(struct CodeGenerator * this);
bool contains(const int * haystack, const int * needle);
int TEST(int, int);
int TEST_int_int(int, int);
int TEST_int_int_1(int, int);
int TEST_int_int_2(int, int);
int TEST_int_int_3(int, int);
