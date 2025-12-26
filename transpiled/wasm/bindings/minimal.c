// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./wasm/bindings/minimal.cpp
// Implementation file

#include "minimal.h"

static void TranspileOptions__ctor_default(struct TranspileOptions * this) {
	this->acslLevel = 0;
	this->acslOutputMode = 0;
	this->target = 0;
	this->cppStandard = 0;
	this->optimize = 0;
	this->monomorphizeTemplates = 0;
	this->templateInstantiationLimit = 0;
	this->enableExceptions = 0;
	this->exceptionModel = 0;
	this->enableRTTI = 0;
	this->usePragmaOnce = 0;
	this->generateDependencyGraph = 0;
}

static void TranspileOptions__ctor_copy(struct TranspileOptions * this, const struct TranspileOptions * other) {
	this->acslLevel = other->acslLevel;
	this->acslOutputMode = other->acslOutputMode;
	this->target = other->target;
	this->cppStandard = other->cppStandard;
	this->optimize = other->optimize;
	this->monomorphizeTemplates = other->monomorphizeTemplates;
	this->templateInstantiationLimit = other->templateInstantiationLimit;
	this->enableExceptions = other->enableExceptions;
	this->exceptionModel = other->exceptionModel;
	this->enableRTTI = other->enableRTTI;
	this->usePragmaOnce = other->usePragmaOnce;
	this->generateDependencyGraph = other->generateDependencyGraph;
}

static void ACSLConfig__ctor_default(struct ACSLConfig * this) {
	this->statements = 0;
	this->typeInvariants = 0;
	this->axiomatics = 0;
	this->ghostCode = 0;
	this->behaviors = 0;
	this->memoryPredicates = 0;
}

static void ACSLConfig__ctor_copy(struct ACSLConfig * this, const struct ACSLConfig * other) {
	this->statements = other->statements;
	this->typeInvariants = other->typeInvariants;
	this->axiomatics = other->axiomatics;
	this->ghostCode = other->ghostCode;
	this->behaviors = other->behaviors;
	this->memoryPredicates = other->memoryPredicates;
}

static void Diagnostic__ctor_default(struct Diagnostic * this) {
	this->line = 0;
	this->column = 0;
	this->message = 0;
	this->severity = 0;
}

static void Diagnostic__ctor_copy(struct Diagnostic * this, const struct Diagnostic * other) {
	this->line = other->line;
	this->column = other->column;
	this->message = other->message;
	this->severity = other->severity;
}

static void TranspileResult__ctor_default(struct TranspileResult * this) {
	this->success = 0;
	this->c = 0;
	this->h = 0;
	this->acsl = 0;
	this->dependencyGraph = 0;
	this->diagnostics = 0;
}

static void TranspileResult__ctor_copy(struct TranspileResult * this, const struct TranspileResult * other) {
	this->success = other->success;
	this->c = other->c;
	this->h = other->h;
	this->acsl = other->acsl;
	this->dependencyGraph = other->dependencyGraph;
	this->diagnostics = other->diagnostics;
}

static void Diagnostic__ctor_default(struct Diagnostic * this) {
	this->line = 0;
	this->column = 0;
	this->message = 0;
	this->severity = 0;
}

static void Diagnostic__ctor_copy(struct Diagnostic * this, const struct Diagnostic * other) {
	this->line = other->line;
	this->column = other->column;
	this->message = other->message;
	this->severity = other->severity;
}

static void ACSLOptions__ctor_default(struct ACSLOptions * this) {
	this->statements = 0;
	this->typeInvariants = 0;
	this->axiomatics = 0;
	this->ghostCode = 0;
	this->behaviors = 0;
	this->memoryPredicates = 0;
}

static void ACSLOptions__ctor_copy(struct ACSLOptions * this, const struct ACSLOptions * other) {
	this->statements = other->statements;
	this->typeInvariants = other->typeInvariants;
	this->axiomatics = other->axiomatics;
	this->ghostCode = other->ghostCode;
	this->behaviors = other->behaviors;
	this->memoryPredicates = other->memoryPredicates;
}

static void TranspileOptions__ctor_default(struct TranspileOptions * this) {
	ACSLOptions__ctor_default(&this->acsl);
	this->target = 0;
	this->optimize = 0;
	this->monomorphizeTemplates = 0;
	this->enableExceptions = 0;
	this->exceptionModel = 0;
	this->enableRTTI = 0;
}

static void TranspileOptions__ctor_copy(struct TranspileOptions * this, const struct TranspileOptions * other) {
	ACSLOptions__ctor_copy(&this->acsl, &other->acsl);
	this->target = other->target;
	this->optimize = other->optimize;
	this->monomorphizeTemplates = other->monomorphizeTemplates;
	this->enableExceptions = other->enableExceptions;
	this->exceptionModel = other->exceptionModel;
	this->enableRTTI = other->enableRTTI;
}

static void TranspileResult__ctor_default(struct TranspileResult * this) {
	this->success = 0;
	this->c = 0;
	this->h = 0;
	this->acsl = 0;
	this->diagnostics = 0;
}

static void TranspileResult__ctor_copy(struct TranspileResult * this, const struct TranspileResult * other) {
	this->success = other->success;
	this->c = other->c;
	this->h = other->h;
	this->acsl = other->acsl;
	this->diagnostics = other->diagnostics;
}

static void WASMTranspiler__ctor_default(struct WASMTranspiler * this) {
}

static void WASMTranspiler__ctor_copy(struct WASMTranspiler * this, const struct WASMTranspiler * other) {
}

struct TranspileResult WASMTranspiler_transpile(struct WASMTranspiler * this, const int * cppCode, const struct TranspileOptions * options) {
	struct TranspileResult result;

	try {
        cpptoc::TranspileOptions libOpts;
        libOpts.acsl.statements = options.acsl.statements;
        libOpts.acsl.typeInvariants = options.acsl.typeInvariants;
        libOpts.acsl.axiomatics = options.acsl.axiomatics;
        libOpts.acsl.ghostCode = options.acsl.ghostCode;
        libOpts.acsl.behaviors = options.acsl.behaviors;
        libOpts.acsl.memoryPredicates = options.acsl.memoryPredicates;
        <recovery-expr>(libOpts) = <recovery-expr>(options);
        libOpts.optimize = options.optimize;
        libOpts.monomorphizeTemplates = options.monomorphizeTemplates;
        libOpts.enableExceptions = options.enableExceptions;
        <recovery-expr>(libOpts) = <recovery-expr>(options);
        libOpts.enableRTTI = options.enableRTTI;
        cpptoc::TranspileResult libResult = <recovery-expr>()(<recovery-expr>(), "input.cpp", libOpts);
        result.success = libResult.success;
        <recovery-expr>(result) = <recovery-expr>(libResult);
        <recovery-expr>(result) = <recovery-expr>(libResult);
        <recovery-expr>(result) = <recovery-expr>(libResult);
} catch (const int &e) {
        Diagnostic diag;
        diag.line = 0;
        diag.column = 0;
        <recovery-expr>(diag) = "error";
        <recovery-expr>(result).push_back(diag);
        result.success = false;
}

	return result;
;
}

struct TranspileResult result
struct TranspileOptions libOpts
struct TranspileResult libResult
struct Diagnostic diag
