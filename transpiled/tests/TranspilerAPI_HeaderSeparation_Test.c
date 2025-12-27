// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/TranspilerAPI_HeaderSeparation_Test.cpp
// Implementation file

#include "TranspilerAPI_HeaderSeparation_Test.h"

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

static void TranspilerAPI_HeaderSeparation__ctor_default(struct TranspilerAPI_HeaderSeparation * this) {
	TranspileOptions__ctor_default(&this->options);
}

static void TranspilerAPI_HeaderSeparation__ctor_copy(struct TranspilerAPI_HeaderSeparation * this, const struct TranspilerAPI_HeaderSeparation * other) {
	TranspileOptions__ctor_copy(&this->options, &other->options);
}

void TranspilerAPI_HeaderSeparation_SetUp(struct TranspilerAPI_HeaderSeparation * this) {
}

int TEST_F(struct TranspilerAPI_HeaderSeparation, int) {
	int cpp;

	auto result;

}

int TEST_F_TranspilerAPI_HeaderSeparation_int(struct TranspilerAPI_HeaderSeparation, int) {
	int cpp;

	auto result;

}

int TEST_F_TranspilerAPI_HeaderSeparation_int_1(struct TranspilerAPI_HeaderSeparation, int) {
	int cpp;

	auto result;

}

int TEST_F_TranspilerAPI_HeaderSeparation_int_2(struct TranspilerAPI_HeaderSeparation, int) {
	struct TranspileOptions opts;

	opts.usePragmaOnce = true;
	int cpp;

	auto result;

}

int TEST_F_TranspilerAPI_HeaderSeparation_int_3(struct TranspilerAPI_HeaderSeparation, int) {
	int cpp;

	auto result;

}

int TEST_F_TranspilerAPI_HeaderSeparation_int_4(struct TranspilerAPI_HeaderSeparation, int) {
	int cpp;

	auto result;

}

int TEST_F_TranspilerAPI_HeaderSeparation_int_5(struct TranspilerAPI_HeaderSeparation, int) {
	int cpp;

	auto result;

}

int TEST_F_TranspilerAPI_HeaderSeparation_int_6(struct TranspilerAPI_HeaderSeparation, int) {
	int cpp;

	auto result;

}

