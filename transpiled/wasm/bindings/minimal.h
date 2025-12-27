// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./wasm/bindings/minimal.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct TranspileOptions {
	struct ACSLConfig acsl;
	ACSLLevelEnum acslLevel;
	ACSLOutputModeEnum acslOutputMode;
	int target;
	int cppStandard;
	bool optimize;
	bool monomorphizeTemplates;
	unsigned int templateInstantiationLimit;
	bool enableExceptions;
	int exceptionModel;
	bool enableRTTI;
	bool usePragmaOnce;
	bool generateDependencyGraph;
};
static void TranspileOptions__ctor_default(struct TranspileOptions * this);
static void TranspileOptions__ctor_copy(struct TranspileOptions * this, const struct TranspileOptions * other);
struct ACSLConfig {
	bool statements;
	bool typeInvariants;
	bool axiomatics;
	bool ghostCode;
	bool behaviors;
	bool memoryPredicates;
};
static void ACSLConfig__ctor_default(struct ACSLConfig * this);
static void ACSLConfig__ctor_copy(struct ACSLConfig * this, const struct ACSLConfig * other);
typedef enum {
    Basic = 0,
    Full = 1
} ACSLLevelEnum;
typedef enum {
    Inline = 0,
    Separate = 1
} ACSLOutputModeEnum;
struct Diagnostic {
	int line;
	int column;
	int message;
	int severity;
};
static void Diagnostic__ctor_default(struct Diagnostic * this);
static void Diagnostic__ctor_copy(struct Diagnostic * this, const struct Diagnostic * other);
struct TranspileResult {
	bool success;
	int c;
	int h;
	int acsl;
	int dependencyGraph;
	int diagnostics;
};
static void TranspileResult__ctor_default(struct TranspileResult * this);
static void TranspileResult__ctor_copy(struct TranspileResult * this, const struct TranspileResult * other);
struct Diagnostic {
	int line;
	int column;
	int message;
	int severity;
};
static void Diagnostic__ctor_default(struct Diagnostic * this);
static void Diagnostic__ctor_copy(struct Diagnostic * this, const struct Diagnostic * other);
struct ACSLOptions {
	bool statements;
	bool typeInvariants;
	bool axiomatics;
	bool ghostCode;
	bool behaviors;
	bool memoryPredicates;
};
static void ACSLOptions__ctor_default(struct ACSLOptions * this);
static void ACSLOptions__ctor_copy(struct ACSLOptions * this, const struct ACSLOptions * other);
struct TranspileOptions {
	struct ACSLOptions acsl;
	int target;
	bool optimize;
	bool monomorphizeTemplates;
	bool enableExceptions;
	int exceptionModel;
	bool enableRTTI;
};
static void TranspileOptions__ctor_default(struct TranspileOptions * this);
static void TranspileOptions__ctor_copy(struct TranspileOptions * this, const struct TranspileOptions * other);
struct TranspileResult {
	bool success;
	int c;
	int h;
	int acsl;
	int diagnostics;
};
static void TranspileResult__ctor_default(struct TranspileResult * this);
static void TranspileResult__ctor_copy(struct TranspileResult * this, const struct TranspileResult * other);
struct WASMTranspiler {
};
static void WASMTranspiler__ctor_default(struct WASMTranspiler * this);
static void WASMTranspiler__ctor_copy(struct WASMTranspiler * this, const struct WASMTranspiler * other);
struct TranspileResult WASMTranspiler_transpile(struct WASMTranspiler * this, const int * cppCode, const struct TranspileOptions * options);
struct TranspileResult result
struct TranspileOptions libOpts
struct TranspileResult libResult
struct Diagnostic diag
