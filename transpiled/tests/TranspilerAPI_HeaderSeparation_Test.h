// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/TranspilerAPI_HeaderSeparation_Test.cpp
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
struct TranspilerAPI_HeaderSeparation {
	struct TranspileOptions options;
};
static void TranspilerAPI_HeaderSeparation__ctor_default(struct TranspilerAPI_HeaderSeparation * this);
static void TranspilerAPI_HeaderSeparation__ctor_copy(struct TranspilerAPI_HeaderSeparation * this, const struct TranspilerAPI_HeaderSeparation * other);
void TranspilerAPI_HeaderSeparation_SetUp(struct TranspilerAPI_HeaderSeparation * this);
int TEST_F(struct TranspilerAPI_HeaderSeparation, int);
int TEST_F_TranspilerAPI_HeaderSeparation_int(struct TranspilerAPI_HeaderSeparation, int);
int TEST_F_TranspilerAPI_HeaderSeparation_int_1(struct TranspilerAPI_HeaderSeparation, int);
int TEST_F_TranspilerAPI_HeaderSeparation_int_2(struct TranspilerAPI_HeaderSeparation, int);
int TEST_F_TranspilerAPI_HeaderSeparation_int_3(struct TranspilerAPI_HeaderSeparation, int);
int TEST_F_TranspilerAPI_HeaderSeparation_int_4(struct TranspilerAPI_HeaderSeparation, int);
int TEST_F_TranspilerAPI_HeaderSeparation_int_5(struct TranspilerAPI_HeaderSeparation, int);
int TEST_F_TranspilerAPI_HeaderSeparation_int_6(struct TranspilerAPI_HeaderSeparation, int);
