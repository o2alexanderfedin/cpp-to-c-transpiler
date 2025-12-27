// Generated from: /Users/alexanderfedin/Projects/hapyy/hupyy-cpp-to-c/./tests/CFGAnalysisTest.cpp
// Header file

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <stdbool.h>

struct CFGAnalyzer {
	int cfg;
	int exitPoints;
	int localVars;
	int scopes;
	int breakContinueStmts;
	int gotoStmts;
};
static void CFGAnalyzer__ctor_copy(struct CFGAnalyzer * this, const struct CFGAnalyzer * other);
int CFGAnalyzer_getExitPointCount(struct CFGAnalyzer * this);
int CFGAnalyzer_getLocalVarCount(struct CFGAnalyzer * this);
int CFGAnalyzer_getScopeCount(struct CFGAnalyzer * this);
int CFGAnalyzer_getBreakContinueCount(struct CFGAnalyzer * this);
int CFGAnalyzer_getGotoCount(struct CFGAnalyzer * this);
const int * CFGAnalyzer_getExitPoints(struct CFGAnalyzer * this);
const int * CFGAnalyzer_getLocalVars(struct CFGAnalyzer * this);
const int * CFGAnalyzer_getScopes(struct CFGAnalyzer * this);
int * CFGAnalyzer_getCFG(struct CFGAnalyzer * this);
void test_CFGDetectsAllReturns();
void test_CFGTracksLocalVars();
void test_CFGIdentifiesNestedScopes();
void test_CFGDetectsBreakContinue();
void test_CFGDetectsGoto();
int main();
