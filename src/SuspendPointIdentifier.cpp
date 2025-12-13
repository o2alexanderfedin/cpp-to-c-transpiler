/**
 * @file SuspendPointIdentifier.cpp
 * @brief Implementation of SuspendPointIdentifier (Story #103)
 */

#include "../include/SuspendPointIdentifier.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/AST/StmtCXX.h"
#include "clang/Basic/SourceManager.h"
#include <sstream>
#include <algorithm>

using namespace clang;

namespace {

/**
 * @brief Visitor to collect all suspend points
 */
class SuspendPointCollector : public RecursiveASTVisitor<SuspendPointCollector> {
public:
    std::vector<const Stmt*> suspendPoints;

    bool VisitCoawaitExpr(CoawaitExpr* E) {
        suspendPoints.push_back(E);
        return true;
    }

    bool VisitCoyieldExpr(CoyieldExpr* E) {
        suspendPoints.push_back(E);
        return true;
    }

    bool VisitCoreturnStmt(CoreturnStmt* S) {
        suspendPoints.push_back(S);
        return true;
    }
};

} // anonymous namespace

SuspendPointIdentifier::SuspendPointIdentifier(ASTContext& Context)
    : Context(Context) {}

std::vector<SuspendPoint> SuspendPointIdentifier::identifySuspendPoints(const FunctionDecl* FD) {
    if (!FD || !FD->hasBody()) {
        return {};
    }

    // Collect all suspend point statements
    SuspendPointCollector collector;
    collector.TraverseStmt(FD->getBody());

    // Convert to SuspendPoint structs with metadata
    std::vector<SuspendPoint> result;
    unsigned int stateId = 1; // State 0 is reserved for initial state

    for (const auto* stmt : collector.suspendPoints) {
        SuspendPoint sp;
        sp.stmt = stmt;
        sp.kind = classifySuspendPoint(stmt);
        getLocation(stmt, sp.line, sp.column);
        sp.stateId = stateId++;
        result.push_back(sp);
    }

    // Sort by source location (line, then column)
    std::sort(result.begin(), result.end(), [](const SuspendPoint& a, const SuspendPoint& b) {
        if (a.line != b.line) {
            return a.line < b.line;
        }
        return a.column < b.column;
    });

    // Renumber state IDs after sorting
    stateId = 1;
    for (auto& sp : result) {
        sp.stateId = stateId++;
    }

    return result;
}

std::string SuspendPointIdentifier::generateStateLabels(const FunctionDecl* FD) {
    if (!FD) {
        return "";
    }

    auto suspendPoints = identifySuspendPoints(FD);
    if (suspendPoints.empty()) {
        return "";
    }

    std::ostringstream code;
    std::string funcName = FD->getNameAsString();

    code << "// State labels for " << funcName << " suspend points\n";
    code << "enum " << funcName << "_state {\n";
    code << "    " << funcName << "_STATE_INITIAL = 0";

    for (const auto& sp : suspendPoints) {
        code << ",\n    " << funcName << "_STATE_SUSPEND_" << sp.stateId;
    }

    code << "\n};\n";

    return code.str();
}

size_t SuspendPointIdentifier::getSuspendPointCount(const FunctionDecl* FD) {
    return identifySuspendPoints(FD).size();
}

std::string SuspendPointIdentifier::classifySuspendPoint(const Stmt* S) {
    if (!S) {
        return "";
    }

    if (isa<CoawaitExpr>(S)) {
        return "co_await";
    } else if (isa<CoyieldExpr>(S)) {
        return "co_yield";
    } else if (isa<CoreturnStmt>(S)) {
        return "co_return";
    }

    return "";
}

void SuspendPointIdentifier::getLocation(const Stmt* S, unsigned int& line, unsigned int& column) {
    if (!S) {
        line = 0;
        column = 0;
        return;
    }

    SourceLocation loc = S->getBeginLoc();
    if (loc.isInvalid()) {
        line = 0;
        column = 0;
        return;
    }

    SourceManager& SM = Context.getSourceManager();
    PresumedLoc presumedLoc = SM.getPresumedLoc(loc);

    if (presumedLoc.isValid()) {
        line = presumedLoc.getLine();
        column = presumedLoc.getColumn();
    } else {
        line = 0;
        column = 0;
    }
}
