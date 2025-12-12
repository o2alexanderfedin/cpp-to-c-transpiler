// ActionTableGenerator.cpp - Implementation of action table generation
// Story #77: Implement Action Table Generation from CFG Analysis

#include "ActionTableGenerator.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include <sstream>
#include <algorithm>

namespace clang {

// Helper visitor to find try statements
class TryStatementFinder : public RecursiveASTVisitor<TryStatementFinder> {
public:
    std::vector<CXXTryStmt*> tryStmts;

    bool VisitCXXTryStmt(CXXTryStmt *S) {
        tryStmts.push_back(S);
        return true;
    }
};

// Helper visitor to find variable declarations with constructors
class ConstructedObjectFinder : public RecursiveASTVisitor<ConstructedObjectFinder> {
public:
    std::vector<VarDecl*> constructedObjects;
    int nestedTryDepth = 0;

    bool VisitVarDecl(VarDecl *VD) {
        // Only include variables when not inside a nested try block
        if (nestedTryDepth < 0) {
            // Check if variable has a class type with a destructor
            QualType QT = VD->getType();
            if (const RecordType *RT = QT->getAs<RecordType>()) {
                if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(RT->getDecl())) {
                    // Check if class has a destructor
                    if (RD->hasDefinition() && RD->hasNonTrivialDestructor()) {
                        constructedObjects.push_back(VD);
                    }
                }
            }
        }
        return true;
    }

    bool TraverseCXXTryStmt(CXXTryStmt *S) {
        // Increment depth when entering a nested try block
        nestedTryDepth++;
        bool result = RecursiveASTVisitor::TraverseCXXTryStmt(S);
        nestedTryDepth--;
        return result;
    }
};

void ActionTableGenerator::analyzeTryBlocks(FunctionDecl *FD) {
    if (!FD || !FD->hasBody()) {
        return;
    }

    // Find all try statements in the function
    std::vector<CXXTryStmt*> tryStmts;
    findTryStatements(FD->getBody(), tryStmts);

    // Analyze each try block
    int index = 0;
    for (CXXTryStmt *tryStmt : tryStmts) {
        TryBlockInfo info;
        info.tryStmt = tryStmt;
        info.tryBlockIndex = index++;
        info.constructedObjects = findConstructedObjects(tryStmt);
        tryBlocks.push_back(info);
    }
}

void ActionTableGenerator::findTryStatements(Stmt *S, std::vector<CXXTryStmt*>& tryStmts) {
    if (!S) {
        return;
    }

    TryStatementFinder finder;
    finder.TraverseStmt(S);
    tryStmts = finder.tryStmts;
}

std::vector<VarDecl*> ActionTableGenerator::findConstructedObjects(CXXTryStmt *tryStmt) {
    if (!tryStmt) {
        return {};
    }

    // Get the try block compound statement
    CompoundStmt *tryBlock = dyn_cast<CompoundStmt>(tryStmt->getTryBlock());
    if (!tryBlock) {
        return {};
    }

    // Find all constructed objects in the try block
    // Start at depth -1 so that when we traverse the block, nested try statements start at depth 0
    ConstructedObjectFinder finder;
    finder.nestedTryDepth = -1;
    finder.TraverseStmt(tryBlock);

    return finder.constructedObjects;
}

int ActionTableGenerator::getObjectCount(int tryBlockIndex) const {
    if (tryBlockIndex < 0 || tryBlockIndex >= static_cast<int>(tryBlocks.size())) {
        return 0;
    }
    return tryBlocks[tryBlockIndex].constructedObjects.size();
}

std::vector<std::string> ActionTableGenerator::getDestructorSequence(int tryBlockIndex) const {
    std::vector<std::string> sequence;

    if (tryBlockIndex < 0 || tryBlockIndex >= static_cast<int>(tryBlocks.size())) {
        return sequence;
    }

    const TryBlockInfo& info = tryBlocks[tryBlockIndex];

    // Destructors called in REVERSE construction order
    for (auto it = info.constructedObjects.rbegin();
         it != info.constructedObjects.rend();
         ++it) {
        VarDecl *VD = *it;
        sequence.push_back(getVariableName(VD));
    }

    return sequence;
}

std::string ActionTableGenerator::generateActionTable(int tryBlockIndex) const {
    if (tryBlockIndex < 0 || tryBlockIndex >= static_cast<int>(tryBlocks.size())) {
        return "";
    }

    const TryBlockInfo& info = tryBlocks[tryBlockIndex];
    std::ostringstream oss;

    // Generate action table array
    oss << "static struct __cxx_action_entry actions_try" << tryBlockIndex << "[] = {\n";

    // Add entries in reverse construction order (destruction order)
    for (auto it = info.constructedObjects.rbegin();
         it != info.constructedObjects.rend();
         ++it) {
        VarDecl *VD = *it;
        QualType QT = VD->getType();

        if (const RecordType *RT = QT->getAs<RecordType>()) {
            if (const CXXRecordDecl *RD = dyn_cast<CXXRecordDecl>(RT->getDecl())) {
                std::string destructorName = getDestructorName(RD);
                oss << "    {(void(*)(void*))" << destructorName << ", NULL},\n";
            }
        }
    }

    // Add sentinel entry
    oss << "    {NULL, NULL}\n";
    oss << "};\n";

    return oss.str();
}

std::string ActionTableGenerator::generateRuntimeBinding(int tryBlockIndex) const {
    if (tryBlockIndex < 0 || tryBlockIndex >= static_cast<int>(tryBlocks.size())) {
        return "";
    }

    const TryBlockInfo& info = tryBlocks[tryBlockIndex];
    std::ostringstream oss;

    // Generate runtime binding code
    int entryIndex = 0;
    for (auto it = info.constructedObjects.rbegin();
         it != info.constructedObjects.rend();
         ++it) {
        VarDecl *VD = *it;
        std::string varName = getVariableName(VD);
        oss << "actions_try" << tryBlockIndex << "[" << entryIndex << "].object = &"
            << varName << ";\n";
        entryIndex++;
    }

    return oss.str();
}

std::string ActionTableGenerator::getDestructorName(const CXXRecordDecl *classDecl) const {
    if (!classDecl) {
        return "unknown_dtor";
    }

    // Get class name and generate destructor name
    std::string className = classDecl->getNameAsString();
    return className + "__dtor";
}

std::string ActionTableGenerator::getVariableName(const VarDecl *varDecl) const {
    if (!varDecl) {
        return "unknown";
    }

    return varDecl->getNameAsString();
}

} // namespace clang
