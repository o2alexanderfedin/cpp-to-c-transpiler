/**
 * @file DestructorHandler.cpp
 * @brief Implementation of DestructorHandler dispatcher pattern
 *
 * Integrates with CppToCVisitorDispatcher to handle destructor translation.
 * Translates C++ destructors to C cleanup functions with explicit this parameter.
 * Retrieves translated function bodies from StmtMapper via CompoundStmtHandler.
 */

#include "dispatch/DestructorHandler.h"
#include "CNodeBuilder.h"
#include "NameMangler.h"
#include "SourceLocationMapper.h"
#include "mapping/DeclMapper.h"
#include "mapping/StmtMapper.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Support/Casting.h"
#include "llvm/Support/raw_ostream.h"
#include <cassert>

namespace cpptoc {

void DestructorHandler::registerWith(CppToCVisitorDispatcher& dispatcher) {
    dispatcher.addHandler(
        &DestructorHandler::canHandle,
        &DestructorHandler::handleDestructor
    );
}

bool DestructorHandler::canHandle(const clang::Decl* D) {
    assert(D && "Declaration must not be null");

    // Check if this is a CXXDestructorDecl
    return llvm::isa<clang::CXXDestructorDecl>(D);
}

void DestructorHandler::handleDestructor(
    const CppToCVisitorDispatcher& disp,
    const clang::ASTContext& cppASTContext,
    clang::ASTContext& cASTContext,
    const clang::Decl* D
) {
    assert(D && "Declaration must not be null");
    assert(llvm::isa<clang::CXXDestructorDecl>(D) && "Must be CXXDestructorDecl");

    const auto* cppDestructor = llvm::cast<clang::CXXDestructorDecl>(D);

    // Check if already translated
    cpptoc::DeclMapper& declMapper = disp.getDeclMapper();
    if (declMapper.hasCreated(cppDestructor)) {
        llvm::outs() << "[DestructorHandler] Already translated: "
                     << cppDestructor->getQualifiedNameAsString() << "\n";
        return;
    }

    // Get parent class
    const auto* cxxRecord = cppDestructor->getParent();
    if (!cxxRecord) {
        llvm::errs() << "[DestructorHandler] Error: Destructor has no parent class\n";
        return;
    }

    std::string className = cxxRecord->getNameAsString();

    // Generate function name using NameMangler
    std::string functionName = cpptoc::mangle_destructor(cppDestructor);

    // Find the C RecordDecl (created by RecordHandler)
    clang::RecordDecl* cRecordDecl = nullptr;
    auto* cTU = cASTContext.getTranslationUnitDecl();
    for (auto* decl : cTU->decls()) {
        if (auto* RD = llvm::dyn_cast<clang::RecordDecl>(decl)) {
            if (RD->getName() == className) {
                cRecordDecl = RD;
                break;
            }
        }
    }

    if (!cRecordDecl) {
        llvm::errs() << "[DestructorHandler] Error: C RecordDecl not found for class: "
                     << className << "\n";
        llvm::errs() << "[DestructorHandler] RecordHandler should have created the struct first\n";
        return;
    }

    // Create this parameter: struct ClassName* this
    clang::QualType classType = cASTContext.getRecordType(cRecordDecl);
    clang::ParmVarDecl* thisParam = createThisParameter(classType, cASTContext);

    // Create parameters vector with just this parameter
    std::vector<clang::ParmVarDecl*> params = { thisParam };

    // Translate destructor body (if exists) via CompoundStmtHandler
    clang::CompoundStmt* cBody = nullptr;
    if (cppDestructor->hasBody()) {
        const clang::Stmt* cppBody = cppDestructor->getBody();
        if (cppBody) {
            // Dispatch body to CompoundStmtHandler
            bool bodyHandled = disp.dispatch(cppASTContext, cASTContext, const_cast<clang::Stmt*>(cppBody));
            if (bodyHandled) {
                // Retrieve created C body from StmtMapper
                cpptoc::StmtMapper& stmtMapper = disp.getStmtMapper();
                clang::Stmt* cStmt = stmtMapper.getCreated(cppBody);

                if (cStmt) {
                    // Ensure it's a CompoundStmt as expected for function bodies
                    cBody = llvm::dyn_cast<clang::CompoundStmt>(cStmt);
                    if (cBody) {
                        llvm::outs() << "[DestructorHandler] Body dispatched and retrieved successfully "
                                     << "(" << cBody->size() << " statements)\n";
                    } else {
                        llvm::errs() << "[DestructorHandler] Error: Retrieved statement is not CompoundStmt for destructor: "
                                     << functionName << "\n";
                    }
                } else {
                    llvm::errs() << "[DestructorHandler] Warning: CompoundStmtHandler did not create C body for destructor: "
                                 << functionName << "\n";
                }
            }
        }
    }

    // Create C function using CNodeBuilder
    clang::CNodeBuilder builder(cASTContext);
    clang::FunctionDecl* cFunc = builder.funcDecl(
        functionName,
        cASTContext.VoidTy,  // Destructors always return void
        params,
        cBody  // Body is nullptr if not translated, or CompoundStmt if successfully translated
    );

    assert(cFunc && "Failed to create C FunctionDecl for destructor");

    // Verify body was properly attached
    if (cBody) {
        assert(cFunc->hasBody() && "Destructor function should have body after creation");
        assert(cFunc->getBody() == cBody && "Destructor body should match provided body");
        llvm::outs() << "[DestructorHandler] Destructor body successfully attached to: "
                     << functionName << "\n";
    }

    // Store in DeclMapper
    declMapper.setCreated(cppDestructor, cFunc);

    // Get target path for this C++ source file
    std::string targetPath = disp.getCurrentTargetPath();  // Use current path set by TranslationUnitHandler
    if (targetPath.empty()) {
        targetPath = disp.getTargetPath(cppASTContext, D);
    }

    // Get or create C TranslationUnit for this target file
    cpptoc::PathMapper& pathMapper = disp.getPathMapper();
    clang::TranslationUnitDecl* cTargetTU = pathMapper.getOrCreateTU(targetPath);
    assert(cTargetTU && "Failed to get/create C TranslationUnit");

    // Add C function to C TranslationUnit
    cFunc->setDeclContext(cTargetTU);
    cTargetTU->addDecl(cFunc);

    // Register node location in PathMapper for tracking
    pathMapper.setNodeLocation(cFunc, targetPath);

    // Debug output for verification
    llvm::outs() << "[DestructorHandler] Translated destructor: "
                 << cppDestructor->getQualifiedNameAsString()
                 << " → " << functionName
                 << " → " << targetPath << "\n";
}

clang::ParmVarDecl* DestructorHandler::createThisParameter(
    clang::QualType recordType,
    clang::ASTContext& cASTContext
) {
    // Create pointer type: struct ClassName*
    clang::QualType thisType = cASTContext.getPointerType(recordType);

    // Create identifier for parameter name
    clang::IdentifierInfo& II = cASTContext.Idents.get("this");

    // Create parameter declaration
    clang::ParmVarDecl* thisParam = clang::ParmVarDecl::Create(
        cASTContext,
        cASTContext.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &II,
        thisType,
        cASTContext.getTrivialTypeSourceInfo(thisType),
        clang::SC_None,
        nullptr  // No default argument
    );

    return thisParam;
}

} // namespace cpptoc
