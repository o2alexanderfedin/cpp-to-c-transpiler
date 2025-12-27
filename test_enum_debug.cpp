#include "clang/AST/Decl.h"
#include "clang/Tooling/Tooling.h"
#include <iostream>

int main() {
    // Create a minimal AST
    auto AST = clang::tooling::buildASTFromCode("int dummy;");
    if (!AST) {
        std::cerr << "Failed to create AST\n";
        return 1;
    }
    
    auto& Ctx = AST->getASTContext();
    
    // Create an enum
    clang::IdentifierInfo& enumII = Ctx.Idents.get("TestEnum");
    clang::EnumDecl* enumDecl = clang::EnumDecl::Create(
        Ctx,
        Ctx.getTranslationUnitDecl(),
        clang::SourceLocation(),
        clang::SourceLocation(),
        &enumII,
        nullptr,
        false,
        false,
        true
    );
    
    enumDecl->startDefinition();
    
    // Try creating enum constant with nullptr parent
    clang::IdentifierInfo& constII = Ctx.Idents.get("Value");
    llvm::APSInt value(32, false);
    value = 42;
    
    std::cout << "Creating EnumConstantDecl with nullptr parent...\n";
    clang::EnumConstantDecl* constDecl = clang::EnumConstantDecl::Create(
        Ctx,
        nullptr,  // This might be the problem
        clang::SourceLocation(),
        &constII,
        Ctx.IntTy,
        nullptr,
        value
    );
    
    std::cout << "Successfully created EnumConstantDecl\n";
    
    std::cout << "Adding to enum...\n";
    enumDecl->addDecl(constDecl);
    std::cout << "Successfully added to enum\n";
    
    std::cout << "Completing definition...\n";
    enumDecl->completeDefinition(Ctx.IntTy, Ctx.IntTy, 0, 0);
    std::cout << "Successfully completed definition\n";
    
    std::cout << "Iterating enumerators...\n";
    for (auto* ecd : enumDecl->enumerators()) {
        std::cout << "Found: " << ecd->getNameAsString() << "\n";
    }
    
    return 0;
}
