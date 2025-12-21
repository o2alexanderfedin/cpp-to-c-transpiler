/**
 * @file VirtualTableTestBase.h
 * @brief Shared test fixtures for virtual table and inheritance tests
 *
 * Provides common helpers and fixtures for testing virtual table generation,
 * virtual method analysis, and C++ polymorphism features.
 */

#ifndef VIRTUAL_TABLE_TEST_BASE_H
#define VIRTUAL_TABLE_TEST_BASE_H

#include <gtest/gtest.h>
#include "clang/Tooling/Tooling.h"
#include "clang/Frontend/ASTUnit.h"
#include <memory>
#include <string>
#include <vector>

using namespace clang;

/**
 * @brief Base test fixture for all virtual table related tests
 *
 * Provides common functionality for building AST from C++ code snippets,
 * finding classes by name, and other common test operations.
 */
class VirtualTableTestBase : public ::testing::Test {
protected:
    /**
     * @brief Build AST from C++ code string
     * @param code C++ code to parse
     * @return Unique pointer to parsed AST unit
     */
    std::unique_ptr<ASTUnit> buildAST(const char *code) {
        std::vector<std::string> args = {"-std=c++17"};
        return tooling::buildASTFromCodeWithArgs(code, args, "input.cc");
    }

    /**
     * @brief Find a C++ class declaration by name in the translation unit
     * @param TU Translation unit to search
     * @param name Class name to find
     * @return Pointer to the class declaration, or nullptr if not found
     */
    CXXRecordDecl* findClass(TranslationUnitDecl* TU, const std::string& name) {
        for (auto *D : TU->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->getNameAsString() == name && RD->isCompleteDefinition()) {
                    return RD;
                }
            }
        }
        return nullptr;
    }

    /**
     * @brief Find all classes in the translation unit
     * @param TU Translation unit to search
     * @return Vector of all class declarations
     */
    std::vector<CXXRecordDecl*> findAllClasses(TranslationUnitDecl* TU) {
        std::vector<CXXRecordDecl*> classes;
        for (auto *D : TU->decls()) {
            if (auto *RD = dyn_cast<CXXRecordDecl>(D)) {
                if (RD->isCompleteDefinition()) {
                    classes.push_back(RD);
                }
            }
        }
        return classes;
    }

    /**
     * @brief Find a method by name in a class
     * @param RD Class declaration to search
     * @param methodName Method name to find
     * @return Pointer to the method declaration, or nullptr if not found
     */
    CXXMethodDecl* findMethod(CXXRecordDecl* RD, const std::string& methodName) {
        for (auto* method : RD->methods()) {
            if (method->getNameAsString() == methodName) {
                return method;
            }
        }
        return nullptr;
    }

    /**
     * @brief Count virtual methods in a class (excluding destructors)
     * @param RD Class declaration
     * @return Number of virtual methods
     */
    size_t countVirtualMethods(CXXRecordDecl* RD) {
        size_t count = 0;
        for (auto* method : RD->methods()) {
            if (method->isVirtual() && !isa<CXXDestructorDecl>(method)) {
                count++;
            }
        }
        return count;
    }

    /**
     * @brief Check if a class has virtual methods
     * @param RD Class declaration
     * @return True if the class is polymorphic
     */
    bool isPolymorphic(CXXRecordDecl* RD) {
        return RD->isPolymorphic();
    }
};

/**
 * @brief Test fixture for virtual inheritance tests
 *
 * Extends VirtualTableTestBase with helpers specific to virtual inheritance
 * and diamond hierarchy patterns.
 */
class VirtualInheritanceTestBase : public VirtualTableTestBase {
protected:
    /**
     * @brief Check if a class has virtual bases
     * @param RD Class declaration
     * @return True if the class has virtual base classes
     */
    bool hasVirtualBases(CXXRecordDecl* RD) {
        return RD->getNumVBases() > 0;
    }

    /**
     * @brief Count direct virtual base classes
     * @param RD Class declaration
     * @return Number of virtual base classes
     */
    size_t countVirtualBases(CXXRecordDecl* RD) {
        return RD->getNumVBases();
    }

    /**
     * @brief Count direct non-virtual base classes
     * @param RD Class declaration
     * @return Number of non-virtual base classes
     */
    size_t countNonVirtualBases(CXXRecordDecl* RD) {
        return RD->getNumBases() - RD->getNumVBases();
    }
};

#endif // VIRTUAL_TABLE_TEST_BASE_H
