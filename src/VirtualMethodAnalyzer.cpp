/**
 * @file VirtualMethodAnalyzer.cpp
 * @brief Implementation of VirtualMethodAnalyzer
 */

#include "../include/VirtualMethodAnalyzer.h"
#include "clang/AST/DeclCXX.h"
#include "llvm/Config/llvm-config.h" // For LLVM_VERSION_MAJOR
#include <functional>
#include <map>
#include <set>
#include <string>

using namespace clang;

VirtualMethodAnalyzer::VirtualMethodAnalyzer(ASTContext &Context)
    : Context(Context) {}

bool VirtualMethodAnalyzer::isPolymorphic(const CXXRecordDecl *Record) const {
  if (!Record) {
    return false;
  }

  // Clang's built-in polymorphic check
  return Record->isPolymorphic();
}

std::vector<CXXMethodDecl *>
VirtualMethodAnalyzer::getVirtualMethods(const CXXRecordDecl *Record) const {
  std::vector<CXXMethodDecl *> virtualMethods;

  if (!Record || !Record->isCompleteDefinition()) {
    return virtualMethods;
  }

  // Use a map to track the most derived version of each virtual method
  // Key: method name + signature, Value: method declaration
  std::map<std::string, CXXMethodDecl *> virtualMethodMap;

  // Helper to generate a unique key for a method (name + parameter types)
  auto getMethodKey = [](const CXXMethodDecl *Method) -> std::string {
    std::string key = Method->getNameAsString();
    key += "(";
    for (unsigned i = 0; i < Method->getNumParams(); ++i) {
      if (i > 0)
        key += ",";
      key += Method->parameters()[i]->getType().getAsString();
    }
    key += ")";
    return key;
  };

  // Helper to recursively collect virtual methods from base classes
  std::set<const CXXRecordDecl *> visited;
  std::function<void(const CXXRecordDecl *)> collectFromBases =
      [&](const CXXRecordDecl *R) {
        if (!R || !R->isCompleteDefinition() || visited.count(R)) {
          return;
        }
        visited.insert(R);

        // First recurse to base classes
        for (const auto &Base : R->bases()) {
          const CXXRecordDecl *BaseRecord =
              Base.getType()->getAsCXXRecordDecl();
          if (BaseRecord) {
            collectFromBases(BaseRecord);
          }
        }

        // Then add virtual methods from this level
        // (derived class methods override base class methods with same
        // signature)
        for (auto *Method : R->methods()) {
          if (Method->isVirtual()) {
            std::string key = getMethodKey(Method);
            virtualMethodMap[key] = Method; // Overwrite if exists
          }
        }
      };

  // Start collection from the given record
  collectFromBases(Record);

  // Convert map to vector
  for (const auto &pair : virtualMethodMap) {
    virtualMethods.push_back(pair.second);
  }

  return virtualMethods;
}

bool VirtualMethodAnalyzer::isPureVirtual(const CXXMethodDecl *Method) const {
  if (!Method) {
    return false;
  }

  // Check if method is pure virtual (= 0)
#if LLVM_VERSION_MAJOR >= 16
  return Method->isPureVirtual();
#else
  // LLVM 15 uses isPure() instead of isPureVirtual()
  return Method->isPure();
#endif
}

bool VirtualMethodAnalyzer::isAbstractClass(const CXXRecordDecl *Record) const {
  if (!Record) {
    return false;
  }

  // Clang's built-in abstract class check
  // A class is abstract if it has at least one pure virtual method
  return Record->isAbstract();
}
