#include "CppToCVisitor.h"
#include "handlers/HandlerContext.h"
#include "CFGAnalyzer.h"
#include "MethodSignatureHelper.h"
#include "TargetContext.h"
#include "clang/AST/Attr.h"
#include "clang/AST/Expr.h"
#include "clang/AST/ExprCXX.h"
#include "clang/Basic/SourceManager.h"
#include "llvm/Support/raw_ostream.h"
#include <algorithm>
#include <sstream>
#include <vector>

using namespace clang;

// Forward declarations of CLI accessor functions from main.cpp
extern bool shouldGenerateACSL();
extern ACSLLevel getACSLLevel();
extern ACSLOutputMode getACSLOutputMode();
extern bool shouldGenerateMemoryPredicates();        // Phase 6 (v1.23.0)
extern bool shouldMonomorphizeTemplates();           // Phase 11 (v2.4.0)
extern unsigned int getTemplateInstantiationLimit(); // Phase 11 (v2.4.0)
extern bool shouldEnableExceptions();                // Phase 12 (v2.5.0)
extern std::string getExceptionModel();              // Phase 12 (v2.5.0)
extern bool shouldEnableRTTI();                      // Phase 13 (v2.6.0)

// Epic #193: ACSL Integration - Constructor Implementation
CppToCVisitor::CppToCVisitor(ASTContext &Context, CNodeBuilder &Builder,
                             TargetContext &targetCtx_param,
                             cpptoc::FileOriginTracker &tracker,
                             TranslationUnitDecl *C_TU_param,
                             const std::string& currentFile)
    : Context(Context), Builder(Builder), targetCtx(targetCtx_param), Mangler(Context),
      fileOriginTracker(tracker),
      VirtualAnalyzer(Context), VptrInjectorInstance(Context, VirtualAnalyzer),
      MoveCtorTranslator(Context), MoveAssignTranslator(Context),
      RvalueRefParamTrans(Context), C_TranslationUnit(C_TU_param) {

  // Initialize FileOriginFilter for proper file-based filtering
  if (!currentFile.empty()) {
    fileOriginFilter = std::make_unique<cpptoc::FileOriginFilter>(tracker, currentFile);
    llvm::outs() << "FileOriginFilter initialized for: " << currentFile << "\n";
  }

  // Initialize ACSL annotators if --generate-acsl flag is enabled
  if (shouldGenerateACSL()) {
    ACSLLevel level = getACSLLevel();
    ACSLOutputMode mode = getACSLOutputMode();

    llvm::outs() << "Initializing ACSL annotators (level: "
                 << (level == ACSLLevel::Basic ? "basic" : "full") << ", mode: "
                 << (mode == ACSLOutputMode::Inline ? "inline" : "separate")
                 << ")\n";

    // Initialize all 8 ACSL annotator classes
    m_functionAnnotator = std::make_unique<ACSLFunctionAnnotator>(level, mode);
    m_loopAnnotator = std::make_unique<ACSLLoopAnnotator>(level, mode);
    m_classAnnotator = std::make_unique<ACSLClassAnnotator>(level, mode);
    m_statementAnnotator =
        std::make_unique<ACSLStatementAnnotator>(level, mode);
    m_typeInvariantGen =
        std::make_unique<ACSLTypeInvariantGenerator>(level, mode);
    m_axiomaticBuilder = std::make_unique<ACSLAxiomaticBuilder>(level, mode);
    m_ghostInjector = std::make_unique<ACSLGhostCodeInjector>(level, mode);
    // Note: ACSLBehaviorAnnotator only accepts level parameter (no mode
    // parameter)
    m_behaviorAnnotator = std::make_unique<ACSLBehaviorAnnotator>(level);

    // Phase 6 (v1.23.0): Configure memory predicates if enabled
    if (shouldGenerateMemoryPredicates()) {
      m_functionAnnotator->setMemoryPredicatesEnabled(true);
      llvm::outs() << "Memory predicates enabled (allocable, freeable, "
                      "block_length, base_addr)\n";
    }
  }

  // Phase 9 (v2.2.0): Initialize virtual method infrastructure
  m_overrideResolver =
      std::make_unique<OverrideResolver>(Context, VirtualAnalyzer);
  m_vtableGenerator = std::make_unique<VtableGenerator>(
      Context, VirtualAnalyzer, m_overrideResolver.get());
  m_vtableInitializer =
      std::make_unique<VtableInitializer>(Context, VirtualAnalyzer);
  m_virtualCallTrans =
      std::make_unique<VirtualCallTranslator>(Context, VirtualAnalyzer);
  llvm::outs() << "Virtual method support initialized\n";

  // Phase 11 (v2.4.0): Initialize template monomorphization infrastructure
  // Note: Always initialize these, but only use them if
  // shouldMonomorphizeTemplates() is true
  // Bug #17: Pass FileOriginTracker to skip system header templates
  m_templateExtractor = std::make_unique<TemplateExtractor>(Context, &tracker);
  m_templateMonomorphizer =
      std::make_unique<TemplateMonomorphizer>(Context, Mangler, Builder);
  m_templateTracker = std::make_unique<TemplateInstantiationTracker>();

  if (shouldMonomorphizeTemplates()) {
    llvm::outs() << "Template monomorphization enabled (limit: "
                 << getTemplateInstantiationLimit() << " instantiations)\n";
  }

  // Phase 12 (v2.5.0): Initialize exception handling infrastructure
  m_exceptionFrameGen = std::make_shared<ExceptionFrameGenerator>();
  m_tryCatchTransformer =
      std::make_unique<clang::TryCatchTransformer>(m_exceptionFrameGen);
  m_throwTranslator = std::make_unique<clang::ThrowTranslator>();
  llvm::outs() << "Exception handling support initialized (SJLJ model)\n";

  // Phase 13 (v2.6.0): Initialize RTTI infrastructure
  m_typeidTranslator =
      std::make_unique<TypeidTranslator>(Context, VirtualAnalyzer);
  m_dynamicCastTranslator =
      std::make_unique<DynamicCastTranslator>(Context, VirtualAnalyzer);
  llvm::outs() << "RTTI support initialized (typeid and dynamic_cast)\n";

  // Phase 1: Initialize multidimensional subscript operator translator (C++23)
  m_multidimSubscriptTrans = std::make_unique<MultidimSubscriptTranslator>(Builder);
  llvm::outs() << "Multidimensional subscript operator support initialized (C++23)\n";

  // Phase 2: Initialize static operator translator (C++23)
  m_staticOperatorTrans = std::make_unique<StaticOperatorTranslator>(Builder);
  llvm::outs() << "Static operator() and operator[] support initialized (C++23)\n";

  // Phase 3: Initialize assume attribute handler (C++23)
  m_assumeHandler = std::make_unique<AssumeAttributeHandler>(Builder, AssumeStrategy::Comment);
  llvm::outs() << "[[assume]] attribute support initialized (C++23)\n";

  // Phase 4: Initialize deducing this translator (C++23 P0847R7)
  m_deducingThisTrans = std::make_unique<DeducingThisTranslator>(Builder);
  llvm::outs() << "Deducing this / explicit object parameter support initialized (C++23 P0847R7)\n";

  // Phase 5: Initialize if consteval translator (C++23 P1938R3)
  m_constevalIfTrans = std::make_unique<clang::ConstevalIfTranslator>(Builder, clang::ConstevalStrategy::Runtime);
  llvm::outs() << "if consteval support initialized (C++23 P1938R3) - Runtime strategy\n";

  // Phase 6: Initialize auto(x) decay-copy and constexpr handlers (C++23 P0849R8)
  m_autoDecayTrans = std::make_unique<AutoDecayCopyTranslator>(Builder);
  m_constexprHandler = std::make_unique<ConstexprEnhancementHandler>(Builder);
  llvm::outs() << "auto(x) decay-copy and partial constexpr support initialized (C++23 P0849R8)\n";

  // Phase 47: Initialize scoped enum translator
  m_enumTranslator = std::make_unique<cpptoc::EnumTranslator>();
  llvm::outs() << "Scoped enum translation support initialized (Phase 47)\n";

  // Phase 50: Initialize arithmetic operator translator
  m_arithmeticOpTrans = std::make_unique<ArithmeticOperatorTranslator>(Builder, Mangler);
  llvm::outs() << "Arithmetic operator overloading support initialized (Phase 50)\n";

  // Phase 51: Initialize comparison & logical operator translator
  m_comparisonOpTrans = std::make_unique<ComparisonOperatorTranslator>(Builder, Mangler);
  llvm::outs() << "Comparison & logical operator overloading support initialized (Phase 51)\n";

  // Phase 52: Initialize special operator translator
  m_specialOpTrans = std::make_unique<SpecialOperatorTranslator>(Builder, Mangler);
  llvm::outs() << "Special operator overloading support initialized (Phase 52)\n";

  // Phase 53: Initialize type alias analyzer and typedef generator
  m_typeAliasAnalyzer = std::make_unique<cpptoc::TypeAliasAnalyzer>(Context, Builder);
  m_typedefGenerator = std::make_unique<cpptoc::TypedefGenerator>(Builder.getContext(), Builder);
  llvm::outs() << "Type alias and typedef support initialized (Phase 53)\n";

  // Phase 35-02 (Bug #30 FIX): C_TranslationUnit passed as constructor parameter
  // Each source file has its own C_TU in the shared target context
  llvm::outs() << "[Bug #30 FIX] CppToCVisitor using C_TU @ " << (void*)C_TranslationUnit << "\n";
}

// Phase 47: Enum Class Translation using EnumTranslator handler
bool CppToCVisitor::VisitEnumDecl(EnumDecl *ED) {
  // Skip declarations from non-transpilable files (system headers, etc.)
  if (!fileOriginTracker.shouldTranspile(ED)) {
    return true;
  }

  // Skip forward declarations
  if (!ED->isCompleteDefinition()) {
    return true;
  }

  // Skip compiler-generated enums
  if (ED->isImplicit()) {
    return true;
  }

  llvm::outs() << "Translating enum: " << ED->getNameAsString() << "\n";

  // Phase 47: Use EnumTranslator handler for translation
  // Create HandlerContext for enum translation
  cpptoc::HandlerContext ctx(Context, Builder.getContext(), Builder);

  // Delegate to EnumTranslator
  clang::Decl* C_Enum = m_enumTranslator->handleDecl(ED, ctx);

  if (!C_Enum) {
    llvm::outs() << "  -> ERROR: EnumTranslator returned nullptr for enum "
                 << ED->getNameAsString() << "\n";
    return false;
  }

  // BUG #2 FIX: Add enum to per-file C_TranslationUnit for emission
  // EnumTranslator adds enum to shared TU, but we need it in per-file C_TU
  C_TranslationUnit->addDecl(C_Enum);

  // Note: EnumTranslator already registers enum and constant mappings in ctx
  // But CppToCVisitor still uses enumConstantMap for backward compatibility
  // Update enumConstantMap from HandlerContext registrations
  if (ED->isScoped()) {
    for (const EnumConstantDecl* CPP_ECD : ED->enumerators()) {
      // Lookup translated constant from HandlerContext
      if (clang::Decl* C_Decl = ctx.lookupDecl(CPP_ECD)) {
        if (auto* C_ECD = llvm::dyn_cast<EnumConstantDecl>(C_Decl)) {
          enumConstantMap[CPP_ECD] = C_ECD;
          llvm::outs() << "    Mapped: " << CPP_ECD->getName() << " (C++) -> "
                       << C_ECD->getName() << " (C)\n";
        }
      }
    }
  }

  llvm::outs() << "  -> C enum " << ED->getNameAsString() << " created via EnumTranslator and added to C_TU\n";

  return true;
}

// Phase 53: Type Alias Translation (using X = Y)
bool CppToCVisitor::VisitTypeAliasDecl(TypeAliasDecl *TAD) {
  // Skip declarations from non-transpilable files (system headers, etc.)
  if (!fileOriginTracker.shouldTranspile(TAD)) {
    return true;
  }

  // Skip compiler-generated aliases
  if (TAD->isImplicit()) {
    return true;
  }

  // Skip template type alias declarations (they need to be instantiated first)
  if (TAD->getDescribedAliasTemplate() != nullptr) {
    // This is a template type alias pattern (e.g., template<typename T> using Vec = ...)
    // Skip it - we'll handle instantiations when they occur
    return true;
  }

  llvm::outs() << "Translating type alias: " << TAD->getNameAsString() << "\n";

  // Analyze the type alias
  cpptoc::TypeAliasInfo info = m_typeAliasAnalyzer->analyzeTypeAlias(TAD);

  // Generate C typedef
  clang::TypedefDecl* C_Typedef = m_typedefGenerator->generateTypedef(info);

  if (!C_Typedef) {
    llvm::outs() << "  -> ERROR: TypedefGenerator returned nullptr for type alias "
                 << TAD->getNameAsString() << "\n";
    return false;
  }

  llvm::outs() << "  -> C typedef " << info.aliasName << " created\n";

  return true;
}

// Phase 61: Reject C++20 modules with clear error message
// Decision: DEFERRED INDEFINITELY (see PLAN.md for rationale)
bool CppToCVisitor::VisitModuleDecl(Decl *MD) {
  // C++20 modules are not supported - C has no module system
  // Transpilation would lose all module benefits (compilation speed, encapsulation)
  // and result in identical code to traditional headers

  llvm::errs() << "\n";
  llvm::errs() << "ERROR: C++20 modules are not supported by the transpiler\n";
  llvm::errs() << "  Location: " << MD->getLocation().printToString(Context.getSourceManager()) << "\n";
  llvm::errs() << "\n";
  llvm::errs() << "  Reason: C has no module system. Modules are a C++ compilation optimization\n";
  llvm::errs() << "          that provides no semantic benefit when transpiling to C.\n";
  llvm::errs() << "\n";
  llvm::errs() << "  Migration Guide:\n";
  llvm::errs() << "  1. Convert module interfaces to traditional header files (.h)\n";
  llvm::errs() << "  2. Convert 'export module Name;' to 'name.h' with include guards\n";
  llvm::errs() << "  3. Convert 'export <declaration>' to public declarations in header\n";
  llvm::errs() << "  4. Convert 'import ModuleName;' to '#include \"module_name.h\"'\n";
  llvm::errs() << "  5. Convert non-exported declarations to 'static' in implementation\n";
  llvm::errs() << "\n";
  llvm::errs() << "  See docs/UNSUPPORTED_FEATURES.md for detailed migration examples.\n";
  llvm::errs() << "\n";

  // Fail transpilation cleanly
  return false;
}

// Story #15 + Story #50: Class-to-Struct Conversion with Base Class Embedding
bool CppToCVisitor::VisitCXXRecordDecl(CXXRecordDecl *D) {
  // Phase 40 (Bug Fix): Record declaration in FileOriginTracker
  // This populates fileCategories map, enabling getUserHeaderFiles() to work
  fileOriginTracker.recordDeclaration(D);

  // Phase 34 (v2.5.0): Skip declarations from non-transpilable files (system headers, etc.)
  if (!fileOriginTracker.shouldTranspile(D)) {
    return true;
  }

  // Edge case 1: Forward declarations - skip
  if (!D->isCompleteDefinition())
    return true;

  // Edge case 2: Compiler-generated classes - skip
  if (D->isImplicit())
    return true;

  // Edge case 3: Template patterns - skip (Bug #17)
  // Template patterns are handled by template monomorphization
  // Only template specializations (instantiations) should be visited here
  if (D->getDescribedClassTemplate() != nullptr) {
    // This is a template pattern (e.g., template<typename T> class LinkedList)
    // Skip it - we'll generate monomorphized versions from TemplateMonomorphizer
    return true;
  }

  // Edge case 3b: Nested classes inside template patterns - skip (Bug #17 extension)
  // If this class is defined inside a template class, skip it here.
  // It will be handled by TemplateMonomorphizer when generating monomorphized versions.
  // Example: struct Node inside template<typename T> class LinkedList
  DeclContext *DC = D->getDeclContext();
  while (DC && !DC->isTranslationUnit()) {
    if (CXXRecordDecl *ParentRecord = dyn_cast<CXXRecordDecl>(DC)) {
      if (ParentRecord->getDescribedClassTemplate() != nullptr) {
        // Parent is a template pattern, so this nested class should be skipped
        llvm::outs() << "Skipping nested class '" << D->getNameAsString()
                     << "' inside template pattern '" << ParentRecord->getNameAsString() << "'\n";
        return true;
      }
    }
    DC = DC->getParent();
  }

  // Edge case 4: Already translated - avoid duplicates
  if (cppToCMap.find(D) != cppToCMap.end())
    return true;

  llvm::outs() << "Translating class: " << D->getNameAsString() << "\n";

  // Build field list for C struct
  std::vector<FieldDecl *> fields;

  // Story #50: Embed base class fields at offset 0 (SRP: delegate to helper)
  collectBaseClassFields(D, fields);

  // Story #169: Inject vptr field if this is a polymorphic class without bases
  // If class has bases, base class would have already injected vptr
  if (D->getNumBases() == 0) {
    VptrInjectorInstance.injectVptrField(D, fields);
  }

  // Add derived class's own fields after base class fields and vptr
  for (FieldDecl *Field : D->fields()) {
    // Create C field with same type and name
    FieldDecl *CField = Builder.fieldDecl(Field->getType(), Field->getName());
    fields.push_back(CField);
  }

  // Create C struct using CNodeBuilder
  RecordDecl *CStruct = Builder.structDecl(D->getName(), fields);

  // Store mapping for method translation
  cppToCMap[D] = CStruct;

  // Phase 40 (Bug Fix): Smart filtering for cross-file struct definitions
  // Keep struct if:
  // 1. From main source file (not user header), OR
  // 2. From user header whose basename matches current file's basename
  //    (e.g., Vector3D.cpp keeps struct from Vector3D.h)
  bool shouldAddToTU = true;
  if (fileOriginTracker.isFromUserHeader(D)) {
    // Extract basename from current file
    std::string currentBasename;
    {
      auto &SM = Context.getSourceManager();
      FileID mainFID = SM.getMainFileID();
      if (auto mainFile = SM.getFileEntryRefForID(mainFID)) {
        std::string mainFileName = std::string(mainFile->getName());
        size_t lastSlash = mainFileName.find_last_of("/\\");
        size_t lastDot = mainFileName.find_last_of('.');
        if (lastSlash != std::string::npos) {
          currentBasename = mainFileName.substr(lastSlash + 1);
        } else {
          currentBasename = mainFileName;
        }
        if (lastDot != std::string::npos && lastDot > lastSlash) {
          currentBasename = currentBasename.substr(0, lastDot - (lastSlash != std::string::npos ? lastSlash + 1 : 0));
        }
      }
    }

    // Extract basename from struct's source file
    std::string structBasename;
    {
      std::string originFile = fileOriginTracker.getOriginFile(D);
      size_t lastSlash = originFile.find_last_of("/\\");
      size_t lastDot = originFile.find_last_of('.');
      if (lastSlash != std::string::npos) {
        structBasename = originFile.substr(lastSlash + 1);
      } else {
        structBasename = originFile;
      }
      if (lastDot != std::string::npos && lastDot > lastSlash) {
        structBasename = structBasename.substr(0, lastDot - (lastSlash != std::string::npos ? lastSlash + 1 : 0));
      }
    }

    // Keep if basenames match (e.g., Vector3D.cpp and Vector3D.h)
    shouldAddToTU = (currentBasename == structBasename);
    if (!shouldAddToTU) {
      llvm::outs() << "  -> struct " << CStruct->getName() << " NOT added to C_TU "
                   << "(from header " << structBasename << ", current file: " << currentBasename << ")\n";
    }
  }

  // Phase 32: Add to C TranslationUnit for output generation
  if (shouldAddToTU) {
    C_TranslationUnit->addDecl(CStruct);
    llvm::outs() << "  -> struct " << CStruct->getName() << " with "
                 << fields.size() << " fields\n";
  }

  // Story #62: Generate implicit constructors if needed
  generateImplicitConstructors(D);

  // Epic #193: Generate ACSL class invariants if enabled
  if (m_classAnnotator && m_typeInvariantGen) {
    llvm::outs() << "Generating ACSL invariants for class: "
                 << D->getNameAsString() << "\n";

    // Generate class invariants
    std::string classInvariant =
        m_classAnnotator->generateClassInvariantPredicate(D);

    // Generate type invariants if full level
    std::string typeInvariants;
    if (getACSLLevel() == ACSLLevel::Full && m_typeInvariantGen) {
      typeInvariants = m_typeInvariantGen->generateTypeInvariant(D);
    }

    // Combine annotations
    std::string fullAnnotation = classInvariant;
    if (!typeInvariants.empty()) {
      fullAnnotation += "\n" + typeInvariants;
    }

    // Emit ACSL annotation
    if (!fullAnnotation.empty()) {
      emitACSL(fullAnnotation, getACSLOutputMode());
    }
  }

  // Phase 31-03: Generate COM-style static declarations for ALL methods
  std::string allMethodDecls = generateAllMethodDeclarations(D);
  if (!allMethodDecls.empty()) {
    llvm::outs() << "\n" << allMethodDecls << "\n";
  }

  // Phase 9 (v2.2.0): Generate vtable struct for polymorphic classes
  if (VirtualAnalyzer.isPolymorphic(D)) {
    llvm::outs() << "Generating vtable for polymorphic class: "
                 << D->getNameAsString() << "\n";

    // Generate vtable struct definition
    std::string vtableStruct = m_vtableGenerator->generateVtableStruct(D);
    if (!vtableStruct.empty()) {
      llvm::outs() << "Vtable struct generated:\n" << vtableStruct << "\n";

      // Generate vtable instance (global variable)
      std::string className = D->getNameAsString();
      std::ostringstream vtableInstance;
      vtableInstance << "\n// Vtable instance for " << className << "\n";
      vtableInstance << "struct " << className << "_vtable " << className
                     << "_vtable_instance = {\n";
      vtableInstance << "    .type_info = &" << className
                     << "_type_info,  // RTTI type_info (placeholder)\n";

      // Get methods in vtable order
      auto methods = m_vtableGenerator->getVtableMethodOrder(D);

      // Initialize function pointers
      for (auto *method : methods) {
        std::string methodName;
        if (isa<CXXDestructorDecl>(method)) {
          methodName = "destructor";
          vtableInstance << "    ." << methodName << " = " << className
                         << "_destructor,\n";
        } else {
          methodName = method->getNameAsString();
          vtableInstance << "    ." << methodName << " = " << className << "_"
                         << methodName << ",\n";
        }
      }

      vtableInstance << "};\n";

      // Store vtable instance code
      m_vtableInstances[className] = vtableInstance.str();

      llvm::outs() << "Vtable instance generated:\n"
                   << vtableInstance.str() << "\n";
    }
  }

  return true;
}

// Story #16: Method-to-Function Conversion
bool CppToCVisitor::VisitCXXMethodDecl(CXXMethodDecl *MD) {
  // Bug #43 FIX: Use FileOriginFilter for proper file-based filtering
  // This ensures method bodies from StateMachine.cpp don't get processed when
  // we're translating main.cpp (even though main.cpp includes StateMachine.h)
  if (fileOriginFilter && !fileOriginFilter->shouldProcessMethod(MD)) {
    return true;
  }

  // Fallback to old tracker if filter not initialized
  if (!fileOriginFilter && !fileOriginTracker.shouldTranspile(MD)) {
    return true;
  }

  // Edge case 1: Skip implicit methods (compiler-generated)
  if (MD->isImplicit()) {
    return true;
  }

  // Edge case 2: Skip methods of template patterns (Bug #17)
  // Template pattern methods are handled by template monomorphization
  CXXRecordDecl *ParentClass = MD->getParent();
  if (ParentClass && ParentClass->getDescribedClassTemplate() != nullptr) {
    // This method belongs to a template pattern class
    // Skip it - we'll generate monomorphized versions from TemplateMonomorphizer
    return true;
  }

  // Edge case 2b: Skip methods of nested classes inside template patterns (Bug #17 extension)
  // If the parent class is nested inside a template class, skip it here.
  // It will be handled by TemplateMonomorphizer when generating monomorphized versions.
  // Example: methods of struct Node inside template<typename T> class LinkedList
  if (ParentClass) {
    DeclContext *DC = ParentClass->getDeclContext();
    while (DC && !DC->isTranslationUnit()) {
      if (CXXRecordDecl *AncestorRecord = dyn_cast<CXXRecordDecl>(DC)) {
        if (AncestorRecord->getDescribedClassTemplate() != nullptr) {
          // Ancestor is a template pattern, so this method should be skipped
          llvm::outs() << "Skipping method '" << MD->getNameAsString()
                       << "' of nested class '" << ParentClass->getNameAsString()
                       << "' inside template pattern '" << AncestorRecord->getNameAsString() << "'\n";
          return true;
        }
      }
      DC = DC->getParent();
    }
  }

  // Edge case 3: Skip constructors/destructors (handled separately)
  if (isa<CXXConstructorDecl>(MD) || isa<CXXDestructorDecl>(MD)) {
    return true;
  }

  // Bug fix #11: Skip method declarations (no body) to prevent duplicates
  // Only process method definitions to avoid generating the same function twice
  // (once from header declaration, once from .cpp definition)
  // Bug fix #44: Use isThisDeclarationADefinition() instead of hasBody()
  // hasBody() returns true for BOTH declaration and definition in the same TU,
  // but isThisDeclarationADefinition() only returns true for the actual definition
  if (!MD->isThisDeclarationADefinition()) {
    return true;
  }

  // Bug #43 FIX: FileOriginFilter ensures proper file-based filtering
  // Do NOT check targetCtx.getMethodMap() here - that map is shared across files which causes issues
  // FileOriginFilter already prevents cross-file pollution
  // We DO need the canonical decl for later storage
  CXXMethodDecl *CanonicalMD = MD->getCanonicalDecl();

  // Phase 4: Handle explicit object parameters (deducing this, C++23 P0847R7)
  if (MD->isExplicitObjectMemberFunction()) {
    llvm::outs() << "Translating explicit object member function: "
                 << MD->getQualifiedNameAsString() << "\n";
    auto C_Funcs = m_deducingThisTrans->transformMethod(MD, Context, C_TranslationUnit);
    if (!C_Funcs.empty()) {
      llvm::outs() << "  -> Generated " << C_Funcs.size() << " overload(s):\n";
      for (auto* C_Func : C_Funcs) {
        llvm::outs() << "     " << C_Func->getNameAsString() << "\n";
      }
    }
    return true;
  }

  // Phase 2: Handle static operator() and operator[] (C++23)
  if (MD->isStatic() && MD->isOverloadedOperator()) {
    auto Op = MD->getOverloadedOperator();
    if (Op == OO_Call || Op == OO_Subscript) {
      llvm::outs() << "Translating static operator: "
                   << MD->getQualifiedNameAsString() << "\n";
      auto* C_Func = m_staticOperatorTrans->transformMethod(MD, Context, C_TranslationUnit);
      if (C_Func) {
        // Function already added to C_TranslationUnit by translator
        llvm::outs() << "  -> " << C_Func->getNameAsString() << "\n";
      }
      return true;
    }
  }

  // Phase 50: Handle arithmetic operator overloading (v2.10.0)
  if (MD->isOverloadedOperator() && m_arithmeticOpTrans->isArithmeticOperator(MD->getOverloadedOperator())) {
    llvm::outs() << "Translating arithmetic operator: "
                 << MD->getQualifiedNameAsString() << "\n";
    auto* C_Func = m_arithmeticOpTrans->transformMethod(MD, Context, C_TranslationUnit);
    if (C_Func) {
      // Store in method map for later call site transformation
      std::string methodKey = Mangler.mangleName(MD);
      targetCtx.getMethodMap()[methodKey] = C_Func;
      llvm::outs() << "  -> " << C_Func->getNameAsString() << "\n";
    }
    return true;
  }

  // Phase 51: Handle comparison & logical operator overloading (v2.11.0)
  if (MD->isOverloadedOperator() && m_comparisonOpTrans->isComparisonOperator(MD->getOverloadedOperator())) {
    llvm::outs() << "Translating comparison/logical operator: "
                 << MD->getQualifiedNameAsString() << "\n";
    auto* C_Func = m_comparisonOpTrans->transformMethod(MD, Context, C_TranslationUnit);
    if (C_Func) {
      // Store in method map for later call site transformation
      std::string methodKey = Mangler.mangleName(MD);
      targetCtx.getMethodMap()[methodKey] = C_Func;
      llvm::outs() << "  -> " << C_Func->getNameAsString() << " (returns bool)\n";
    }
    return true;
  }

  // Phase 52: Handle special operator overloading (v2.12.0)
  // Includes: operator[], operator(), operator->, operator*, operator<<, operator>>,
  // operator=, operator&, operator, (comma)
  if (MD->isOverloadedOperator() && m_specialOpTrans->isSpecialOperator(MD->getOverloadedOperator())) {
    llvm::outs() << "Translating special operator: "
                 << MD->getQualifiedNameAsString() << "\n";
    auto* C_Func = m_specialOpTrans->transformMethod(MD, Context, C_TranslationUnit);
    if (C_Func) {
      // Store in method map for later call site transformation
      std::string methodKey = Mangler.mangleName(MD);
      targetCtx.getMethodMap()[methodKey] = C_Func;
      llvm::outs() << "  -> " << C_Func->getNameAsString() << "\n";
    }
    return true;
  }

  // Edge case 4: Skip virtual methods (handled by vtable infrastructure)
  if (MD->isVirtual()) {
    llvm::outs() << "Skipping virtual method (handled by vtable): "
                 << MD->getQualifiedNameAsString() << "\n";
    return true;
  }

  // Story #131 & Story #134: Move and copy assignment operators
  // RESOLVED by Phase 52 (v2.12.0): Now handled by SpecialOperatorTranslator above
  // Both copy assignment (operator=(const T&)) and move assignment (operator=(T&&))
  // are properly translated as special operators with explicit this parameter
  // Old TODOs at lines 528 and 539 are now RESOLVED

  llvm::outs() << "Translating method: " << MD->getQualifiedNameAsString()
               << "\n";

  CXXRecordDecl *Parent = MD->getParent();
  RecordDecl *CStruct = nullptr;

  // Find C struct for parent class
  if (cppToCMap.find(Parent) != cppToCMap.end()) {
    CStruct = cppToCMap[Parent];
  } else {
    llvm::outs() << "  Warning: Parent struct not found, skipping\n";
    return true;
  }

  // Build parameter list: this + original params
  std::vector<ParmVarDecl *> params;

  // Add this parameter
  QualType thisType = Builder.ptrType(Builder.structType(Parent->getName()));
  ParmVarDecl *thisParam = Builder.param(thisType, "this");
  params.push_back(thisParam);

  // Add original parameters
  for (ParmVarDecl *Param : MD->parameters()) {
    ParmVarDecl *CParam = Builder.param(Param->getType(), Param->getName());
    params.push_back(CParam);
  }

  // Generate function name using name mangling
  std::string funcName = Mangler.mangleName(MD);

  // Create C function (body will be added below)
  FunctionDecl *CFunc =
      Builder.funcDecl(funcName, MD->getReturnType(), params, nullptr);

  // Set translation context for body translation (Story #19)
  currentThisParam = thisParam;
  currentMethod = MD;

  // Translate method body if it exists
  if (MD->hasBody()) {
    Stmt *Body = MD->getBody();
    Stmt *TranslatedBody = translateStmt(Body);
    CFunc->setBody(TranslatedBody);
    llvm::outs() << "  -> " << funcName << " with body translated\n";
  } else {
    llvm::outs() << "  -> " << funcName << " (no body)\n";
  }

  // Clear translation context
  currentThisParam = nullptr;
  currentMethod = nullptr;

  // Store mapping using canonical declaration to prevent duplicate processing
  std::string methodKey = Mangler.mangleName(CanonicalMD);
  targetCtx.getMethodMap()[methodKey] = CFunc;

  // Phase 32: Add to C TranslationUnit for output generation
  C_TranslationUnit->addDecl(CFunc);

  // Mark as generated to prevent re-processing as standalone function
  generatedFunctions.insert(CFunc);

  llvm::outs() << "  -> " << funcName << " with " << params.size()
               << " parameters\n";

  return true;
}

// Phase 52: Conversion Operator Translation (v2.12.0)
// Handles operator T(), explicit operator bool(), etc.
bool CppToCVisitor::VisitCXXConversionDecl(CXXConversionDecl *CD) {
  if (!CD || CD->isImplicit()) {
    return true;
  }

  // Skip if not from current file
  if (fileOriginFilter && !fileOriginFilter->shouldProcess(CD)) {
    return true;
  }

  llvm::outs() << "Translating conversion operator: "
               << CD->getQualifiedNameAsString() << "\n";

  // Use SpecialOperatorTranslator to handle conversion operators
  auto* C_Func = m_specialOpTrans->transformConversion(CD, Context, C_TranslationUnit);
  if (C_Func) {
    // Store in method map for later call site transformation
    // Note: CXXConversionDecl is a subclass of CXXMethodDecl
    std::string methodKey = Mangler.mangleName(CD);
    targetCtx.getMethodMap()[methodKey] = C_Func;
    llvm::outs() << "  -> " << C_Func->getNameAsString() << "\n";
  }

  return true;
}

// Story #17: Constructor Translation
bool CppToCVisitor::VisitCXXConstructorDecl(CXXConstructorDecl *CD) {
  // Phase 34 (v2.5.0): Skip declarations from non-transpilable files
  if (!fileOriginTracker.shouldTranspile(CD)) {
    return true;
  }

  // Edge case: Skip implicit constructors (compiler-generated)
  if (CD->isImplicit()) {
    return true;
  }

  // Edge case: Skip constructors of template patterns (Bug #17)
  // Template pattern constructors are handled by template monomorphization
  CXXRecordDecl *ParentClass = CD->getParent();
  if (ParentClass && ParentClass->getDescribedClassTemplate() != nullptr) {
    // This constructor belongs to a template pattern class
    // Skip it - we'll generate monomorphized versions from TemplateMonomorphizer
    return true;
  }

  // Edge case extension: Skip constructors of nested classes inside template patterns (Bug #17 extension)
  // If the parent class is nested inside a template class, skip it here.
  // It will be handled by TemplateMonomorphizer when generating monomorphized versions.
  // Example: constructor of struct Node inside template<typename T> class LinkedList
  if (ParentClass) {
    DeclContext *DC = ParentClass->getDeclContext();
    while (DC && !DC->isTranslationUnit()) {
      if (CXXRecordDecl *AncestorRecord = dyn_cast<CXXRecordDecl>(DC)) {
        if (AncestorRecord->getDescribedClassTemplate() != nullptr) {
          // Ancestor is a template pattern, so this constructor should be skipped
          llvm::outs() << "Skipping constructor of nested class '" << ParentClass->getNameAsString()
                       << "' inside template pattern '" << AncestorRecord->getNameAsString() << "'\n";
          return true;
        }
      }
      DC = DC->getParent();
    }
  }

  // Bug fix #18: Skip constructor declarations without definitions (cross-file duplicates)
  // Only process constructors with bodies (actual definitions in .cpp files)
  // Declarations from headers should only generate forward declarations, not definitions
  if (!CD->isThisDeclarationADefinition() || !CD->hasBody()) {
    // This is just a declaration (from header), not a definition
    // The actual definition will be processed when we visit the .cpp file
    return true;
  }

  // Bug fix #15: Skip constructors already translated to prevent redefinitions
  // Check if this constructor was already processed (prevents duplicate function definitions)
  // Note: We use mangled name as key (not pointer) because each file has its own C++ ASTContext
  CXXConstructorDecl *CanonicalCD = cast<CXXConstructorDecl>(CD->getCanonicalDecl());
  std::string mangledKey = Mangler.mangleConstructor(CD);
  if (targetCtx.getCtorMap().count(mangledKey) > 0) {
    llvm::outs() << "  -> Already translated, skipping redefinition of "
                 << CD->getParent()->getName() << "::"
                 << CD->getParent()->getName() << "\n";
    return true;
  }

  // Story #130: Handle move constructors specially
  if (MoveCtorTranslator.isMoveConstructor(CD)) {
    llvm::outs() << "Detected move constructor: " << CD->getParent()->getName()
                 << "::" << CD->getParent()->getName() << "(&&)\n";

    std::string moveCtorCode = MoveCtorTranslator.generateMoveConstructor(CD);
    if (!moveCtorCode.empty()) {
      llvm::outs() << "Generated move constructor C code:\n"
                   << moveCtorCode << "\n";
    }

    // Note: For now, we just generate the code for testing/validation
    // Full integration would store this in a function declaration
    // Continue with normal processing to store in targetCtx.getCtorMap() for now
  }

  llvm::outs() << "Translating constructor: " << CD->getParent()->getName()
               << "::" << CD->getParent()->getName() << "\n";

  CXXRecordDecl *Parent = CD->getParent();
  RecordDecl *CStruct = nullptr;

  // Find C struct for parent class
  if (cppToCMap.find(Parent) != cppToCMap.end()) {
    CStruct = cppToCMap[Parent];
  } else {
    llvm::outs() << "  Warning: Parent struct not found, skipping\n";
    return true;
  }

  // Build parameter list: this + original params
  std::vector<ParmVarDecl *> params;

  // Add 'this' parameter - use the existing C struct type
  QualType thisType = Builder.ptrType(Context.getRecordType(CStruct));
  ParmVarDecl *thisParam = Builder.param(thisType, "this");
  params.push_back(thisParam);

  // Add original parameters
  for (ParmVarDecl *Param : CD->parameters()) {
    ParmVarDecl *CParam = Builder.param(Param->getType(), Param->getName());
    params.push_back(CParam);
  }

  // Generate constructor name using name mangling
  std::string funcName = Mangler.mangleConstructor(CD);

  // Create C init function (body will be added below)
  FunctionDecl *CFunc =
      Builder.funcDecl(funcName, Builder.voidType(), params, nullptr);

  // Build function body
  std::vector<Stmt *> stmts;

  // Set translation context for expression translation
  currentThisParam = thisParam;
  currentMethod = CD;

  // Story #171: Inject vptr initialization for polymorphic classes
  // This must happen FIRST, before base/member initialization
  if (VirtualAnalyzer.isPolymorphic(Parent)) {
    Stmt *vptrInit = m_vtableInitializer->generateVptrInit(Parent, thisParam);
    if (vptrInit) {
      stmts.push_back(vptrInit);
      llvm::outs() << "  -> Injected vptr initialization\n";
    }
  }

  // Story #184: Handle delegating constructors
  if (CD->isDelegatingConstructor()) {
    llvm::outs() << "  Delegating constructor detected\n";

    // Find the delegating initializer
    CXXCtorInitializer *DelegatingInit = nullptr;
    for (CXXCtorInitializer *Init : CD->inits()) {
      if (Init->isDelegatingInitializer()) {
        DelegatingInit = Init;
        break;
      }
    }

    if (DelegatingInit) {
      // Get the target constructor from the delegating initializer
      Expr *InitExpr = DelegatingInit->getInit();
      CXXConstructExpr *CtorExpr = dyn_cast_or_null<CXXConstructExpr>(InitExpr);

      if (CtorExpr) {
        CXXConstructorDecl *TargetCtor = CtorExpr->getConstructor();

        // Lookup the C function for the target constructor
        std::string targetCtorKey = Mangler.mangleConstructor(TargetCtor);
        auto it = targetCtx.getCtorMap().find(targetCtorKey);
        if (it != targetCtx.getCtorMap().end()) {
          FunctionDecl *TargetCFunc = it->second;

          // Build argument list: this + arguments from delegating call
          std::vector<Expr *> targetArgs;
          targetArgs.push_back(Builder.ref(thisParam));

          for (unsigned i = 0; i < CtorExpr->getNumArgs(); i++) {
            Expr *Arg = CtorExpr->getArg(i);
            Expr *TranslatedArg = translateExpr(Arg);
            if (TranslatedArg) {
              targetArgs.push_back(TranslatedArg);
            }
          }

          // Create call to target constructor
          CallExpr *DelegateCall = Builder.call(TargetCFunc, targetArgs);
          if (DelegateCall) {
            stmts.push_back(DelegateCall);
            llvm::outs() << "  -> Delegating to "
                         << TargetCFunc->getNameAsString() << "\n";
          }
        } else {
          llvm::outs() << "  Warning: Target constructor function not found\n";
        }
      }
    }
    // Note: For delegating constructors, we skip base/member initialization
    // because the target constructor handles all initialization
  } else {
    // Non-delegating constructor: normal initialization
    // Story #51: Emit base constructor calls FIRST (before member initializers)
    emitBaseConstructorCalls(CD, thisParam, stmts);

    // Story #63: Emit member constructor calls in DECLARATION order
    // Handles both class-type members (constructor calls) and primitives
    // (assignment)
    emitMemberConstructorCalls(CD, thisParam, stmts);
  }

  // Translate constructor body statements
  if (CD->hasBody()) {
    CompoundStmt *Body = dyn_cast<CompoundStmt>(CD->getBody());
    if (Body) {
      for (Stmt *S : Body->body()) {
        Stmt *TranslatedStmt = translateStmt(S);
        if (TranslatedStmt) {
          stmts.push_back(TranslatedStmt);
        }
      }
    }
  }

  // Clear translation context
  currentThisParam = nullptr;
  currentMethod = nullptr;

  // Set function body
  CFunc->setBody(Builder.block(stmts));

  // Store mapping using mangled name (not pointer) to work across C++ ASTContexts
  targetCtx.getCtorMap()[mangledKey] = CFunc;
  llvm::outs() << "  [DEBUG] Added constructor to SHARED map: " << funcName
               << " (key: " << mangledKey << ", map size now: " << targetCtx.getCtorMap().size() << ")\n";

  // Phase 32: Add to C TranslationUnit for output generation
  C_TranslationUnit->addDecl(CFunc);

  llvm::outs() << "  -> " << funcName << " with " << params.size()
               << " parameters, " << stmts.size() << " statements\n";

  return true;
}

bool CppToCVisitor::VisitVarDecl(VarDecl *VD) {
  // Phase 34 (v2.5.0): Skip declarations from non-transpilable files
  if (!fileOriginTracker.shouldTranspile(VD)) {
    return true;
  }

  llvm::outs() << "Found variable: " << VD->getNameAsString() << "\n";
  return true;
}

// Retrieve generated C struct by class name (for testing)
RecordDecl *CppToCVisitor::getCStruct(llvm::StringRef className) const {
  // Search through mapping to find struct by name
  for (const auto &entry : cppToCMap) {
    if (entry.second && entry.second->getName() == className) {
      return entry.second;
    }
  }
  return nullptr;
}

// Retrieve generated C function by name (for testing)
FunctionDecl *CppToCVisitor::getCFunc(llvm::StringRef funcName) const {
  // Search through method mapping to find function by name
  for (const auto &entry : targetCtx.getMethodMap()) {
    if (entry.second && entry.second->getName() == funcName) {
      return entry.second;
    }
  }

  // Phase 8: Also search standalone function map
  auto it = standaloneFuncMap.find(funcName.str());
  if (it != standaloneFuncMap.end()) {
    return it->second;
  }

  return nullptr;
}

// Retrieve generated C constructor function by name (for testing)
FunctionDecl *CppToCVisitor::getCtor(llvm::StringRef funcName) const {
  // Search through mapping to find constructor by name
  for (const auto &entry : targetCtx.getCtorMap()) {
    if (entry.second && entry.second->getName() == funcName) {
      return entry.second;
    }
  }
  return nullptr;
}

// Retrieve generated C destructor function by name (for testing - Story #152)
FunctionDecl *CppToCVisitor::getDtor(llvm::StringRef funcName) const {
  // Search through mapping to find destructor by name
  for (const auto &entry : targetCtx.getDtorMap()) {
    if (entry.second && entry.second->getName() == funcName) {
      return entry.second;
    }
  }
  return nullptr;
}

// ============================================================================
// Epic #5: RAII + Automatic Destructor Injection
// Story #152: Destructor Injection at Function Exit
// ============================================================================

// Visit C++ destructor declarations
bool CppToCVisitor::VisitCXXDestructorDecl(CXXDestructorDecl *DD) {
  // Phase 34 (v2.5.0): Skip declarations from non-transpilable files
  if (!fileOriginTracker.shouldTranspile(DD)) {
    return true;
  }

  // Edge case: Skip implicit destructors (compiler-generated)
  if (DD->isImplicit() || DD->isTrivial()) {
    return true;
  }

  // Edge case: Skip destructors of template patterns (Bug #17)
  // Template pattern destructors are handled by template monomorphization
  CXXRecordDecl *ParentClass = DD->getParent();
  if (ParentClass && ParentClass->getDescribedClassTemplate() != nullptr) {
    // This destructor belongs to a template pattern class
    // Skip it - we'll generate monomorphized versions from TemplateMonomorphizer
    return true;
  }

  // Bug fix #15: Skip destructors already translated to prevent redefinitions
  // Check if this destructor was already processed (prevents duplicate function definitions)
  // Note: We check the canonical declaration because the AST may contain multiple
  // CXXDestructorDecl nodes for the same destructor (e.g., declaration vs definition)
  CXXDestructorDecl *CanonicalDD = cast<CXXDestructorDecl>(DD->getCanonicalDecl());
  std::string dtorKey = Mangler.mangleDestructor(CanonicalDD);
  if (targetCtx.getDtorMap().count(dtorKey) > 0) {
    llvm::outs() << "  -> Already translated, skipping redefinition of ~"
                 << DD->getParent()->getName() << "\n";
    return true;
  }

  llvm::outs() << "Translating destructor: ~" << DD->getParent()->getName()
               << "\n";

  CXXRecordDecl *Parent = DD->getParent();
  RecordDecl *CStruct = nullptr;

  // Find C struct for parent class
  if (cppToCMap.find(Parent) != cppToCMap.end()) {
    CStruct = cppToCMap[Parent];
  } else {
    llvm::outs() << "  Warning: Parent struct not found, skipping\n";
    return true;
  }

  // Build parameter list: this pointer only
  std::vector<ParmVarDecl *> params;
  QualType thisType = Builder.ptrType(Context.getRecordType(CStruct));
  ParmVarDecl *thisParam = Builder.param(thisType, "this");
  params.push_back(thisParam);

  // Generate destructor name using name mangling
  std::string funcName = Mangler.mangleDestructor(DD);

  // Create C cleanup function
  FunctionDecl *CFunc =
      Builder.funcDecl(funcName, Builder.voidType(), params, nullptr);

  // Set translation context for body translation
  currentThisParam = thisParam;
  currentMethod = DD;

  // Build destructor body with base destructor chaining
  std::vector<Stmt *> stmts;

  // Translate derived destructor body FIRST
  if (DD->hasBody()) {
    CompoundStmt *Body = dyn_cast<CompoundStmt>(DD->getBody());
    if (Body) {
      for (Stmt *S : Body->body()) {
        Stmt *TranslatedStmt = translateStmt(S);
        if (TranslatedStmt) {
          stmts.push_back(TranslatedStmt);
        }
      }
    }
  }

  // Story #63: Emit member destructor calls in REVERSE declaration order
  // Called AFTER derived body, BEFORE base destructors
  CXXRecordDecl *ClassDecl = DD->getParent();
  emitMemberDestructorCalls(ClassDecl, thisParam, stmts);

  // Story #52: Emit base destructor calls AFTER member destructors
  emitBaseDestructorCalls(DD, thisParam, stmts);

  // Set complete body
  CFunc->setBody(Builder.block(stmts));
  llvm::outs() << "  -> " << funcName << " with " << stmts.size()
               << " statements\n";

  // Clear translation context
  currentThisParam = nullptr;
  currentMethod = nullptr;

  // Store mapping using canonical declaration to prevent duplicate processing
  targetCtx.getDtorMap()[dtorKey] = CFunc;

  // Phase 32: Add to C TranslationUnit for output generation
  C_TranslationUnit->addDecl(CFunc);

  llvm::outs() << "  -> " << funcName << " created\n";

  return true;
}

// Visit function declarations for destructor injection
bool CppToCVisitor::VisitFunctionDecl(FunctionDecl *FD) {
  // Phase 34 (v2.5.0): Skip declarations from non-transpilable files
  if (!fileOriginTracker.shouldTranspile(FD)) {
    return true;
  }

  // Skip if this is a C++ method (handled by VisitCXXMethodDecl)
  if (isa<CXXMethodDecl>(FD)) {
    return true;
  }

  // Phase 6: Handle constexpr functions (C++23 enhancements)
  if (FD->isConstexpr()) {
    m_constexprHandler->handleConstexprFunction(FD, Context);
    // Continue processing (handler determines strategy internally)
  }

  // Skip if no body
  if (!FD->hasBody()) {
    return true;
  }

  // FIX: Skip functions we generated ourselves to prevent infinite recursion
  // (following Frama-Clang's pattern of marking synthetic functions)
  if (generatedFunctions.count(FD) > 0) {
    llvm::outs() << "  -> Skipping generated function to prevent recursion\n";
    return true;
  }

  // Story #152: Analyze function for RAII objects and inject destructors
  llvm::outs() << "Analyzing function for RAII: " << FD->getNameAsString()
               << "\n";

  // Use CFGAnalyzer to find local variables
  CFGAnalyzer analyzer;
  analyzer.analyzeCFG(FD);

  std::vector<VarDecl *> localVars = analyzer.getLocalVars();
  llvm::outs() << "  Found " << localVars.size() << " local variables\n";

  // Filter to only objects with destructors
  std::vector<VarDecl *> objectsToDestroy;
  for (VarDecl *VD : localVars) {
    if (hasNonTrivialDestructor(VD->getType())) {
      objectsToDestroy.push_back(VD);
      llvm::outs() << "  Variable '" << VD->getNameAsString()
                   << "' has destructor\n";
    }
  }

  if (!objectsToDestroy.empty()) {
    llvm::outs() << "  Will inject destructors for " << objectsToDestroy.size()
                 << " objects\n";

    // Story #44: Store objects for destruction at function scope
    // These will be used during statement translation to inject destructor
    // calls
    currentFunctionObjectsToDestroy = objectsToDestroy;

    // Story #45: Clear previous return tracking for this function
    currentFunctionReturns.clear();

    // Story #47: Clear previous goto/label tracking for this function
    currentFunctionGotos.clear();
    currentFunctionLabels.clear();

    // Story #48: Clear previous break/continue tracking for this function
    currentFunctionBreaksContinues.clear();

    // Story #45: Analyze return statements in the function
    // The VisitReturnStmt will be called automatically during traversal
    // and will populate currentFunctionReturns

    // Story #47: Analyze goto statements after traversal
    // The VisitGotoStmt and VisitLabelStmt will be called during traversal
    // and will populate currentFunctionGotos and currentFunctionLabels
    // After traversal, we match them and determine destructor injection points
    analyzeGotoStatements(FD);

    // Story #48: Analyze break/continue statements after traversal
    // The VisitBreakStmt and VisitContinueStmt will be called during traversal
    // and will populate currentFunctionBreaksContinues
    // After traversal, we identify objects needing destruction
    analyzeBreakContinueStatements(FD);

  } else {
    currentFunctionObjectsToDestroy.clear();
    currentFunctionReturns.clear();
    currentFunctionGotos.clear();
    currentFunctionLabels.clear();
    currentFunctionBreaksContinues.clear();
  }

  // Epic #193: Generate ACSL function contracts if enabled
  if (m_functionAnnotator && m_behaviorAnnotator) {
    llvm::outs() << "Generating ACSL contract for function: "
                 << FD->getNameAsString() << "\n";

    // Generate function contract (requires, ensures, assigns)
    std::string functionContract =
        m_functionAnnotator->generateFunctionContract(FD);

    // Generate behavior annotations if full level
    std::string behaviorAnnotations;
    if (getACSLLevel() == ACSLLevel::Full && m_behaviorAnnotator) {
      behaviorAnnotations = m_behaviorAnnotator->generateBehaviors(FD);
    }

    // Combine annotations
    std::string fullAnnotation = functionContract;
    if (!behaviorAnnotations.empty()) {
      fullAnnotation += "\n" + behaviorAnnotations;
    }

    // Emit ACSL annotation
    if (!fullAnnotation.empty()) {
      emitACSL(fullAnnotation, getACSLOutputMode());
    }
  }

  // ============================================================================
  // Phase 8: Standalone Function Translation (v2.1.0)
  // ============================================================================
  // Translate standalone functions (non-member functions) to C
  // This enables translation of free functions, main(), function overloading

  // Skip methods - they're handled by VisitCXXMethodDecl
  if (isa<CXXMethodDecl>(FD)) {
    return true; // Already handled
  }

  // Skip forward declarations (no body)
  if (!FD->hasBody()) {
    return true; // Only translate definitions
  }

  llvm::outs() << "Translating standalone function: " << FD->getNameAsString()
               << "\n";

  // Get mangled name (handles overloading, main(), extern "C")
  std::string mangledName = Mangler.mangleStandaloneFunction(FD);

  llvm::outs() << "  Mangled name: " << mangledName << "\n";

  // Check if function already translated (deduplication)
  if (standaloneFuncMap.count(mangledName) > 0) {
    llvm::outs() << "  -> Already translated, skipping\n";
    return true;
  }

  // Build parameter list for C function
  llvm::SmallVector<ParmVarDecl *, 4> cParams;
  for (ParmVarDecl *Param : FD->parameters()) {
    // Create parameter with same type and name
    ParmVarDecl *CParam = Builder.param(Param->getType(), Param->getName());
    cParams.push_back(CParam);
  }

  // Get function body and translate it (Phase 34-05)
  Stmt *body = FD->getBody();
  Stmt *translatedBody = nullptr;
  if (body) {
    translatedBody = translateStmt(body);
  }

  // Check if function is variadic
  bool isVariadic = FD->isVariadic();

  // Create C function declaration with mangled name
  FunctionDecl *CFunc =
      Builder.funcDecl(mangledName, FD->getReturnType(), cParams, translatedBody,
                       CC_C,      // Calling convention (default)
                       isVariadic // Variadic property
      );

  // Preserve linkage and storage class
  if (FD->getStorageClass() == SC_Static) {
    CFunc->setStorageClass(SC_Static);
    llvm::outs() << "  Linkage: static (internal)\n";
  } else if (FD->getStorageClass() == SC_Extern || FD->isExternC()) {
    CFunc->setStorageClass(SC_Extern);
    llvm::outs() << "  Linkage: extern (external)\n";
  }

  // Preserve inline specifier
  if (FD->isInlineSpecified()) {
    CFunc->setInlineSpecified(true);
    llvm::outs() << "  Inline: yes\n";
  }

  // Log variadic property
  if (isVariadic) {
    llvm::outs() << "  Variadic: yes\n";
  }

  // Store in standalone function map
  standaloneFuncMap[mangledName] = CFunc;

  // Phase 32: Add to C TranslationUnit for output generation
  C_TranslationUnit->addDecl(CFunc);

  // Mark as generated to prevent re-processing
  generatedFunctions.insert(CFunc);

  llvm::outs() << "  -> C function '" << mangledName << "' created\n";
  llvm::outs() << "  Parameters: " << cParams.size() << "\n";
  llvm::outs() << "  Return type: " << CFunc->getReturnType().getAsString()
               << "\n";

  return true;
}

// ============================================================================
// Epic #6: Single Inheritance Helper Methods
// ============================================================================

/**
 * Story #50: Collect all base class fields in inheritance order
 *
 * SOLID Principles Applied:
 * - Single Responsibility: Only collects base fields, doesn't modify anything
 * - Open/Closed: Can be extended for multiple inheritance without modification
 * - Dependency Inversion: Depends on FieldDecl abstraction, not concrete types
 *
 * Algorithm:
 * 1. Iterate through each base class
 * 2. Lookup the already-translated C struct for that base
 * 3. Copy all fields from base C struct (which already includes its bases)
 * 4. This naturally handles multi-level inheritance (A -> B -> C)
 */
void CppToCVisitor::collectBaseClassFields(CXXRecordDecl *D,
                                           std::vector<FieldDecl *> &fields) {
  // For each direct base class
  for (const CXXBaseSpecifier &Base : D->bases()) {
    CXXRecordDecl *BaseClass = Base.getType()->getAsCXXRecordDecl();

    // Edge case: Invalid or incomplete base class definition
    if (!BaseClass || !BaseClass->isCompleteDefinition()) {
      continue;
    }

    // Lookup the C struct for this base class
    // Note: Base classes are visited before derived classes by AST traversal
    auto it = cppToCMap.find(BaseClass);
    if (it == cppToCMap.end()) {
      // Base class not yet translated - should not happen with proper traversal
      llvm::errs() << "Warning: Base class " << BaseClass->getNameAsString()
                   << " not yet translated\n";
      continue;
    }

    RecordDecl *BaseCStruct = it->second;

    // Copy all fields from base C struct (DRY: reuse existing field decls)
    // The base C struct already contains its own base fields (multi-level)
    for (FieldDecl *BaseField : BaseCStruct->fields()) {
      // Create new field with same type and name for derived struct
      FieldDecl *CField =
          Builder.fieldDecl(BaseField->getType(), BaseField->getName());
      fields.push_back(CField);
    }
  }
}

/**
 * Story #51: Base Constructor Chaining (Epic #6)
 *
 * Single Responsibility: Extract base constructor call logic from
 * VisitCXXConstructorDecl Open/Closed: Open for extension (virtual
 * inheritance), closed for modification
 *
 * Implementation Strategy:
 * 1. Iterate through constructor's member initializer list
 * 2. For each base class initializer:
 *    a. Extract the base class type
 *    b. Get the C constructor function from targetCtx.getCtorMap()
 *    c. Build argument list (this + initializer args)
 *    d. Create call expression to base constructor
 * 3. Add base constructor calls to statement list in order
 *
 * C++ Semantics:
 * - Base constructors are called BEFORE derived constructor body
 * - Base constructors are called in the order they appear in member init list
 * - For multi-level inheritance, each level calls its immediate parent only
 */
void CppToCVisitor::emitBaseConstructorCalls(CXXConstructorDecl *CD,
                                             ParmVarDecl *thisParam,
                                             std::vector<Stmt *> &stmts) {
  // Process base class initializers in order
  for (CXXCtorInitializer *Init : CD->inits()) {
    // Skip non-base initializers (member, delegating, etc.)
    if (!Init->isBaseInitializer()) {
      continue;
    }

    // Get the base class type from initializer
    QualType BaseType = Init->getBaseClass()->getCanonicalTypeInternal();
    CXXRecordDecl *BaseClass = BaseType->getAsCXXRecordDecl();

    // Edge case: Invalid base class
    if (!BaseClass) {
      llvm::outs() << "  Warning: Could not get base class, skipping\n";
      continue;
    }

    llvm::outs() << "  Translating base class initializer: "
                 << BaseClass->getName() << "\n";

    // Get the init expression (should be CXXConstructExpr)
    Expr *BaseInit = Init->getInit();
    CXXConstructExpr *CtorExpr = dyn_cast_or_null<CXXConstructExpr>(BaseInit);

    // Edge case: Not a constructor expression
    if (!CtorExpr) {
      llvm::outs() << "  Warning: Base initializer is not a CXXConstructExpr\n";
      continue;
    }

    // Get the base class constructor declaration
    CXXConstructorDecl *BaseCtorDecl = CtorExpr->getConstructor();

    // Lookup the C function for this base constructor
    std::string baseCtorKey = Mangler.mangleConstructor(BaseCtorDecl);
    auto it = targetCtx.getCtorMap().find(baseCtorKey);
    if (it == targetCtx.getCtorMap().end()) {
      llvm::outs() << "  Warning: Base constructor function not found\n";
      continue;
    }

    FunctionDecl *BaseCFunc = it->second;

    // Build argument list for base constructor call
    std::vector<Expr *> baseArgs;

    // First argument: this pointer
    // No explicit cast needed - base class fields are at offset 0 (Story #50)
    baseArgs.push_back(Builder.ref(thisParam));

    // Remaining arguments: from base initializer expression
    for (unsigned i = 0; i < CtorExpr->getNumArgs(); i++) {
      Expr *Arg = CtorExpr->getArg(i);
      Expr *TranslatedArg = translateExpr(Arg);
      if (TranslatedArg) {
        baseArgs.push_back(TranslatedArg);
      }
    }

    // Create the base constructor call expression
    CallExpr *BaseCall = Builder.call(BaseCFunc, baseArgs);
    if (BaseCall) {
      stmts.push_back(BaseCall);
      llvm::outs() << "  -> Added base constructor call to "
                   << BaseCFunc->getNameAsString() << "\n";
    }
  }
}

/**
 * Story #52: Base Destructor Chaining (Epic #6)
 *
 * Single Responsibility: Extract base destructor call logic from
 * VisitCXXDestructorDecl Open/Closed: Open for extension (virtual inheritance),
 * closed for modification
 *
 * Implementation Strategy:
 * 1. Get the derived class's base classes
 * 2. For each base class:
 *    a. Find the base destructor in targetCtx.getDtorMap()
 *    b. Create call to base destructor with 'this' pointer
 *    c. Append to statement list
 * 3. Base destructors called in order (for single inheritance, only one base)
 *
 * C++ Semantics:
 * - Base destructors are called AFTER derived destructor body
 * - Destruction order is REVERSE of construction order
 * - For multi-level inheritance, each level calls its immediate parent only
 */
void CppToCVisitor::emitBaseDestructorCalls(CXXDestructorDecl *DD,
                                            ParmVarDecl *thisParam,
                                            std::vector<Stmt *> &stmts) {
  CXXRecordDecl *DerivedClass = DD->getParent();

  // Process each direct base class
  for (const CXXBaseSpecifier &Base : DerivedClass->bases()) {
    CXXRecordDecl *BaseClass = Base.getType()->getAsCXXRecordDecl();

    // Edge case: Invalid base class
    if (!BaseClass || !BaseClass->isCompleteDefinition()) {
      continue;
    }

    llvm::outs() << "  Emitting base destructor call for: "
                 << BaseClass->getName() << "\n";

    // Get the base class destructor
    CXXDestructorDecl *BaseDtor = BaseClass->getDestructor();
    if (!BaseDtor) {
      llvm::outs() << "  Warning: Base class has no destructor\n";
      continue;
    }

    // Lookup the C function for this base destructor
    std::string baseDtorKey = Mangler.mangleDestructor(BaseDtor);
    auto it = targetCtx.getDtorMap().find(baseDtorKey);
    if (it == targetCtx.getDtorMap().end()) {
      llvm::outs() << "  Warning: Base destructor function not found\n";
      continue;
    }

    FunctionDecl *BaseDFunc = it->second;

    // Build argument list: just 'this' pointer
    std::vector<Expr *> baseArgs;
    baseArgs.push_back(Builder.ref(thisParam));

    // Create the base destructor call expression
    CallExpr *BaseCall = Builder.call(BaseDFunc, baseArgs);
    if (BaseCall) {
      stmts.push_back(BaseCall);
      llvm::outs() << "  -> Added base destructor call to "
                   << BaseDFunc->getNameAsString() << "\n";
    }
  }
}

// ============================================================================
// Story #63: Complete Constructor/Destructor Chaining Helper Methods
// ============================================================================

// Helper: Find initializer for a specific field in constructor init list
CXXCtorInitializer *
CppToCVisitor::findInitializerForField(CXXConstructorDecl *CD,
                                       FieldDecl *Field) {
  for (CXXCtorInitializer *Init : CD->inits()) {
    if (Init->isAnyMemberInitializer() && Init->getAnyMember() == Field) {
      return Init;
    }
  }
  return nullptr;
}

// Emit member constructor calls in declaration order
void CppToCVisitor::emitMemberConstructorCalls(CXXConstructorDecl *CD,
                                               ParmVarDecl *thisParam,
                                               std::vector<Stmt *> &stmts) {
  CXXRecordDecl *ClassDecl = CD->getParent();

  // Iterate fields in DECLARATION order (not init list order)
  for (FieldDecl *Field : ClassDecl->fields()) {
    QualType fieldType = Field->getType();

    // Check if field has initializer in init list
    CXXCtorInitializer *Init = findInitializerForField(CD, Field);

    if (fieldType->isRecordType()) {
      // Class-type member: needs constructor call
      const RecordType *RT = fieldType->getAs<RecordType>();
      CXXRecordDecl *FieldClass = dyn_cast<CXXRecordDecl>(RT->getDecl());

      if (!FieldClass || !FieldClass->hasDefinition()) {
        continue;
      }

      if (Init) {
        // Has explicit initializer: inner(val) or inner = other
        Expr *InitExpr = Init->getInit();

        if (CXXConstructExpr *CE = dyn_cast<CXXConstructExpr>(InitExpr)) {
          // Constructor call: inner(val)
          CXXConstructorDecl *MemberCtor = CE->getConstructor();

          // Lookup the C constructor function
          std::string memberCtorKey = Mangler.mangleConstructor(MemberCtor);
          auto it = targetCtx.getCtorMap().find(memberCtorKey);
          if (it == targetCtx.getCtorMap().end()) {
            llvm::outs()
                << "  Warning: Member constructor function not found\n";
            continue;
          }

          FunctionDecl *MemberCFunc = it->second;

          // Build argument list: &this->field, arg1, arg2, ...
          MemberExpr *ThisMember =
              Builder.arrowMember(Builder.ref(thisParam), Field->getName());
          Expr *memberAddr = Builder.addrOf(ThisMember);

          std::vector<Expr *> args;
          args.push_back(memberAddr);

          for (const Expr *Arg : CE->arguments()) {
            args.push_back(translateExpr(const_cast<Expr *>(Arg)));
          }

          CallExpr *ctorCall = Builder.call(MemberCFunc, args);
          stmts.push_back(ctorCall);

        } else {
          // Copy/assignment: inner = other or inner(other) for copy
          // Treat as assignment for now
          MemberExpr *ThisMember =
              Builder.arrowMember(Builder.ref(thisParam), Field->getName());
          Expr *TranslatedExpr = translateExpr(InitExpr);
          BinaryOperator *Assignment =
              Builder.assign(ThisMember, TranslatedExpr);
          stmts.push_back(Assignment);
        }
      } else {
        // No initializer: call default constructor
        // Find default constructor
        CXXConstructorDecl *DefaultCtor = nullptr;
        for (CXXConstructorDecl *Ctor : FieldClass->ctors()) {
          if (Ctor->isDefaultConstructor()) {
            DefaultCtor = Ctor;
            break;
          }
        }

        if (DefaultCtor) {
          // Lookup the C constructor function
          std::string defaultCtorKey = Mangler.mangleConstructor(DefaultCtor);
          auto it = targetCtx.getCtorMap().find(defaultCtorKey);
          if (it != targetCtx.getCtorMap().end()) {
            FunctionDecl *MemberCFunc = it->second;

            MemberExpr *ThisMember =
                Builder.arrowMember(Builder.ref(thisParam), Field->getName());
            Expr *memberAddr = Builder.addrOf(ThisMember);

            CallExpr *ctorCall = Builder.call(MemberCFunc, {memberAddr});
            stmts.push_back(ctorCall);
          }
        }
      }
    } else {
      // Primitive member: use assignment if has initializer
      if (Init) {
        MemberExpr *ThisMember =
            Builder.arrowMember(Builder.ref(thisParam), Field->getName());
        Expr *TranslatedExpr = translateExpr(Init->getInit());
        BinaryOperator *Assignment = Builder.assign(ThisMember, TranslatedExpr);
        stmts.push_back(Assignment);
      }
    }
  }
}

// Emit member destructor calls in reverse declaration order
void CppToCVisitor::emitMemberDestructorCalls(CXXRecordDecl *ClassDecl,
                                              ParmVarDecl *thisParam,
                                              std::vector<Stmt *> &stmts) {
  // Collect fields with non-trivial destructors
  std::vector<FieldDecl *> fieldsToDestroy;

  for (FieldDecl *Field : ClassDecl->fields()) {
    if (hasNonTrivialDestructor(Field->getType())) {
      fieldsToDestroy.push_back(Field);
    }
  }

  // Destroy in REVERSE declaration order
  for (auto it = fieldsToDestroy.rbegin(); it != fieldsToDestroy.rend(); ++it) {
    FieldDecl *Field = *it;
    QualType fieldType = Field->getType();

    // Get destructor for member type
    const RecordType *RT = fieldType->getAs<RecordType>();
    if (!RT)
      continue;

    CXXRecordDecl *FieldClass = dyn_cast<CXXRecordDecl>(RT->getDecl());
    if (!FieldClass || !FieldClass->hasDefinition())
      continue;

    CXXDestructorDecl *FieldDtor = FieldClass->getDestructor();
    if (!FieldDtor)
      continue;

    // Lookup the C destructor function
    std::string fieldDtorKey = Mangler.mangleDestructor(FieldDtor);
    auto it2 = targetCtx.getDtorMap().find(fieldDtorKey);
    if (it2 == targetCtx.getDtorMap().end()) {
      continue;
    }

    FunctionDecl *FieldDFunc = it2->second;

    // Build: FieldDtor(&this->field)
    MemberExpr *ThisMember =
        Builder.arrowMember(Builder.ref(thisParam), Field->getName());
    Expr *memberAddr = Builder.addrOf(ThisMember);
    CallExpr *dtorCall = Builder.call(FieldDFunc, {memberAddr});
    stmts.push_back(dtorCall);
  }
}

// ============================================================================
// Epic #5: RAII Helper Methods
// ============================================================================

// Story #45: Visit return statements for early return detection
bool CppToCVisitor::VisitReturnStmt(ReturnStmt *RS) {
  // Skip if not analyzing a function
  if (currentFunctionObjectsToDestroy.empty()) {
    return true;
  }

  llvm::outs() << "  Detected return statement for early return analysis\n";

  // Track this return statement (we'll analyze scope later during translation)
  ReturnInfo info;
  info.returnStmt = RS;
  // Live objects will be determined during translation phase
  currentFunctionReturns.push_back(info);

  return true;
}

// Story #45: Analyze which objects are live at a specific return point
std::vector<VarDecl *>
CppToCVisitor::analyzeLiveObjectsAtReturn(ReturnStmt *RS, FunctionDecl *FD) {

  std::vector<VarDecl *> liveObjects;

  if (!FD || !RS) {
    return liveObjects;
  }

  // Get source location of the return statement
  SourceLocation returnLoc = RS->getBeginLoc();

  llvm::outs() << "  Analyzing live objects at return statement...\n";

  // For each object with a destructor in the function
  for (VarDecl *VD : currentFunctionObjectsToDestroy) {
    SourceLocation varLoc = VD->getBeginLoc();

    // Check if variable is declared before the return statement
    if (varLoc.isValid() && returnLoc.isValid()) {
      // Use source manager to compare locations
      SourceManager &SM = Context.getSourceManager();

      // Variable must be declared before return to be live
      if (SM.isBeforeInTranslationUnit(varLoc, returnLoc)) {
        // Additional check: ensure variable is in scope at return point
        // For now, we assume lexical ordering implies scope
        // TODO: More sophisticated scope analysis for nested blocks

        liveObjects.push_back(VD);
        llvm::outs() << "    Variable '" << VD->getNameAsString()
                     << "' is live at return\n";
      }
    }
  }

  return liveObjects;
}

// Story #45: Check if one statement comes before another
bool CppToCVisitor::comesBefore(Stmt *Before, Stmt *After) {
  if (!Before || !After) {
    return false;
  }

  SourceLocation beforeLoc = Before->getBeginLoc();
  SourceLocation afterLoc = After->getBeginLoc();

  if (!beforeLoc.isValid() || !afterLoc.isValid()) {
    return false;
  }

  SourceManager &SM = Context.getSourceManager();
  return SM.isBeforeInTranslationUnit(beforeLoc, afterLoc);
}

// ============================================================================
// Story #46: Nested Scope Tracking Methods
// ============================================================================

// Enter a new scope (push onto scope stack)
void CppToCVisitor::enterScope(CompoundStmt *CS) {
  ScopeInfo info;
  info.stmt = CS;
  info.depth = scopeStack.size(); // Current stack size is the depth
  // objects vector starts empty

  scopeStack.push_back(info);

  llvm::outs() << "  [Scope] Entering scope at depth " << info.depth << "\n";
}

// Exit current scope (pop from scope stack)
CppToCVisitor::ScopeInfo CppToCVisitor::exitScope() {
  if (scopeStack.empty()) {
    llvm::errs() << "Warning: Attempting to exit scope when stack is empty\n";
    return ScopeInfo{nullptr, {}, 0};
  }

  ScopeInfo info = scopeStack.back();
  scopeStack.pop_back();

  llvm::outs() << "  [Scope] Exiting scope at depth " << info.depth << " with "
               << info.objects.size() << " objects\n";

  return info;
}

// Track a variable declaration in the current scope
void CppToCVisitor::trackObjectInCurrentScope(VarDecl *VD) {
  if (scopeStack.empty()) {
    llvm::outs() << "  [Scope] Warning: No active scope to track object in\n";
    return;
  }

  // Add to the current (top) scope
  scopeStack.back().objects.push_back(VD);

  llvm::outs() << "  [Scope] Tracked object '" << VD->getNameAsString()
               << "' in scope depth " << scopeStack.back().depth << "\n";
}

// ============================================================================
// Story #47: Goto Statement Handling Methods
// ============================================================================

// Visit goto statements for detection and tracking
bool CppToCVisitor::VisitGotoStmt(GotoStmt *GS) {
  // Skip if not analyzing a function
  if (currentFunctionObjectsToDestroy.empty()) {
    return true;
  }

  llvm::outs() << "  [Goto] Detected goto to label: "
               << GS->getLabel()->getName() << "\n";

  // Store goto statement for later analysis
  GotoInfo info;
  info.gotoStmt = GS;
  info.targetLabel = nullptr; // Will be matched in analyzeGotoStatements()
  currentFunctionGotos.push_back(info);

  return true;
}

// Visit label statements for detection and tracking
bool CppToCVisitor::VisitLabelStmt(LabelStmt *LS) {
  // Skip if not analyzing a function
  if (currentFunctionObjectsToDestroy.empty()) {
    return true;
  }

  std::string labelName = LS->getName();
  llvm::outs() << "  [Goto] Detected label: " << labelName << "\n";

  // Store label for goto matching
  currentFunctionLabels[labelName] = LS;

  return true;
}

// Analyze goto-label pairs and determine objects needing destruction
void CppToCVisitor::analyzeGotoStatements(FunctionDecl *FD) {
  if (currentFunctionGotos.empty()) {
    return; // No gotos to analyze
  }

  llvm::outs() << "  [Goto] Analyzing " << currentFunctionGotos.size()
               << " goto statement(s)\n";

  // Match each goto to its target label
  for (GotoInfo &info : currentFunctionGotos) {
    std::string labelName = info.gotoStmt->getLabel()->getName().str();

    // Find matching label
    auto it = currentFunctionLabels.find(labelName);
    if (it == currentFunctionLabels.end()) {
      llvm::errs() << "  [Goto] Warning: Label '" << labelName
                   << "' not found for goto\n";
      continue;
    }

    info.targetLabel = it->second;

    // Check if this is a forward jump
    if (isForwardJump(info.gotoStmt, info.targetLabel)) {
      llvm::outs() << "  [Goto] Forward jump to '" << labelName << "'\n";

      // Analyze which objects need destruction
      info.liveObjects =
          analyzeObjectsForGoto(info.gotoStmt, info.targetLabel, FD);

      llvm::outs() << "    -> " << info.liveObjects.size()
                   << " object(s) need destruction before goto\n";
    } else {
      llvm::outs() << "  [Goto] Backward jump to '" << labelName
                   << "' (no destructor injection)\n";
      // Backward jumps: objects remain alive, no destruction needed
    }
  }
}

// Check if goto comes before its target label (forward jump)
bool CppToCVisitor::isForwardJump(GotoStmt *gotoStmt, LabelStmt *labelStmt) {
  if (!gotoStmt || !labelStmt) {
    return false;
  }

  SourceManager &SM = Context.getSourceManager();
  SourceLocation gotoLoc = gotoStmt->getBeginLoc();
  SourceLocation labelLoc = labelStmt->getBeginLoc();

  // Forward jump: goto comes before label in source
  return SM.isBeforeInTranslationUnit(gotoLoc, labelLoc);
}

// Determine which objects are live at goto and out of scope at label
std::vector<VarDecl *>
CppToCVisitor::analyzeObjectsForGoto(GotoStmt *gotoStmt, LabelStmt *labelStmt,
                                     FunctionDecl *FD) {

  std::vector<VarDecl *> objectsToDestroy;

  if (!gotoStmt || !labelStmt || !FD) {
    return objectsToDestroy;
  }

  SourceManager &SM = Context.getSourceManager();
  SourceLocation gotoLoc = gotoStmt->getBeginLoc();
  SourceLocation labelLoc = labelStmt->getBeginLoc();

  // For each tracked object in the function
  for (VarDecl *VD : currentFunctionObjectsToDestroy) {
    SourceLocation varLoc = VD->getBeginLoc();

    // Object is live at goto if:
    // 1. It's declared before the goto
    // 2. It needs destruction (already filtered in tracking)
    if (SM.isBeforeInTranslationUnit(varLoc, gotoLoc)) {
      // For forward jumps, all objects constructed before goto need destruction
      // (This is a simplified analysis - a full implementation would check
      //  exact scope boundaries to determine if object is still in scope at
      //  label)
      objectsToDestroy.push_back(VD);
      llvm::outs() << "      - Will destroy: " << VD->getNameAsString() << "\n";
    }
  }

  return objectsToDestroy;
}

// ============================================================================
// Story #48: Loop Break/Continue Handling Methods
// ============================================================================

// Visit break statements for detection and tracking
bool CppToCVisitor::VisitBreakStmt(BreakStmt *BS) {
  // Skip if not analyzing a function
  if (currentFunctionObjectsToDestroy.empty() && scopeStack.empty()) {
    return true;
  }

  // Only track breaks inside loops (loopNestingLevel > 0)
  // Breaks in switch statements (loopNestingLevel == 0) are not tracked
  if (loopNestingLevel == 0) {
    llvm::outs()
        << "  [Break] Detected break in switch (no destructor injection)\n";
    return true;
  }

  llvm::outs() << "  [Break] Detected break in loop (nesting level: "
               << loopNestingLevel << ")\n";

  // Store break statement for later analysis
  BreakContinueInfo info;
  info.stmt = BS;
  info.isBreak = true;
  currentFunctionBreaksContinues.push_back(info);

  return true;
}

// Visit continue statements for detection and tracking
bool CppToCVisitor::VisitContinueStmt(ContinueStmt *CS) {
  // Skip if not analyzing a function
  if (currentFunctionObjectsToDestroy.empty() && scopeStack.empty()) {
    return true;
  }

  // Continue is only valid inside loops
  if (loopNestingLevel == 0) {
    llvm::errs()
        << "  [Continue] Warning: Continue outside loop (should not happen)\n";
    return true;
  }

  llvm::outs() << "  [Continue] Detected continue in loop (nesting level: "
               << loopNestingLevel << ")\n";

  // Store continue statement for later analysis
  BreakContinueInfo info;
  info.stmt = CS;
  info.isBreak = false;
  currentFunctionBreaksContinues.push_back(info);

  return true;
}

// Visit while statements to track loop nesting
bool CppToCVisitor::VisitWhileStmt(WhileStmt *WS) {
  // Don't increment here - we'll do it during traversal
  // This is just a marker visitor

  // Epic #193: Generate ACSL loop invariants if enabled
  if (m_loopAnnotator && getACSLLevel() == ACSLLevel::Full) {
    std::string loopInvariant = m_loopAnnotator->generateLoopAnnotations(WS);
    if (!loopInvariant.empty()) {
      emitACSL(loopInvariant, getACSLOutputMode());
    }
  }

  return true;
}

// Visit for statements to track loop nesting
bool CppToCVisitor::VisitForStmt(ForStmt *FS) {
  // Don't increment here - we'll do it during traversal
  // This is just a marker visitor

  // Epic #193: Generate ACSL loop invariants if enabled
  if (m_loopAnnotator && getACSLLevel() == ACSLLevel::Full) {
    std::string loopInvariant = m_loopAnnotator->generateLoopAnnotations(FS);
    if (!loopInvariant.empty()) {
      emitACSL(loopInvariant, getACSLOutputMode());
    }
  }

  return true;
}

// Visit do statements to track loop nesting
bool CppToCVisitor::VisitDoStmt(DoStmt *DS) {
  // Don't increment here - we'll do it during traversal
  // This is just a marker visitor

  // Epic #193: Generate ACSL loop invariants if enabled
  if (m_loopAnnotator && getACSLLevel() == ACSLLevel::Full) {
    std::string loopInvariant = m_loopAnnotator->generateLoopAnnotations(DS);
    if (!loopInvariant.empty()) {
      emitACSL(loopInvariant, getACSLOutputMode());
    }
  }

  return true;
}

// Visit range-based for statements to track loop nesting
bool CppToCVisitor::VisitCXXForRangeStmt(CXXForRangeStmt *FRS) {
  // Don't increment here - we'll do it during traversal
  // This is just a marker visitor

  // Epic #193: Note - CXXForRangeStmt not yet supported by ACSLLoopAnnotator
  // TODO: Add generateLoopAnnotations(const clang::CXXForRangeStmt *loop)
  // overload to ACSLLoopAnnotator

  return true;
}

// Analyze break/continue statements and determine objects needing destruction
void CppToCVisitor::analyzeBreakContinueStatements(FunctionDecl *FD) {
  if (currentFunctionBreaksContinues.empty()) {
    return; // No breaks/continues to analyze
  }

  llvm::outs() << "  [Break/Continue] Analyzing "
               << currentFunctionBreaksContinues.size()
               << " break/continue statement(s)\n";

  // For each break/continue statement
  for (BreakContinueInfo &info : currentFunctionBreaksContinues) {
    const char *stmtType = info.isBreak ? "break" : "continue";

    // Analyze which objects need destruction
    info.liveObjects = analyzeObjectsForBreakContinue(info.stmt, FD);

    llvm::outs() << "  [" << stmtType << "] " << info.liveObjects.size()
                 << " object(s) need destruction before " << stmtType << "\n";
  }
}

// Determine which objects are live at break/continue and need destruction
std::vector<VarDecl *>
CppToCVisitor::analyzeObjectsForBreakContinue(Stmt *stmt, FunctionDecl *FD) {

  std::vector<VarDecl *> objectsToDestroy;

  if (!stmt || !FD) {
    return objectsToDestroy;
  }

  SourceManager &SM = Context.getSourceManager();
  SourceLocation stmtLoc = stmt->getBeginLoc();

  // For break/continue: destroy all loop-local objects that are live at this
  // point This includes:
  // 1. Objects declared in the loop body before this statement
  // 2. Objects declared in nested scopes that are still alive
  //
  // Simplified approach: Destroy all objects constructed before the
  // break/continue

  for (VarDecl *VD : currentFunctionObjectsToDestroy) {
    SourceLocation varLoc = VD->getBeginLoc();

    // Object is live at break/continue if:
    // 1. It's declared before the break/continue
    // 2. It has a destructor (already filtered in tracking)
    if (SM.isBeforeInTranslationUnit(varLoc, stmtLoc)) {
      objectsToDestroy.push_back(VD);
      llvm::outs() << "      - Will destroy: " << VD->getNameAsString() << "\n";
    }
  }

  return objectsToDestroy;
}

// Visit compound statements for scope tracking
bool CppToCVisitor::VisitCompoundStmt(CompoundStmt *CS) {
  // We don't enter scope here because VisitCompoundStmt is called
  // during traversal, but we need to handle scope entry/exit during
  // translation (in translateCompoundStmt) to properly inject destructors
  // This visitor is just for detection/analysis if needed
  return true;
}

// Helper: Check if type has non-trivial destructor
bool CppToCVisitor::hasNonTrivialDestructor(QualType type) const {
  // Remove qualifiers and get canonical type
  type = type.getCanonicalType();
  type.removeLocalConst();

  // Check if it's a record type (class/struct)
  const RecordType *RT = type->getAs<RecordType>();
  if (!RT) {
    return false;
  }

  RecordDecl *RD = RT->getDecl();
  CXXRecordDecl *CXXRD = dyn_cast<CXXRecordDecl>(RD);

  if (!CXXRD) {
    return false; // C struct, no destructor
  }

  // Check if destructor exists and is non-trivial
  if (!CXXRD->hasDefinition()) {
    return false;
  }

  return CXXRD->hasNonTrivialDestructor();
}

// Bug #8: Check if a statement contains RecoveryExpr (parsing errors)
// This recursively checks if any expression in the statement tree is RecoveryExpr
bool CppToCVisitor::containsRecoveryExpr(Stmt *S) {
  if (!S) {
    return false;
  }

  // Check if this statement itself is a RecoveryExpr
  if (isa<RecoveryExpr>(S)) {
    return true;
  }

  // CRITICAL FIX for Bug #X (Empty C files):
  // Do NOT recurse into nested CompoundStmts - they handle their own filtering.
  // This prevents skipping entire if/while/for blocks just because they contain
  // a RecoveryExpr somewhere deep inside.
  //
  // Each CompoundStmt independently filters its own statements, creating a
  // hierarchy of filtering rather than all-or-nothing.
  if (isa<CompoundStmt>(S)) {
    // Don't recurse into compound statements - they filter themselves
    return false;
  }

  // Recursively check all child statements/expressions (except CompoundStmts)
  for (Stmt *Child : S->children()) {
    if (containsRecoveryExpr(Child)) {
      return true;
    }
  }

  return false;
}

// Helper: Create destructor call for a variable
CallExpr *CppToCVisitor::createDestructorCall(VarDecl *VD) {
  QualType type = VD->getType();
  const RecordType *RT = type->getAs<RecordType>();
  if (!RT) {
    return nullptr;
  }

  CXXRecordDecl *CXXRD = dyn_cast<CXXRecordDecl>(RT->getDecl());
  if (!CXXRD || !CXXRD->hasDefinition()) {
    return nullptr;
  }

  CXXDestructorDecl *Dtor = CXXRD->getDestructor();
  if (!Dtor) {
    return nullptr;
  }

  // Find the C destructor function
  FunctionDecl *CDtor = nullptr;
  std::string dtorKey = Mangler.mangleDestructor(Dtor);
  if (targetCtx.getDtorMap().find(dtorKey) != targetCtx.getDtorMap().end()) {
    CDtor = targetCtx.getDtorMap()[dtorKey];
  }

  if (!CDtor) {
    // Destructor not yet translated, this might happen in multi-pass scenarios
    llvm::outs() << "  Warning: Destructor for " << CXXRD->getName()
                 << " not found in mapping\n";
    return nullptr;
  }

  // Create call: ClassName__dtor(&var)
  Expr *VarRef = Builder.ref(VD);
  Expr *AddrOf = Builder.addrOf(VarRef);

  return Builder.call(CDtor, {AddrOf});
}

// Helper: Inject destructors at scope exit
void CppToCVisitor::injectDestructorsAtScopeExit(
    CompoundStmt *CS, const std::vector<VarDecl *> &vars) {
  if (vars.empty()) {
    return;
  }

  // Get existing statements
  std::vector<Stmt *> stmts;
  for (Stmt *S : CS->body()) {
    stmts.push_back(S);
  }

  // Inject destructors in reverse construction order (LIFO)
  for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
    CallExpr *DtorCall = createDestructorCall(*it);
    if (DtorCall) {
      stmts.push_back(DtorCall);
      llvm::outs() << "  Injected destructor call for: "
                   << (*it)->getNameAsString() << "\n";
    }
  }

  // Note: In a real implementation, we'd need to replace the CompoundStmt
  // For now, this demonstrates the logic
  // Actual replacement would require TreeTransform or similar
}

// ============================================================================
// Story #19: Member Access Transformation - Expression Translation
// ============================================================================

// Main expression translation dispatcher
Expr *CppToCVisitor::translateExpr(Expr *E) {
  if (!E)
    return nullptr;

  // Bug #37: Handle ConstantExpr - unwrap and translate subexpression
  // ConstantExpr appears in case labels: case GameState::Menu
  // Unwrap to get the DeclRefExpr and translate it
  if (ConstantExpr *CE = dyn_cast<ConstantExpr>(E)) {
    return translateExpr(CE->getSubExpr());
  }

  // Dispatch to specific translators based on expression type
  if (MemberExpr *ME = dyn_cast<MemberExpr>(E)) {
    return translateMemberExpr(ME);
  }

  if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(E)) {
    return translateDeclRefExpr(DRE);
  }

  // Story #172: Handle virtual method calls (must be checked BEFORE CallExpr)
  if (CXXMemberCallExpr *MCE = dyn_cast<CXXMemberCallExpr>(E)) {
    // Check if this is a virtual call
    if (m_virtualCallTrans->isVirtualCall(MCE)) {
      llvm::outs() << "  Translating virtual method call\n";
      // For now, just pass through - full translation would convert to:
      // obj->vptr->method(obj, args...)
      // This requires generating the appropriate vtable access code
    }
    // Fall through to translateCallExpr for now
  }

  if (CallExpr *CE = dyn_cast<CallExpr>(E)) {
    return translateCallExpr(CE);
  }

  if (BinaryOperator *BO = dyn_cast<BinaryOperator>(E)) {
    return translateBinaryOperator(BO);
  }

  // Handle constructor expressions - need to translate arguments
  if (CXXConstructExpr *CCE = dyn_cast<CXXConstructExpr>(E)) {
    return translateConstructExpr(CCE);
  }

  // Bug fix: Handle C++ new operator - convert to malloc()
  // Example: new Node(value) → malloc(sizeof(struct Node_int))
  if (CXXNewExpr *NE = dyn_cast<CXXNewExpr>(E)) {
    llvm::outs() << "  Translating CXXNewExpr to malloc()\n";

    // Get the allocated type
    QualType AllocatedType = NE->getAllocatedType();

    // Bug #38 FIX: Check if this is a nested class that needs substitution
    // E.g., "new Node()" -> "malloc(sizeof(struct LinkedList_int_Node))"
    if (currentNestedClassMappings && AllocatedType->isRecordType()) {
      const RecordType *RT = AllocatedType->getAs<RecordType>();
      RecordDecl *RD = RT->getDecl();
      std::string typeName = RD->getNameAsString();

      auto it = currentNestedClassMappings->find(typeName);
      if (it != currentNestedClassMappings->end()) {
        // Found it! Replace with monomorphized type
        std::string monomorphizedName = it->second;
        llvm::outs() << "      Substituting new expression type: new " << typeName
                     << "() -> malloc(sizeof(struct " << monomorphizedName << "))\n";

        // Create the monomorphized struct type
        IdentifierInfo &II = Context.Idents.get(monomorphizedName);
        RecordDecl *CRecord = RecordDecl::Create(
            Context,
#if LLVM_VERSION_MAJOR >= 16
            TagTypeKind::Struct,
#else
            TTK_Struct,
#endif
            Context.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            &II
        );

        AllocatedType = Context.getRecordType(CRecord);
      }
    }

    // Create malloc call: malloc(sizeof(Type))
    // 1. Create sizeof(Type) expression using UnaryExprOrTypeTraitExpr
    UnaryExprOrTypeTraitExpr *SizeOfExpr = new (Context) UnaryExprOrTypeTraitExpr(
        UETT_SizeOf,
        Context.getTrivialTypeSourceInfo(AllocatedType, SourceLocation()),
        Context.getSizeType(),
        SourceLocation(),
        SourceLocation()
    );

    // 2. Create malloc call using Builder (takes function name as string)
    std::vector<Expr*> MallocArgs;
    MallocArgs.push_back(SizeOfExpr);
    CallExpr *MallocCall = Builder.call("malloc", MallocArgs);

    // 3. Cast result to appropriate pointer type
    QualType ResultType = Context.getPointerType(AllocatedType);
    return ImplicitCastExpr::Create(Context, ResultType, CK_BitCast,
                                    MallocCall, nullptr, VK_PRValue,
                                    FPOptionsOverride());
  }

  // Bug fix: Handle C++ delete operator - convert to free()
  // Example: delete temp → free(temp)
  if (CXXDeleteExpr *DE = dyn_cast<CXXDeleteExpr>(E)) {
    llvm::outs() << "  Translating CXXDeleteExpr to free()\n";

    // Get the pointer being deleted
    Expr *Argument = DE->getArgument();
    Expr *TranslatedArg = translateExpr(Argument);
    if (!TranslatedArg) {
      TranslatedArg = Argument;
    }

    // Create free call using Builder (takes function name as string)
    std::vector<Expr*> FreeArgs;
    FreeArgs.push_back(TranslatedArg);
    return Builder.call("free", FreeArgs);
  }

  // Bug fix: Handle C++ nullptr literal - convert to NULL
  // Example: nullptr → NULL (which is ((void*)0) in C)
  if (CXXNullPtrLiteralExpr *NPE = dyn_cast<CXXNullPtrLiteralExpr>(E)) {
    llvm::outs() << "  Translating nullptr to NULL\n";

    // Create NULL as ((void*)0)
    // 1. Create integer literal 0
    llvm::APInt Zero(32, 0);
    IntegerLiteral *ZeroLit = IntegerLiteral::Create(
        Context, Zero, Context.IntTy, SourceLocation());

    // 2. Cast to void*
    QualType VoidPtrType = Context.getPointerType(Context.VoidTy);
    return ImplicitCastExpr::Create(Context, VoidPtrType, CK_NullToPointer,
                                    ZeroLit, nullptr, VK_PRValue,
                                    FPOptionsOverride());
  }

  // Handle implicit casts - just translate the sub-expression
  if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(E)) {
    Expr *SubExpr = ICE->getSubExpr();
    Expr *TranslatedSub = translateExpr(SubExpr);
    if (TranslatedSub && TranslatedSub != SubExpr) {
      // Create new implicit cast with translated sub-expression
      return ImplicitCastExpr::Create(Context, ICE->getType(), ICE->getCastKind(),
                                      TranslatedSub, nullptr, ICE->getValueKind(),
                                      FPOptionsOverride());
    }
    return ICE;
  }

  // Bug #13 fix: Handle ArraySubscriptExpr - translate base and index
  // This is critical for expressions like other.data[i] where other is a pointer parameter
  if (ArraySubscriptExpr *ASE = dyn_cast<ArraySubscriptExpr>(E)) {
    Expr *Base = ASE->getBase();
    Expr *Idx = ASE->getIdx();

    // Translate both base and index
    Expr *TranslatedBase = translateExpr(Base);
    Expr *TranslatedIdx = translateExpr(Idx);

    // If either changed, create a new ArraySubscriptExpr
    if ((TranslatedBase && TranslatedBase != Base) ||
        (TranslatedIdx && TranslatedIdx != Idx)) {
      Expr *NewBase = TranslatedBase ? TranslatedBase : Base;
      Expr *NewIdx = TranslatedIdx ? TranslatedIdx : Idx;

      // Create new ArraySubscriptExpr using Clang API
      return new (Context) ArraySubscriptExpr(
          NewBase, NewIdx, ASE->getType(),
          ASE->getValueKind(), ASE->getObjectKind(),
          ASE->getRBracketLoc());
    }
    return ASE;
  }

  // Bug #38 FIX: Handle sizeof expressions to substitute nested class types
  // E.g., sizeof(Node) -> sizeof(struct LinkedList_int_Node)
  if (UnaryExprOrTypeTraitExpr *UETTE = dyn_cast<UnaryExprOrTypeTraitExpr>(E)) {
    if (UETTE->getKind() == UETT_SizeOf && UETTE->isArgumentType()) {
      QualType ArgType = UETTE->getArgumentType();

      // Check if this is a nested class type that needs substitution
      if (currentNestedClassMappings && ArgType->isRecordType()) {
        const RecordType *RT = ArgType->getAs<RecordType>();
        RecordDecl *RD = RT->getDecl();
        std::string typeName = RD->getNameAsString();

        auto it = currentNestedClassMappings->find(typeName);
        if (it != currentNestedClassMappings->end()) {
          // Found it! Replace with monomorphized type
          std::string monomorphizedName = it->second;
          llvm::outs() << "      Substituting sizeof nested class: sizeof(" << typeName
                       << ") -> sizeof(struct " << monomorphizedName << ")\n";

          // Create the monomorphized struct type
          IdentifierInfo &II = Context.Idents.get(monomorphizedName);
          RecordDecl *CRecord = RecordDecl::Create(
              Context,
#if LLVM_VERSION_MAJOR >= 16
              TagTypeKind::Struct,
#else
              TTK_Struct,
#endif
              Context.getTranslationUnitDecl(),
              SourceLocation(),
              SourceLocation(),
              &II
          );

          QualType CStructType = Context.getRecordType(CRecord);

          // Create new sizeof expression with substituted type
          return new (Context) UnaryExprOrTypeTraitExpr(
              UETT_SizeOf,
              Context.getTrivialTypeSourceInfo(CStructType, SourceLocation()),
              Context.getSizeType(),
              SourceLocation(),
              SourceLocation()
          );
        }
      }
    }
    // No substitution needed, return as-is
    return UETTE;
  }

  // Bug fix #8: Handle RecoveryExpr from missing system headers
  // RecoveryExpr is created when Clang can't parse something (e.g., missing <cstdio>)
  // Try to extract the underlying call expression if possible
  if (RecoveryExpr *RE = dyn_cast<RecoveryExpr>(E)) {
    llvm::outs() << "  Warning: RecoveryExpr encountered (parsing error)\n";

    // RecoveryExpr contains sub-expressions that were partially parsed
    // For function calls like printf(...), the sub-expressions are the arguments
    ArrayRef<Expr *> SubExprs = RE->subExpressions();

    if (SubExprs.size() > 0) {
      // First sub-expression is usually the function name (as DeclRefExpr)
      Expr *FirstExpr = SubExprs[0];

      // Check if it's a function call pattern
      if (DeclRefExpr *FuncRef = dyn_cast<DeclRefExpr>(FirstExpr)) {
        std::string FuncName = FuncRef->getDecl()->getNameAsString();
        llvm::outs() << "  RecoveryExpr appears to be call to: " << FuncName << "\n";

        // Create a CallExpr from the recovered pieces
        std::vector<Expr *> Args;
        // Arguments start from index 1
        for (unsigned i = 1; i < SubExprs.size(); ++i) {
          Expr *TranslatedArg = translateExpr(SubExprs[i]);
          Args.push_back(TranslatedArg ? TranslatedArg : SubExprs[i]);
        }

        // Create a function declaration for the call
        // We assume it returns int (common for printf, etc.)
        QualType RetType = Context.IntTy;
        std::vector<ParmVarDecl *> Params;

        // Create function decl
        FunctionDecl *FuncDecl = Builder.funcDecl(FuncName, RetType, Params, nullptr);

        // Create call expression
        CallExpr *Call = Builder.call(FuncDecl, Args);
        if (Call) {
          llvm::outs() << "  Successfully reconstructed call to " << FuncName << "\n";
          return Call;
        }
      }
    }

    // If we can't reconstruct it, return nullptr to skip it
    llvm::outs() << "  Skipping RecoveryExpr (cannot reconstruct)\n";
    return nullptr;
  }

  // Bug #42: Handle ParenExpr - translate subexpression and recreate ParenExpr
  if (ParenExpr *PE = dyn_cast<ParenExpr>(E)) {
    Expr *SubExpr = PE->getSubExpr();
    Expr *TranslatedSubExpr = translateExpr(SubExpr);
    if (TranslatedSubExpr && TranslatedSubExpr != SubExpr) {
      return new (Context) ParenExpr(SourceLocation(), SourceLocation(), TranslatedSubExpr);
    }
    return PE;  // Return original if subexpr unchanged
  }

  // Default: return expression as-is (literals, etc.)
  return E;
}

// Translate DeclRefExpr - handles implicit 'this'
Expr *CppToCVisitor::translateDeclRefExpr(DeclRefExpr *DRE) {
  ValueDecl *D = DRE->getDecl();

  // Bug #37 FIX: Translate scoped enum references to use C naming convention
  // In C++: GameState::Menu (with NestedNameSpecifier)
  // In C: GameState__Menu (scoped enum) or integer literal (unscoped enum)
  if (EnumConstantDecl *ECD = dyn_cast<EnumConstantDecl>(D)) {
    // Check if this C++ enum constant has been mapped to a C enum constant
    auto it = enumConstantMap.find(ECD);
    if (it != enumConstantMap.end()) {
      // Scoped enum: use the mapped C enum constant
      EnumConstantDecl *CECD = it->second;
      llvm::outs() << "  Translating scoped enum ref: " << ECD->getName()
                   << " -> " << CECD->getName() << "\n";

      // Create a DeclRefExpr to the C enum constant
      return Builder.ref(CECD);
    } else {
      // Bug #28: Unscoped enum - keep as integer literal for backward compatibility
      llvm::APSInt Value = ECD->getInitVal();
      return Builder.intLit(Value.getExtValue());
    }
  }

  // Check if this is an implicit member access (field without explicit this)
  if (FieldDecl *FD = dyn_cast<FieldDecl>(D)) {
    // We're inside a method body, convert 'x' to 'this->x'
    if (currentThisParam) {
      llvm::outs() << "  Translating implicit member access: " << FD->getName()
                   << " -> this->" << FD->getName() << "\n";

      return Builder.arrowMember(Builder.ref(currentThisParam), FD->getName());
    }
  }

  // Regular variable reference - return as-is
  return DRE;
}

// Translate MemberExpr - handles explicit member access
Expr *CppToCVisitor::translateMemberExpr(MemberExpr *ME) {
  Expr *Base = ME->getBase();
  ValueDecl *Member = ME->getMemberDecl();

  // Translate base recursively
  Expr *TranslatedBase = translateExpr(Base);

  // If translation failed, return original expression
  if (!TranslatedBase) {
    return ME;
  }

  // Determine if we need -> or . based on the base type
  // Key insight: We need to check if the base refers to a reference parameter,
  // even if it's been implicitly cast. Strip implicit casts to find the real base.
  Expr *UnstrippedBase = Base;
  while (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(UnstrippedBase)) {
    UnstrippedBase = ICE->getSubExpr();
  }

  bool useArrow = false;
  QualType TranslatedBaseType = TranslatedBase->getType();
  QualType OriginalBaseType = Base->getType();

  // Check if base is a pointer
  if (TranslatedBaseType->isPointerType() || OriginalBaseType->isPointerType()) {
    useArrow = true;
  }
  // Check if base is a reference
  if (OriginalBaseType->isReferenceType()) {
    useArrow = true;
  }
  // Bug #13: Check if base is a DeclRef to a reference/pointer parameter
  // This handles parameters that were converted from references to pointers (Bug #1)
  if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(UnstrippedBase)) {
    if (ParmVarDecl *PVD = dyn_cast<ParmVarDecl>(DRE->getDecl())) {
      // Check if parameter is a reference (will be converted to pointer by CodeGenerator)
      if (PVD->getType()->isReferenceType()) {
        useArrow = true;
      }
      // Bug #13: Also check if parameter is already a pointer in the original C++ code
      if (PVD->getType()->isPointerType()) {
        useArrow = true;
      }
    }
  }

  // Create the member expression with the correct arrow/dot operator
  // For reference parameters, we need to manually create the MemberExpr
  // because Builder.arrowMember() requires a pointer type
  Expr *Result = nullptr;

  if (useArrow) {
    // Bug #13 fix: Convert base to pointer type if it's a reference
    // This ensures Clang's printer will use -> instead of .
    Expr *BaseForArrow = TranslatedBase;
    QualType BaseType = TranslatedBase->getType();

    // If the base is a reference type, we need to convert it to a pointer type
    // for the printer to correctly generate ->
    if (BaseType->isReferenceType()) {
      // Get the pointee type (strip reference)
      QualType PointeeType = BaseType.getNonReferenceType();
      // Create pointer type
      QualType PointerType = Context.getPointerType(PointeeType);

      // Create an implicit cast from reference to pointer
      // Note: This is a semantic conversion, not syntactic - the C code will use the pointer directly
      BaseForArrow = ImplicitCastExpr::Create(
          Context, PointerType, CK_LValueToRValue,
          TranslatedBase, nullptr, VK_PRValue, FPOptionsOverride());
    }

    // Try using Builder.arrowMember() with the potentially converted base
    Result = Builder.arrowMember(BaseForArrow, Member->getName());

    // If that failed, create the MemberExpr manually with isArrow=true
    if (!Result) {
      // Get the record type - for references, we need to strip the reference
      QualType BaseRecordType = BaseForArrow->getType();
      if (BaseRecordType->isPointerType()) {
        BaseRecordType = BaseRecordType->getPointeeType();
      } else if (BaseRecordType->isReferenceType()) {
        BaseRecordType = BaseRecordType.getNonReferenceType();
      }

      const RecordType *RT = BaseRecordType->getAs<RecordType>();
      if (RT) {
        RecordDecl *RD = RT->getDecl();
        FieldDecl *FD = nullptr;
        for (auto *Field : RD->fields()) {
          if (Field->getName() == Member->getName()) {
            FD = Field;
            break;
          }
        }

        if (FD) {
          Result = MemberExpr::Create(
              Context, BaseForArrow,
              true, // is arrow
              SourceLocation(), NestedNameSpecifierLoc(), SourceLocation(), FD,
              DeclAccessPair::make(FD, AS_public), DeclarationNameInfo(), nullptr,
              FD->getType(), VK_LValue, OK_Ordinary, NOUR_None);
        }
      }
    }
  } else {
    Result = Builder.member(TranslatedBase, Member->getName());
  }

  // If member access creation failed, return original expression
  if (!Result) {
    return ME;
  }

  return Result;
}

// Translate CallExpr - handles function calls
Expr *CppToCVisitor::translateCallExpr(CallExpr *CE) {
  // Phase 34-05: Check if this is a member method call
  if (CXXMemberCallExpr *MCE = dyn_cast<CXXMemberCallExpr>(CE)) {
    CXXMethodDecl *Method = MCE->getMethodDecl();
    if (Method) {
      // Bug #41 FIX: Use canonical method declaration for lookup
      // Methods are stored in map using canonical decl (line 553)
      // but were being looked up using non-canonical decl, causing mismatches
      CXXMethodDecl *CanonicalMethod = cast<CXXMethodDecl>(Method->getCanonicalDecl());

      // Find the corresponding C function
      FunctionDecl *CFunc = nullptr;
      std::string methodKey = Mangler.mangleName(CanonicalMethod);
      if (targetCtx.getMethodMap().find(methodKey) != targetCtx.getMethodMap().end()) {
        CFunc = targetCtx.getMethodMap()[methodKey];
      }

      if (CFunc) {
        // Translate to C function call: object.method(args) -> Method(&object, args)
        std::vector<Expr *> args;

        // First argument: address of the object
        Expr *ObjectExpr = MCE->getImplicitObjectArgument();
        if (ObjectExpr) {
          Expr *TranslatedObject = translateExpr(ObjectExpr);
          if (TranslatedObject) {
            // Take address if not already a pointer
            if (!ObjectExpr->getType()->isPointerType()) {
              TranslatedObject = Builder.addrOf(TranslatedObject);
            }
            args.push_back(TranslatedObject);
          }
        }

        // Add method arguments
        unsigned paramIdx = 0;  // Index into C++ method parameters
        for (Expr *Arg : MCE->arguments()) {
          Expr *TranslatedArg = translateExpr(Arg);
          Expr *FinalArg = TranslatedArg ? TranslatedArg : Arg;

          // Bug fix #10: Check if C++ parameter was a reference type
          // If so, we need to pass address in C
          if (paramIdx < Method->param_size()) {
            ParmVarDecl *CppParam = Method->getParamDecl(paramIdx);
            QualType CppParamType = CppParam->getType();

            // If C++ parameter was a reference and argument is not already an address-of
            if (CppParamType->isReferenceType() && !isa<UnaryOperator>(FinalArg)) {
              // Strip any implicit casts to check the underlying expression
              Expr *UnderlyingExpr = FinalArg->IgnoreImplicitAsWritten();

              // Only take address if not already a pointer type
              if (!UnderlyingExpr->getType()->isPointerType()) {
                FinalArg = Builder.addrOf(FinalArg);
              }
            }
          }
          args.push_back(FinalArg);
          paramIdx++;
        }

        // Create C function call
        return Builder.call(CFunc, args);
      } else {
        // Bug #14 fix: Method not in map (declaration-only in current TU)
        // Generate the C function call anyway using name mangling
        llvm::outs() << "  Warning: Method not in targetCtx.getMethodMap() map, generating call anyway: "
                     << Method->getQualifiedNameAsString() << "\n";

        // Generate mangled C function name
        std::string funcName = Mangler.mangleName(Method);
        llvm::outs() << "  Generated function name: " << funcName << "\n";

        // Build argument list: &object + original args
        std::vector<Expr *> args;

        // First argument: address of the object
        Expr *ObjectExpr = MCE->getImplicitObjectArgument();
        if (ObjectExpr) {
          Expr *TranslatedObject = translateExpr(ObjectExpr);
          if (TranslatedObject) {
            // Take address if not already a pointer
            if (!ObjectExpr->getType()->isPointerType()) {
              TranslatedObject = Builder.addrOf(TranslatedObject);
            }
            args.push_back(TranslatedObject);
          }
        }

        // Add method arguments
        unsigned paramIdx = 0;
        for (Expr *Arg : MCE->arguments()) {
          Expr *TranslatedArg = translateExpr(Arg);
          Expr *FinalArg = TranslatedArg ? TranslatedArg : Arg;

          // Check if C++ parameter was a reference type
          if (paramIdx < Method->param_size()) {
            ParmVarDecl *CppParam = Method->getParamDecl(paramIdx);
            QualType CppParamType = CppParam->getType();

            // If C++ parameter was a reference and argument is not already an address-of
            if (CppParamType->isReferenceType() && !isa<UnaryOperator>(FinalArg)) {
              // Strip any implicit casts to check the underlying expression
              Expr *UnderlyingExpr = FinalArg->IgnoreImplicitAsWritten();

              // Only take address if not already a pointer type
              if (!UnderlyingExpr->getType()->isPointerType()) {
                FinalArg = Builder.addrOf(FinalArg);
              }
            }
          }
          args.push_back(FinalArg);
          paramIdx++;
        }

        // Create a function declaration for the C function
        // Build parameter types: this pointer + original params
        std::vector<ParmVarDecl *> params;

        // Add this parameter
        CXXRecordDecl *Parent = Method->getParent();
        QualType thisType = Builder.ptrType(Builder.structType(Parent->getName()));
        ParmVarDecl *thisParam = Builder.param(thisType, "this");
        params.push_back(thisParam);

        // Add original parameters
        for (ParmVarDecl *Param : Method->parameters()) {
          ParmVarDecl *CParam = Builder.param(Param->getType(), Param->getName());
          params.push_back(CParam);
        }

        // Create function declaration
        FunctionDecl *CFuncDecl = Builder.funcDecl(funcName, Method->getReturnType(), params, nullptr);

        // Add declaration to C TranslationUnit so it appears in the header
        C_TranslationUnit->addDecl(CFuncDecl);

        // Bug #43 FIX: Store in targetCtx.getMethodMap() map using canonical decl as key
        // This ensures consistency with VisitCXXMethodDecl which also uses canonical
        CXXMethodDecl *CanonicalMethod = cast<CXXMethodDecl>(Method->getCanonicalDecl());
        std::string methodKey = Mangler.mangleName(CanonicalMethod);
        targetCtx.getMethodMap()[methodKey] = CFuncDecl;

        // Create and return the call
        return Builder.call(CFuncDecl, args);
      }
    }
  }

  // Regular function call (not a method)
  // Translate callee and arguments
  Expr *Callee = translateExpr(CE->getCallee());

  // Bug fix #8: If callee translation failed (e.g., RecoveryExpr), skip entire call
  if (!Callee) {
    llvm::outs() << "  Skipping CallExpr due to RecoveryExpr in callee\n";
    return nullptr;
  }

  std::vector<Expr *> args;
  bool hasRecoveryExpr = false;
  for (Expr *Arg : CE->arguments()) {
    Expr *TranslatedArg = translateExpr(Arg);
    if (!TranslatedArg) {
      hasRecoveryExpr = true;
      break;
    }
    args.push_back(TranslatedArg);
  }

  // Bug fix #8: If any argument is RecoveryExpr, skip entire call
  if (hasRecoveryExpr) {
    llvm::outs() << "  Skipping CallExpr due to RecoveryExpr in arguments\n";
    return nullptr;
  }

  // Reconstruct call expression with translated parts
  return CallExpr::Create(Context, Callee, args, CE->getType(),
                          CE->getValueKind(), SourceLocation(),
                          FPOptionsOverride());
}

// Translate BinaryOperator - handles assignments, arithmetic, etc.
Expr *CppToCVisitor::translateBinaryOperator(BinaryOperator *BO) {
  Expr *LHS = translateExpr(BO->getLHS());
  Expr *RHS = translateExpr(BO->getRHS());

  // Bug fix #8: If either operand contains RecoveryExpr (returns nullptr),
  // skip the entire binary operator
  if (!LHS || !RHS) {
    llvm::outs() << "  Skipping BinaryOperator due to RecoveryExpr in operand\n";
    return nullptr;
  }

  return BinaryOperator::Create(
      Context, LHS, RHS, BO->getOpcode(), BO->getType(), BO->getValueKind(),
      BO->getObjectKind(), SourceLocation(), FPOptionsOverride());
}

// Translate CXXConstructExpr - handles C++ constructor calls
// Bug fix #6: Convert C++ constructor to C struct initialization (compound literal)
// Example: Vector3D(x, y, z) -> (struct Vector3D){x, y, z}
// Bug fix #16: Detect copy construction from variable and unwrap it
// Example: return result; -> should stay as "return result;" not "return (struct Type){result};"
Expr *CppToCVisitor::translateConstructExpr(CXXConstructExpr *CCE) {
  // Bug fix #16: Check if this is a copy/move constructor wrapping a simple variable reference
  // Pattern: return result; where result is a local variable
  // Clang represents this as CXXConstructExpr(copy/move ctor, DeclRefExpr)
  // We should unwrap it to just return the variable directly
  // Note: In C++23, this is typically a move constructor due to copy elision

  CXXConstructorDecl *Ctor = CCE->getConstructor();
  if (CCE->getNumArgs() == 1 && (Ctor->isCopyConstructor() || Ctor->isMoveConstructor())) {
    Expr *Arg = CCE->getArg(0);

    // Skip through any implicit casts to find the underlying expression
    while (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(Arg)) {
      Arg = ICE->getSubExpr();
    }

    // If the argument is a simple variable reference (DeclRefExpr),
    // just return the translated variable reference directly
    if (DeclRefExpr *DRE = dyn_cast<DeclRefExpr>(Arg)) {
      return translateExpr(DRE);
    }
  }

  // Translate all constructor arguments
  std::vector<Expr *> translatedArgs;
  for (unsigned i = 0; i < CCE->getNumArgs(); ++i) {
    Expr *Arg = CCE->getArg(i);
    Expr *TranslatedArg = translateExpr(Arg);
    translatedArgs.push_back(TranslatedArg ? TranslatedArg : Arg);
  }

  // Bug fix #6: Get the C struct type instead of C++ class type
  // This ensures (struct Type) instead of just (Type)
  QualType resultType = CCE->getType();
  CXXRecordDecl *CppClass = CCE->getType()->getAsCXXRecordDecl();
  if (CppClass && cppToCMap.find(CppClass) != cppToCMap.end()) {
    // Use the C struct type for proper "struct TypeName" printing
    RecordDecl *CStruct = cppToCMap[CppClass];
    resultType = Context.getRecordType(CStruct);
  }

  // Bug fix #6: Create InitListExpr for C struct initialization
  // This generates {arg1, arg2, ...} syntax
  InitListExpr *InitList = new (Context) InitListExpr(
      Context, SourceLocation(), translatedArgs, SourceLocation());
  InitList->setType(resultType);

  // Wrap in CompoundLiteralExpr to create (struct Type){...}
  // This is the proper C99 syntax for struct literals in return statements
  CompoundLiteralExpr *CompoundLit = new (Context) CompoundLiteralExpr(
      SourceLocation(), Context.getTrivialTypeSourceInfo(resultType),
      resultType, VK_PRValue, InitList, false);

  return CompoundLit;
}

// ============================================================================
// Story #19: Statement Translation
// ============================================================================

// Main statement translation dispatcher
Stmt *CppToCVisitor::translateStmt(Stmt *S) {
  if (!S)
    return nullptr;

  llvm::outs() << "[DEBUG Bug#26] translateStmt called, type: " << S->getStmtClassName() << "\n";

  // Dispatch to specific translators
  if (ReturnStmt *RS = dyn_cast<ReturnStmt>(S)) {
    llvm::outs() << "[DEBUG Bug#26] Dispatching to translateReturnStmt\n";
    return translateReturnStmt(RS);
  }

  if (CompoundStmt *CS = dyn_cast<CompoundStmt>(S)) {
    return translateCompoundStmt(CS);
  }

  // Phase 34-05: Handle variable declarations with constructors
  if (DeclStmt *DS = dyn_cast<DeclStmt>(S)) {
    return translateDeclStmt(DS);
  }

  // Bug #13 fix: Handle ForStmt - translate all sub-statements and expressions
  // This is critical for translating expressions like other.data[i] inside for loops
  if (ForStmt *FS = dyn_cast<ForStmt>(S)) {
    Stmt *Init = FS->getInit();
    Expr *Cond = FS->getCond();
    Expr *Inc = FS->getInc();
    Stmt *Body = FS->getBody();

    // Translate each component
    Stmt *TranslatedInit = Init ? translateStmt(Init) : nullptr;
    Expr *TranslatedCond = Cond ? translateExpr(Cond) : nullptr;
    Expr *TranslatedInc = Inc ? translateExpr(Inc) : nullptr;
    Stmt *TranslatedBody = Body ? translateStmt(Body) : nullptr;

    // Create new ForStmt with translated components
    return new (Context) ForStmt(
        Context, TranslatedInit, TranslatedCond, nullptr, TranslatedInc,
        TranslatedBody, FS->getForLoc(), FS->getLParenLoc(), FS->getRParenLoc());
  }

  // Bug #26: Handle IfStmt - translate condition and branches, create NEW C AST node
  if (IfStmt *IS = dyn_cast<IfStmt>(S)) {
    Expr *Cond = IS->getCond();
    Stmt *Then = IS->getThen();
    Stmt *Else = IS->getElse();

    Expr *TranslatedCond = Cond ? translateExpr(Cond) : nullptr;
    Stmt *TranslatedThen = Then ? translateStmt(Then) : nullptr;
    Stmt *TranslatedElse = Else ? translateStmt(Else) : nullptr;

    return IfStmt::Create(Context, IS->getIfLoc(), IfStatementKind::Ordinary,
                          nullptr, nullptr, TranslatedCond, IS->getLParenLoc(),
                          IS->getRParenLoc(), TranslatedThen, IS->getElseLoc(),
                          TranslatedElse);
  }

  // Bug #26: Handle WhileStmt - translate condition and body, create NEW C AST node
  if (WhileStmt *WS = dyn_cast<WhileStmt>(S)) {
    Expr *Cond = WS->getCond();
    Stmt *Body = WS->getBody();

    Expr *TranslatedCond = Cond ? translateExpr(Cond) : nullptr;
    Stmt *TranslatedBody = Body ? translateStmt(Body) : nullptr;

    return WhileStmt::Create(Context, nullptr, TranslatedCond, TranslatedBody,
                              WS->getWhileLoc(), WS->getLParenLoc(), WS->getRParenLoc());
  }

  // Bug #26: Handle SwitchStmt - translate condition and body, create NEW C AST node
  if (SwitchStmt *SS = dyn_cast<SwitchStmt>(S)) {
    Expr *Cond = SS->getCond();
    Stmt *Body = SS->getBody();

    Expr *TranslatedCond = Cond ? translateExpr(Cond) : nullptr;
    Stmt *TranslatedBody = Body ? translateStmt(Body) : nullptr;

    SwitchStmt *NewSwitch = SwitchStmt::Create(Context, nullptr, nullptr, TranslatedCond,
                                                SS->getLParenLoc(), SS->getRParenLoc());
    NewSwitch->setBody(TranslatedBody);
    return NewSwitch;
  }

  // Bug #26: Handle CaseStmt - translate LHS and substmt, create NEW C AST node
  if (CaseStmt *CS = dyn_cast<CaseStmt>(S)) {
    Expr *LHS = CS->getLHS();
    Stmt *SubStmt = CS->getSubStmt();

    Expr *TranslatedLHS = LHS ? translateExpr(LHS) : nullptr;
    Stmt *TranslatedSubStmt = SubStmt ? translateStmt(SubStmt) : nullptr;

    CaseStmt *NewCase = CaseStmt::Create(Context, TranslatedLHS, nullptr, CS->getCaseLoc(),
                                          CS->getEllipsisLoc(), CS->getColonLoc());
    NewCase->setSubStmt(TranslatedSubStmt);
    return NewCase;
  }

  // Bug #26: Handle DefaultStmt - translate substmt, create NEW C AST node
  if (DefaultStmt *DS = dyn_cast<DefaultStmt>(S)) {
    Stmt *SubStmt = DS->getSubStmt();

    Stmt *TranslatedSubStmt = SubStmt ? translateStmt(SubStmt) : nullptr;

    return new (Context) DefaultStmt(DS->getDefaultLoc(), DS->getColonLoc(), TranslatedSubStmt);
  }

  // Bug #26: Recursively visit all children to ensure nested return statements are seen
  // We don't recreate the statement (complex API issues), but we ensure children are visited
  for (Stmt *Child : S->children()) {
    if (Child) {
      translateStmt(Child);
    }
  }

  // If it's an expression, translate it
  if (Expr *E = dyn_cast<Expr>(S)) {
    return translateExpr(E);
  }

  // Default: return as-is
  return S;
}

// Translate return statements
// Story #45: Modified to inject destructors before early returns
Stmt *CppToCVisitor::translateReturnStmt(ReturnStmt *RS) {
  // If we have objects to destroy at this return point, we need to
  // inject destructor calls before the return
  // This creates a compound statement: { dtors...; return; }

  llvm::outs() << "[DEBUG Bug#26] translateReturnStmt called\n";

  Expr *RetValue = RS->getRetValue();

  // Bug #26: Handle constructor calls in return statements
  // Pattern: return ClassName(args...);
  // Transform to: struct ClassName temp; ClassName__ctor(&temp, args...); return temp;
  if (RetValue) {
    llvm::outs() << "[DEBUG Bug#26] RetValue exists, type: " << RetValue->getStmtClassName() << "\n";

    // Debug: Print full expression structure
    if (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(RetValue)) {
      llvm::outs() << "[DEBUG Bug#26]   ImplicitCastExpr -> subexpr type: " << ICE->getSubExpr()->getStmtClassName() << "\n";
    }
    if (ExprWithCleanups *EWC = dyn_cast<ExprWithCleanups>(RetValue)) {
      llvm::outs() << "[DEBUG Bug#26]   ExprWithCleanups -> subexpr type: " << EWC->getSubExpr()->getStmtClassName() << "\n";
    }

    // Check if return value is a constructor expression
    CXXConstructExpr *CCE = dyn_cast<CXXConstructExpr>(RetValue);
    if (!CCE) {
      // Unwrap implicit casts and cleanups
      if (ExprWithCleanups *EWC = dyn_cast<ExprWithCleanups>(RetValue)) {
        CCE = dyn_cast<CXXConstructExpr>(EWC->getSubExpr());
        if (CCE) llvm::outs() << "[DEBUG Bug#26]   Found CCE inside ExprWithCleanups\n";
      }
      if (!CCE && isa<ImplicitCastExpr>(RetValue)) {
        ImplicitCastExpr *ICE = cast<ImplicitCastExpr>(RetValue);
        CCE = dyn_cast<CXXConstructExpr>(ICE->getSubExpr());
        if (CCE) llvm::outs() << "[DEBUG Bug#26]   Found CCE inside ImplicitCastExpr\n";
      }
      // Bug #26: Also check for CXXFunctionalCastExpr (e.g., Token(EndOfInput))
      if (!CCE) {
        if (CXXFunctionalCastExpr *FCE = dyn_cast<CXXFunctionalCastExpr>(RetValue)) {
          llvm::outs() << "[DEBUG Bug#26]   Found CXXFunctionalCastExpr, checking subexpr\n";
          Expr *SubExpr = FCE->getSubExpr();
          // The subexpr might be wrapped in casts
          while (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(SubExpr)) {
            SubExpr = ICE->getSubExpr();
          }
          CCE = dyn_cast<CXXConstructExpr>(SubExpr);
          if (CCE) llvm::outs() << "[DEBUG Bug#26]   Found CCE inside CXXFunctionalCastExpr\n";
        }
      }
    }

    if (CCE) {
      llvm::outs() << "[DEBUG Bug#26] Constructor expression detected!\n";
      // This is a constructor call in return statement
      CXXConstructorDecl *Ctor = CCE->getConstructor();
      llvm::outs() << "[DEBUG Bug#26] Constructor: " << Ctor->getNameAsString() << "\n";
      llvm::outs() << "[DEBUG Bug#26] isCopyConstructor: " << Ctor->isCopyConstructor() << "\n";
      llvm::outs() << "[DEBUG Bug#26] isMoveConstructor: " << Ctor->isMoveConstructor() << "\n";
      llvm::outs() << "[DEBUG Bug#26] NumArgs: " << CCE->getNumArgs() << "\n";

      // Check if this is a copy/move constructor wrapping another constructor
      if (CCE->getNumArgs() == 1 && (Ctor->isCopyConstructor() || Ctor->isMoveConstructor())) {
        llvm::outs() << "[DEBUG Bug#26] This is a copy/move constructor, checking argument...\n";
        Expr *Arg = CCE->getArg(0);
        llvm::outs() << "[DEBUG Bug#26] Argument type: " << Arg->getStmtClassName() << "\n";

        // Unwrap casts
        while (ImplicitCastExpr *ICE = dyn_cast<ImplicitCastExpr>(Arg)) {
          Arg = ICE->getSubExpr();
          llvm::outs() << "[DEBUG Bug#26] Unwrapped to: " << Arg->getStmtClassName() << "\n";
        }

        // Check if the argument is another constructor call
        if (CXXConstructExpr *InnerCCE = dyn_cast<CXXConstructExpr>(Arg)) {
          llvm::outs() << "[DEBUG Bug#26] Found INNER constructor! Unwrapping copy constructor.\n";
          CCE = InnerCCE;
          Ctor = CCE->getConstructor();
          llvm::outs() << "[DEBUG Bug#26] Inner constructor: " << Ctor->getNameAsString() << "\n";
        } else if (isa<DeclRefExpr>(Arg)) {
          // Just return the variable directly
          llvm::outs() << "[DEBUG Bug#26] Copy of variable, returning normally\n";
          Expr *TranslatedValue = translateExpr(RetValue);
          return Builder.returnStmt(TranslatedValue);
        }
      }

      // Look up the C constructor function using canonical declaration
      CXXConstructorDecl *CanonicalCtor = cast<CXXConstructorDecl>(Ctor->getCanonicalDecl());
      std::string canonicalCtorKey = Mangler.mangleConstructor(CanonicalCtor);
      llvm::outs() << "[DEBUG Bug#26] Looking up in targetCtx.getCtorMap() (size: " << targetCtx.getCtorMap().size() << ")\n";
      auto it = targetCtx.getCtorMap().find(canonicalCtorKey);
      if (it != targetCtx.getCtorMap().end()) {
        FunctionDecl *CCtorFunc = it->second;
        llvm::outs() << "[DEBUG Bug#26] Found in targetCtx.getCtorMap()! C function: " << CCtorFunc->getNameAsString() << "\n";

        // Create a compound statement: { struct Type temp; Type__ctor(&temp, args...); return temp; }
        std::vector<Stmt *> stmts;

        // 1. Create temporary variable: struct Type temp;
        QualType resultType = CCE->getType();
        CXXRecordDecl *CppClass = resultType->getAsCXXRecordDecl();
        if (CppClass && cppToCMap.find(CppClass) != cppToCMap.end()) {
          RecordDecl *CStruct = cppToCMap[CppClass];
          resultType = Context.getRecordType(CStruct);
        }

        VarDecl *tempVar = Builder.var(resultType, "__return_temp");
        stmts.push_back(Builder.declStmt(tempVar));

        // 2. Call constructor: Type__ctor(&temp, args...);
        std::vector<Expr *> ctorArgs;

        // First arg: address of temp variable (&temp)
        DeclRefExpr *tempRef = Builder.ref(tempVar);
        Expr *tempAddr = Builder.addrOf(tempRef);
        ctorArgs.push_back(tempAddr);

        // Remaining args: translate constructor arguments
        for (unsigned i = 0; i < CCE->getNumArgs(); ++i) {
          Expr *Arg = CCE->getArg(i);
          Expr *TranslatedArg = translateExpr(Arg);
          ctorArgs.push_back(TranslatedArg ? TranslatedArg : Arg);
        }

        // Handle default arguments if constructor has more parameters
        unsigned numParams = CCtorFunc->getNumParams();
        unsigned numArgs = ctorArgs.size(); // Includes 'this' parameter
        if (numArgs < numParams) {
          // Add default values for missing arguments
          for (unsigned i = numArgs; i < numParams; ++i) {
            ParmVarDecl *Param = CCtorFunc->getParamDecl(i);
            if (Param->hasDefaultArg()) {
              Expr *DefaultArg = Param->getDefaultArg();
              Expr *TranslatedDefault = translateExpr(DefaultArg);
              ctorArgs.push_back(TranslatedDefault ? TranslatedDefault : DefaultArg);
            } else {
              // No default value available - use zero initializer
              QualType ParamType = Param->getType();
              if (ParamType->isIntegerType()) {
                ctorArgs.push_back(Builder.intLit(0));
              } else {
                llvm::outs() << "  Warning: No default value for parameter " << i << "\n";
              }
            }
          }
        }

        // Create constructor call
        Expr *ctorCall = Builder.call(CCtorFunc, ctorArgs);
        stmts.push_back(ctorCall);

        // 3. Return temp variable
        stmts.push_back(Builder.returnStmt(Builder.ref(tempVar)));

        // Return compound statement
        llvm::outs() << "[DEBUG Bug#26] Returning compound statement with " << stmts.size() << " statements\n";
        return Builder.block(stmts);
      } else {
        llvm::outs() << "[DEBUG Bug#26] WARNING: Constructor not found in targetCtx.getCtorMap() for return statement\n";
        llvm::outs() << "[DEBUG Bug#26] Constructor name: " << CanonicalCtor->getNameAsString() << "\n";
      }
    } else {
      llvm::outs() << "[DEBUG Bug#26] No constructor expression detected after unwrapping\n";
    }

    // Fall back to normal translation
    Expr *TranslatedValue = translateExpr(RetValue);
    if (TranslatedValue) {
      return Builder.returnStmt(TranslatedValue);
    }
  }

  return Builder.returnStmt();
}

// Phase 34-05: Translate declaration statements (variable declarations)
// This handles C++ constructor syntax and converts it to C initialization
Stmt *CppToCVisitor::translateDeclStmt(DeclStmt *DS) {
  if (!DS) {
    return nullptr;
  }

  // Phase 34-05/34-06: Translate variable declarations
  // Handles both class constructors and method call initializers
  llvm::outs() << "  [Translating DeclStmt]\n";

  std::vector<Stmt *> statements;

  // Process each declaration in the statement
  for (Decl *D : DS->decls()) {
    VarDecl *VD = dyn_cast<VarDecl>(D);
    if (!VD) {
      // Not a variable declaration, keep as-is
      continue;
    }

    llvm::outs() << "    Variable: " << VD->getNameAsString() << "\n";

    // Get the variable type
    QualType VarType = VD->getType();
    const Type *T = VarType.getTypePtr();

    // Bug #38 FIX: Check if this is a pointer to a nested class that needs monomorphization
    // E.g., "Node *newNode" -> "struct LinkedList_int_Node *newNode"
    if (currentNestedClassMappings && T->isPointerType()) {
      const PointerType *PT = T->getAs<PointerType>();
      QualType PointeeType = PT->getPointeeType();

      // Check if pointee is a record type (struct/class)
      if (const RecordType *RT = PointeeType->getAs<RecordType>()) {
        RecordDecl *RD = RT->getDecl();
        std::string typeName = RD->getNameAsString();

        // Check if this type is in our nested class mappings
        auto it = currentNestedClassMappings->find(typeName);
        if (it != currentNestedClassMappings->end()) {
          // Found it! Replace with monomorphized type
          std::string monomorphizedName = it->second;
          llvm::outs() << "      Substituting nested class pointer: " << typeName
                       << "* -> struct " << monomorphizedName << "*\n";

          // Create the monomorphized struct type
          IdentifierInfo &II = Context.Idents.get(monomorphizedName);
          RecordDecl *CRecord = RecordDecl::Create(
              Context,
#if LLVM_VERSION_MAJOR >= 16
              TagTypeKind::Struct,
#else
              TTK_Struct,
#endif
              Context.getTranslationUnitDecl(),
              SourceLocation(),
              SourceLocation(),
              &II
          );

          // Create pointer to the struct
          QualType CStructType = Context.getRecordType(CRecord);
          QualType CPointerType = Context.getPointerType(CStructType);

          // Create the C variable declaration
          VarDecl *CVarDecl = Builder.var(CPointerType, VD->getName());

          // If there's an initializer, translate it
          if (Expr *Init = VD->getInit()) {
            Expr *TranslatedInit = translateExpr(Init);
            if (TranslatedInit) {
              CVarDecl->setInit(TranslatedInit);
            }
          }

          return Builder.declStmt(CVarDecl);
        }
      }
    }

    // BUG FIX (Bug #18): Check if this is a template specialization type
    // E.g., LinkedList<int> list; -> struct LinkedList_int list;
    if (const RecordType *RT = T->getAs<RecordType>()) {
      RecordDecl *RD = RT->getDecl();

      // Check if this is a ClassTemplateSpecializationDecl
      if (ClassTemplateSpecializationDecl *CTSD = dyn_cast<ClassTemplateSpecializationDecl>(RD)) {
        llvm::outs() << "      Is a template specialization: " << CTSD->getNameAsString() << "\n";

        // Generate mangled name for the monomorphized struct
        // Reuse TemplateMonomorphizer's generateMangledName function
        std::string mangledName = m_templateMonomorphizer->generateMangledName(
            CTSD->getSpecializedTemplate()->getNameAsString(),
            CTSD->getTemplateArgs()
        );

        llvm::outs() << "      Monomorphized struct name: " << mangledName << "\n";

        // Create C variable declaration with monomorphized struct type
        // struct LinkedList_int list;
        IdentifierInfo &II = Context.Idents.get(mangledName);
        RecordDecl *CRecord = RecordDecl::Create(
            Context,
#if LLVM_VERSION_MAJOR >= 16
            TagTypeKind::Struct,
#else
            TTK_Struct,
#endif
            Context.getTranslationUnitDecl(),
            SourceLocation(),
            SourceLocation(),
            &II
        );

        QualType CStructType = Context.getRecordType(CRecord);
        VarDecl *CVarDecl = Builder.var(CStructType, VD->getName());
        return Builder.declStmt(CVarDecl);
      }
    }

    // Check if this is a class type with a constructor call
    // Note: Use getAs<RecordType>() which works for both C structs and C++ classes
    if (const RecordType *RT = T->getAs<RecordType>()) {
      llvm::outs() << "      Is a struct/class type\n";
      RecordDecl *RD = RT->getDecl();
      CXXRecordDecl *CXXRD = dyn_cast<CXXRecordDecl>(RD);

      if (CXXRD) {
        llvm::outs() << "      Is a C++ class: " << CXXRD->getNameAsString() << "\n";
        // This is a C++ class - need to translate constructor call
        Expr *Init = VD->getInit();

        // Check if the initializer is a constructor expression
        CXXConstructExpr *CCE = nullptr;
        if (Init) {
          // Direct constructor call: Point p(3, 4);
          CCE = dyn_cast<CXXConstructExpr>(Init);
          if (!CCE) {
            // Might be wrapped in ExprWithCleanups or other expressions
            if (ExprWithCleanups *EWC = dyn_cast<ExprWithCleanups>(Init)) {
              CCE = dyn_cast<CXXConstructExpr>(EWC->getSubExpr());
            }
          }
        } else {
          // Default initialization: Point p;
          // We'll create a default constructor call if one exists
        }

        // Find the corresponding C struct
        RecordDecl *CStruct = nullptr;
        if (cppToCMap.find(CXXRD) != cppToCMap.end()) {
          CStruct = cppToCMap[CXXRD];
          llvm::outs() << "      Found C struct: " << CStruct->getNameAsString() << "\n";
        } else {
          llvm::outs() << "      WARNING: C struct not found in cppToCMap!\n";
        }

        if (CStruct) {
          llvm::outs() << "      Creating C variable declaration\n";
          // Step 1: Create variable declaration without initializer
          //         struct Point p;
          QualType CStructType = Context.getRecordType(CStruct);
          VarDecl *CVarDecl = Builder.var(CStructType, VD->getName());
          DeclStmt *CDeclStmt = Builder.declStmt(CVarDecl);
          statements.push_back(CDeclStmt);

          // Step 2: If there's a constructor, create the constructor call
          //         Point__ctor(&p, 3, 4);
          if (CCE) {
            llvm::outs() << "      Has constructor expression\n";
            CXXConstructorDecl *Ctor = CCE->getConstructor();

            // Use mangled name as key (not pointer) to work across C++ ASTContexts
            std::string ctorKey = Mangler.mangleConstructor(Ctor);

            llvm::outs() << "      [DEBUG] Looking for constructor in SHARED map (size: "
                         << targetCtx.getCtorMap().size() << ")\n";
            llvm::outs() << "      [DEBUG] Looking for key: " << ctorKey << "\n";

            // Find the corresponding C constructor function
            FunctionDecl *CCtorFunc = nullptr;
            if (targetCtx.getCtorMap().find(ctorKey) != targetCtx.getCtorMap().end()) {
              CCtorFunc = targetCtx.getCtorMap()[ctorKey];
              llvm::outs() << "      Found C constructor: " << CCtorFunc->getNameAsString() << "\n";
            } else {
              llvm::outs() << "      WARNING: C constructor not found in targetCtx.getCtorMap()!\n";
              llvm::outs() << "      [DEBUG] Map contents:\n";
              for (const auto& entry : targetCtx.getCtorMap()) {
                llvm::outs() << "        Key: " << entry.first << " -> " << entry.second->getNameAsString() << "\n";
              }
            }

            if (CCtorFunc) {
              llvm::outs() << "      Creating constructor call\n";
              // Create argument list: &p, arg1, arg2, ...
              std::vector<Expr *> args;

              // First argument: address of the variable
              DeclRefExpr *VarRef = Builder.ref(CVarDecl);
              Expr *VarAddr = Builder.addrOf(VarRef);
              args.push_back(VarAddr);

              // Add constructor arguments
              for (const Expr *Arg : CCE->arguments()) {
                Expr *TranslatedArg = translateExpr(const_cast<Expr *>(Arg));
                if (TranslatedArg) {
                  args.push_back(TranslatedArg);
                }
              }

              // Create constructor function call
              Expr *CtorCall = Builder.call(CCtorFunc, args);
              statements.push_back(CtorCall);
            }
          }
        } else {
          // C struct not found, return original statement
          return DS;
        }
      } else {
        // Plain C struct, return as-is
        return DS;
      }
    } else {
      // Not a class type (int, float, etc.)
      // Phase 34-06: Still need to translate initializer if it contains method calls
      // Example: int dist = p.distanceSquared(); → int dist = Point_distanceSquared(&p);
      Expr *Init = VD->getInit();
      if (Init) {
        Expr *TranslatedInit = translateExpr(Init);

        // Bug fix #8: If translation returns nullptr (RecoveryExpr), create var without initializer
        if (!TranslatedInit) {
          llvm::outs() << "    Initializer contains RecoveryExpr, creating variable without initializer\n";
          VarDecl *CVar = Builder.var(VarType, VD->getName());
          return Builder.declStmt(CVar);
        }

        if (TranslatedInit != Init) {
          // Initializer was translated (method call, constructor, etc.)
          VarDecl *CVar = Builder.var(VarType, VD->getName(), TranslatedInit);
          return Builder.declStmt(CVar);
        }
      }
      // No translation needed, return as-is
      return DS;
    }
  }

  // If we generated statements, return them as a compound statement
  if (!statements.empty()) {
    return Builder.block(statements);
  }

  // Fallback: return original
  return DS;
}

// Story #45: Helper - removed inline class since it needs access to private
// members The injection logic is now directly in translateCompoundStmt

// Translate compound statements (blocks)
// Story #46: Enhanced with scope tracking for nested destructor injection
Stmt *CppToCVisitor::translateCompoundStmt(CompoundStmt *CS) {
  // Story #46: Enter this scope
  enterScope(CS);

  std::vector<Stmt *> translatedStmts;

  // Translate all statements in the compound statement
  for (Stmt *S : CS->body()) {
    // Bug #8: Skip statements containing RecoveryExpr (parsing errors from missing headers)
    // Bug #17: Exclude DeclStmt from statement-level filtering - it has expression-level handling
    // DeclStmt with RecoveryExpr in initializer creates variable without initializer (correct behavior)
    if (containsRecoveryExpr(S) && !isa<DeclStmt>(S)) {
      llvm::outs() << "  [Bug #8] Skipping statement containing RecoveryExpr\n";
      continue;
    }

    // Check if this is a VarDecl statement with a destructor
    if (DeclStmt *DS = dyn_cast<DeclStmt>(S)) {
      // Check if any decls in this statement have destructors
      for (Decl *D : DS->decls()) {
        if (VarDecl *VD = dyn_cast<VarDecl>(D)) {
          if (hasNonTrivialDestructor(VD->getType())) {
            // Story #46: Track this object in current scope
            trackObjectInCurrentScope(VD);
          }
        }
      }
    }

    // Story #45: Check if this statement contains a return that needs injection
    if (ReturnStmt *RS = dyn_cast<ReturnStmt>(S)) {
      // Analyze live objects at this return point
      std::vector<VarDecl *> liveObjects =
          analyzeLiveObjectsAtReturn(RS, nullptr);

      if (!liveObjects.empty()) {
        llvm::outs() << "  Injecting " << liveObjects.size()
                     << " destructors before return in compound\n";

        // Inject destructors in reverse order (LIFO)
        for (auto it = liveObjects.rbegin(); it != liveObjects.rend(); ++it) {
          CallExpr *DtorCall = createDestructorCall(*it);
          if (DtorCall) {
            translatedStmts.push_back(DtorCall);
            llvm::outs() << "    -> " << (*it)->getNameAsString()
                         << " destructor before return\n";
          }
        }
      }

      // Translate and add the return statement
      Stmt *TranslatedStmt = translateStmt(S);
      if (TranslatedStmt) {
        translatedStmts.push_back(TranslatedStmt);
      }
    } else if (BreakStmt *BS = dyn_cast<BreakStmt>(S)) {
      // Story #48: Check if this break needs destructor injection
      for (const BreakContinueInfo &info : currentFunctionBreaksContinues) {
        if (info.stmt == BS && info.isBreak) {
          if (!info.liveObjects.empty()) {
            llvm::outs() << "  Injecting " << info.liveObjects.size()
                         << " destructors before break\n";

            // Inject destructors in reverse order (LIFO)
            for (auto it = info.liveObjects.rbegin();
                 it != info.liveObjects.rend(); ++it) {
              CallExpr *DtorCall = createDestructorCall(*it);
              if (DtorCall) {
                translatedStmts.push_back(DtorCall);
                llvm::outs() << "    -> " << (*it)->getNameAsString()
                             << " destructor before break\n";
              }
            }
          }
          break; // Found the matching break info
        }
      }

      // Translate and add the break statement
      Stmt *TranslatedStmt = translateStmt(S);
      if (TranslatedStmt) {
        translatedStmts.push_back(TranslatedStmt);
      }
    } else if (ContinueStmt *CS_Cont = dyn_cast<ContinueStmt>(S)) {
      // Story #48: Check if this continue needs destructor injection
      for (const BreakContinueInfo &info : currentFunctionBreaksContinues) {
        if (info.stmt == CS_Cont && !info.isBreak) {
          if (!info.liveObjects.empty()) {
            llvm::outs() << "  Injecting " << info.liveObjects.size()
                         << " destructors before continue\n";

            // Inject destructors in reverse order (LIFO)
            for (auto it = info.liveObjects.rbegin();
                 it != info.liveObjects.rend(); ++it) {
              CallExpr *DtorCall = createDestructorCall(*it);
              if (DtorCall) {
                translatedStmts.push_back(DtorCall);
                llvm::outs() << "    -> " << (*it)->getNameAsString()
                             << " destructor before continue\n";
              }
            }
          }
          break; // Found the matching continue info
        }
      }

      // Translate and add the continue statement
      Stmt *TranslatedStmt = translateStmt(S);
      if (TranslatedStmt) {
        translatedStmts.push_back(TranslatedStmt);
      }
    } else if (IfStmt *IS = dyn_cast<IfStmt>(S)) {
      // Story #45: Recursively handle nested if statements
      // Returns inside if blocks need destructor injection too
      Stmt *TranslatedStmt = translateStmt(S);
      if (TranslatedStmt) {
        translatedStmts.push_back(TranslatedStmt);
      }
    } else {
      // Regular statement translation (includes nested CompoundStmts)
      Stmt *TranslatedStmt = translateStmt(S);
      if (TranslatedStmt) {
        // Phase 34-06: If the translated statement is a CompoundStmt returned from
        // translateDeclStmt, flatten it by adding its children directly
        // This fixes the scoping issue where constructor calls were wrapped in a block
        // Example: {struct Point p; Point__ctor(&p, 3, 4);} → two separate statements
        // Bug #12 fix: Also flatten single-statement blocks from default constructors
        // Example: {struct Matrix3x3 result;} → struct Matrix3x3 result;
        if (CompoundStmt *TranslatedBlock = dyn_cast<CompoundStmt>(TranslatedStmt)) {
          // Check if this is a flattening candidate from translateDeclStmt
          // Bug #12: Remove size check - flatten ALL DeclStmt blocks, even with 1 statement
          if (isa<DeclStmt>(S) && TranslatedBlock->size() > 0) {
            // Flatten: add children directly instead of nested block
            for (Stmt *Child : TranslatedBlock->body()) {
              translatedStmts.push_back(Child);
            }
          } else {
            translatedStmts.push_back(TranslatedStmt);
          }
        } else {
          translatedStmts.push_back(TranslatedStmt);
        }
      }
    }
  }

  // Story #46: Exit this scope and inject destructors for scope-local objects
  ScopeInfo exitedScope = exitScope();

  // Inject destructors for objects in THIS scope (not parent scopes)
  // LIFO order: reverse of declaration order
  if (!exitedScope.objects.empty()) {
    llvm::outs() << "  [Scope] Injecting " << exitedScope.objects.size()
                 << " destructor(s) at end of scope depth " << exitedScope.depth
                 << "\n";

    for (auto it = exitedScope.objects.rbegin();
         it != exitedScope.objects.rend(); ++it) {
      VarDecl *VD = *it;
      CallExpr *DtorCall = createDestructorCall(VD);
      if (DtorCall) {
        translatedStmts.push_back(DtorCall);
        llvm::outs() << "    -> " << VD->getNameAsString()
                     << " destructor injected at scope exit\n";
      }
    }
  }

  // Story #44: Legacy function-level tracking
  // Only inject if we're at depth 0 (function body) and have no scope stack
  // This maintains backward compatibility with Stories #44 and #45
  if (scopeStack.empty() && !currentFunctionObjectsToDestroy.empty()) {
    // This is the function body exiting - but objects are already handled by
    // scope tracking We can skip this if scope tracking handled them
    llvm::outs() << "  [Legacy] Function-level destruction already handled by "
                    "scope tracking\n";
  }

  return Builder.block(translatedStmts);
}

// ============================================================================
// Epic #7: Implicit Constructor Generation (Story #62)
// ============================================================================

/**
 * Story #62: Check if class needs implicit default constructor
 *
 * Returns true if:
 * - No user-declared constructors exist (hasUserDeclaredConstructor() returns
 * false)
 */
bool CppToCVisitor::needsImplicitDefaultConstructor(CXXRecordDecl *D) const {
  // If user declared ANY constructor, no implicit default constructor
  return !D->hasUserDeclaredConstructor();
}

/**
 * Story #62: Check if class needs implicit copy constructor
 *
 * Returns true if:
 * - No user-declared copy constructor exists
 * - Class has at least one constructor (to enable copy construction)
 */
bool CppToCVisitor::needsImplicitCopyConstructor(CXXRecordDecl *D) const {
  // Check if user declared a copy constructor (not compiler-generated)
  for (CXXConstructorDecl *Ctor : D->ctors()) {
    if (Ctor->isCopyConstructor() && !Ctor->isImplicit()) {
      return false; // User declared copy constructor exists
    }
  }

  // Generate copy constructor if class has any constructor
  // (either explicit or we're about to generate default)
  return D->hasUserDeclaredConstructor() || needsImplicitDefaultConstructor(D);
}

/**
 * Story #62: Generate implicit constructors for a class
 *
 * Orchestrates generation of default and copy constructors when needed.
 */
void CppToCVisitor::generateImplicitConstructors(CXXRecordDecl *D) {
  // Generate default constructor if needed
  if (needsImplicitDefaultConstructor(D)) {
    llvm::outs() << "  Generating implicit default constructor\n";
    FunctionDecl *DefaultCtor = generateDefaultConstructor(D);
    if (DefaultCtor) {
      // Store in constructor map for retrieval
      // Find the C++ implicit default constructor to use as key
      CXXConstructorDecl *CppDefaultCtor = nullptr;
      for (CXXConstructorDecl *Ctor : D->ctors()) {
        if (Ctor->isDefaultConstructor()) {
          CppDefaultCtor = Ctor;
          break;
        }
      }

      if (CppDefaultCtor) {
        std::string ctorKey = Mangler.mangleConstructor(CppDefaultCtor);
        targetCtx.getCtorMap()[ctorKey] = DefaultCtor;
      } else {
        // Fallback: use function name as key if no C++ ctor found
        targetCtx.getCtorMap()[DefaultCtor->getNameAsString()] = DefaultCtor;
      }

      // Phase 32: Add to C TranslationUnit for output generation
      C_TranslationUnit->addDecl(DefaultCtor);
    }
  }

  // Generate copy constructor if needed
  if (needsImplicitCopyConstructor(D)) {
    llvm::outs() << "  Generating implicit copy constructor\n";
    FunctionDecl *CopyCtor = generateCopyConstructor(D);
    if (CopyCtor) {
      // Store in constructor map for retrieval
      // Find the C++ implicit copy constructor to use as key
      CXXConstructorDecl *CppCopyCtor = nullptr;
      for (CXXConstructorDecl *Ctor : D->ctors()) {
        if (Ctor->isCopyConstructor()) {
          CppCopyCtor = Ctor;
          break;
        }
      }

      if (CppCopyCtor) {
        std::string ctorKey = Mangler.mangleConstructor(CppCopyCtor);
        targetCtx.getCtorMap()[ctorKey] = CopyCtor;
      } else {
        // Fallback: use function name as key if no C++ ctor found
        targetCtx.getCtorMap()[CopyCtor->getNameAsString()] = CopyCtor;
      }

      // Phase 32: Add to C TranslationUnit for output generation
      C_TranslationUnit->addDecl(CopyCtor);
    }
  }
}

/**
 * Story #62: Generate default constructor
 *
 * Generates: Class__ctor_default(struct Class *this)
 * - Zero-initializes primitive members
 * - Calls default constructors for class-type members
 * - Calls base class default constructor if derived
 */
FunctionDecl *CppToCVisitor::generateDefaultConstructor(CXXRecordDecl *D) {
  // Get the C struct for this class
  RecordDecl *CStruct = cppToCMap[D];
  if (!CStruct) {
    llvm::outs()
        << "  Warning: C struct not found for default ctor generation\n";
    return nullptr;
  }

  // Build parameter list: only 'this' parameter
  std::vector<ParmVarDecl *> params;
  QualType thisType = Builder.ptrType(Context.getRecordType(CStruct));
  ParmVarDecl *thisParam = Builder.param(thisType, "this");
  params.push_back(thisParam);

  // Generate constructor name: Class__ctor_default
  std::string funcName = D->getName().str() + "__ctor_default";

  // Create C init function
  FunctionDecl *CFunc =
      Builder.funcDecl(funcName, Builder.voidType(), params, nullptr);

  // Bug #19: Make implicit constructors static to avoid linker conflicts
  // Since this is an implicit constructor, it's generated in every translation
  // unit that sees the class. Making it static ensures each TU has its own copy.
  CFunc->setStorageClass(SC_Static);

  // Build function body
  std::vector<Stmt *> stmts;

  // Set translation context
  currentThisParam = thisParam;
  currentMethod = nullptr;

  // 1. Call base class default constructor if derived
  if (D->getNumBases() > 0) {
    for (const CXXBaseSpecifier &Base : D->bases()) {
      CXXRecordDecl *BaseClass = Base.getType()->getAsCXXRecordDecl();
      if (!BaseClass)
        continue;

      std::string baseCtorName = BaseClass->getName().str() + "__ctor_default";
      llvm::outs() << "    TODO: Call base default constructor: "
                   << baseCtorName << "\n";
      // TODO: Look up base constructor and create call expression
      // For now, this is left for Story #63 (Complete Constructor Chaining)
    }
  }

  // 2. Initialize members in declaration order
  for (FieldDecl *Field : D->fields()) {
    QualType fieldType = Field->getType();

    // Create this->field member expression
    MemberExpr *ThisMember =
        Builder.arrowMember(Builder.ref(thisParam), Field->getName());

    if (fieldType->isRecordType()) {
      // Class-type member: call default constructor
      CXXRecordDecl *FieldClass = fieldType->getAsCXXRecordDecl();
      if (FieldClass) {
        std::string fieldCtorName =
            FieldClass->getName().str() + "__ctor_default";

        // Look up the member's default constructor
        // Try implicit name first (_default suffix)
        FunctionDecl *MemberCtor = getCtor(fieldCtorName);

        // If not found, try explicit default constructor name (no suffix)
        if (!MemberCtor) {
          std::string explicitCtorName = FieldClass->getName().str() + "__ctor";
          MemberCtor = getCtor(explicitCtorName);
        }

        // If still not found, try to translate it on-demand
        if (!MemberCtor) {
          // Find the member class's default constructor
          for (CXXConstructorDecl *Ctor : FieldClass->ctors()) {
            if (Ctor->isDefaultConstructor() && !Ctor->isImplicit()) {
              // Translate this explicit default constructor now
              std::string explicitCtorName =
                  FieldClass->getName().str() + "__ctor";
              llvm::outs() << "    On-demand translation of "
                           << explicitCtorName << "\n";
              VisitCXXConstructorDecl(Ctor);
              MemberCtor = getCtor(explicitCtorName);
              break;
            }
          }
        }

        if (MemberCtor) {
          // Create call: MemberClass__ctor_default(&this->member);
          std::vector<Expr *> args;

          // Address of this->member
          Expr *memberAddr = Builder.addrOf(ThisMember);
          args.push_back(memberAddr);

          // Create call expression
          CallExpr *memberCtorCall = Builder.call(MemberCtor, args);
          if (memberCtorCall) {
            stmts.push_back(memberCtorCall);
            llvm::outs() << "    Calling member default constructor: "
                         << fieldCtorName << " for field " << Field->getName()
                         << "\n";
          }
        } else {
          llvm::outs() << "    Warning: Member default constructor not found: "
                       << fieldCtorName << "\n";
        }
      }
    } else if (fieldType->isPointerType()) {
      // Pointer member: initialize to NULL
      Expr *nullExpr = Builder.nullPtr();
      BinaryOperator *Assignment = Builder.assign(ThisMember, nullExpr);
      stmts.push_back(Assignment);
    } else {
      // Primitive member: zero-initialize
      Expr *zeroExpr = Builder.intLit(0);
      BinaryOperator *Assignment = Builder.assign(ThisMember, zeroExpr);
      stmts.push_back(Assignment);
    }
  }

  // Create function body
  CompoundStmt *body = Builder.block(stmts);

  // Set function body
  CFunc->setBody(body);

  llvm::outs() << "  Generated default constructor: " << funcName << "\n";
  return CFunc;
}

/**
 * Story #62: Generate copy constructor
 *
 * Generates: Class__ctor_copy(struct Class *this, const struct Class *other)
 * - Performs memberwise copy for primitive members
 * - Calls copy constructors for class-type members
 * - Performs shallow copy for pointer members
 * - Calls base class copy constructor if derived
 */
FunctionDecl *CppToCVisitor::generateCopyConstructor(CXXRecordDecl *D) {
  // Get the C struct for this class
  RecordDecl *CStruct = cppToCMap[D];
  if (!CStruct) {
    llvm::outs() << "  Warning: C struct not found for copy ctor generation\n";
    return nullptr;
  }

  // Build parameter list: this + other
  std::vector<ParmVarDecl *> params;

  QualType thisType = Builder.ptrType(Context.getRecordType(CStruct));
  ParmVarDecl *thisParam = Builder.param(thisType, "this");
  params.push_back(thisParam);

  // const struct Class *other
  QualType otherType =
      Builder.ptrType(Context.getConstType(Context.getRecordType(CStruct)));
  ParmVarDecl *otherParam = Builder.param(otherType, "other");
  params.push_back(otherParam);

  // Generate constructor name: Class__ctor_copy
  std::string funcName = D->getName().str() + "__ctor_copy";

  // Create C init function
  FunctionDecl *CFunc =
      Builder.funcDecl(funcName, Builder.voidType(), params, nullptr);

  // Bug #19: Make implicit constructors static to avoid linker conflicts
  // Since this is an implicit constructor, it's generated in every translation
  // unit that sees the class. Making it static ensures each TU has its own copy.
  CFunc->setStorageClass(SC_Static);

  // Build function body
  std::vector<Stmt *> stmts;

  // Set translation context
  currentThisParam = thisParam;
  currentMethod = nullptr;

  // 1. Call base class copy constructor if derived
  if (D->getNumBases() > 0) {
    for (const CXXBaseSpecifier &Base : D->bases()) {
      CXXRecordDecl *BaseClass = Base.getType()->getAsCXXRecordDecl();
      if (!BaseClass)
        continue;

      std::string baseCopyCtorName = BaseClass->getName().str() + "__ctor_copy";
      llvm::outs() << "    TODO: Call base copy constructor: "
                   << baseCopyCtorName << "\n";
    }
  }

  // 2. Copy members in declaration order
  for (FieldDecl *Field : D->fields()) {
    QualType fieldType = Field->getType();

    // Create this->field and other->field member expressions
    MemberExpr *ThisMember =
        Builder.arrowMember(Builder.ref(thisParam), Field->getName());

    MemberExpr *OtherMember =
        Builder.arrowMember(Builder.ref(otherParam), Field->getName());

    if (fieldType->isRecordType()) {
      // Class-type member: call copy constructor
      CXXRecordDecl *FieldClass = fieldType->getAsCXXRecordDecl();
      if (FieldClass) {
        std::string fieldCopyCtorName =
            FieldClass->getName().str() + "__ctor_copy";

        // Look up the member's copy constructor
        // Try implicit name first (_copy suffix)
        FunctionDecl *MemberCopyCtor = getCtor(fieldCopyCtorName);

        // If not found, try to translate explicit copy constructor on-demand
        if (!MemberCopyCtor) {
          // Find the member class's copy constructor
          for (CXXConstructorDecl *Ctor : FieldClass->ctors()) {
            if (Ctor->isCopyConstructor() && !Ctor->isImplicit()) {
              // Translate this explicit copy constructor now
              llvm::outs()
                  << "    On-demand translation of explicit copy constructor\n";
              VisitCXXConstructorDecl(Ctor);
              // After translation, look it up directly using the key
              std::string ctorKey = Mangler.mangleConstructor(Ctor);
              auto it = targetCtx.getCtorMap().find(ctorKey);
              if (it != targetCtx.getCtorMap().end()) {
                MemberCopyCtor = it->second;
                llvm::outs() << "    Found copy constructor: "
                             << MemberCopyCtor->getNameAsString() << "\n";
              } else {
                llvm::outs() << "    Warning: Translated copy constructor not "
                                "found in map\n";
              }
              break;
            }
          }
        }

        if (MemberCopyCtor) {
          // Create call: MemberClass__ctor_copy(&this->member, &other->member);
          std::vector<Expr *> args;

          // First arg: address of this->member
          Expr *thisMemberAddr = Builder.addrOf(ThisMember);
          args.push_back(thisMemberAddr);

          // Second arg: address of other->member
          Expr *otherMemberAddr = Builder.addrOf(OtherMember);
          args.push_back(otherMemberAddr);

          // Create call expression
          CallExpr *memberCopyCall = Builder.call(MemberCopyCtor, args);
          if (memberCopyCall) {
            stmts.push_back(memberCopyCall);
            llvm::outs() << "    Calling member copy constructor: "
                         << MemberCopyCtor->getNameAsString() << " for field "
                         << Field->getName() << "\n";
          }
        } else {
          llvm::outs() << "    Warning: Member copy constructor not found: "
                       << fieldCopyCtorName << "\n";
        }
      }
    } else if (fieldType->isArrayType()) {
      // Array member: use memcpy for deep copy
      // memcpy(&this->field, &other->field, sizeof(this->field));

      // Get array size
      const ConstantArrayType *ArrayTy =
          Context.getAsConstantArrayType(fieldType);
      if (ArrayTy) {
        // Create memcpy function reference
        // We assume memcpy is available (added in generated headers)
        IdentifierInfo *MemcpyIdent = &Context.Idents.get("memcpy");
        DeclarationName MemcpyName(MemcpyIdent);

        // Create a placeholder function decl for memcpy
        // void *memcpy(void *dest, const void *src, size_t n)
        QualType VoidPtrTy = Context.getPointerType(Context.VoidTy);
        QualType ConstVoidPtrTy = Context.getPointerType(
            Context.getConstType(Context.VoidTy));
        QualType SizeTy = Context.getSizeType();

        std::vector<ParmVarDecl *> memcpyParams;
        memcpyParams.push_back(Builder.param(VoidPtrTy, "dest"));
        memcpyParams.push_back(Builder.param(ConstVoidPtrTy, "src"));
        memcpyParams.push_back(Builder.param(SizeTy, "n"));

        FunctionDecl *MemcpyDecl = Builder.funcDecl(
            "memcpy", VoidPtrTy, memcpyParams, nullptr);

        // Create arguments for memcpy call
        std::vector<Expr *> args;
        args.push_back(Builder.addrOf(ThisMember));    // dest
        args.push_back(Builder.addrOf(OtherMember));   // src

        // sizeof(this->field)
        Expr *SizeofExpr = new (Context) UnaryExprOrTypeTraitExpr(
            UETT_SizeOf, ThisMember, Context.getSizeType(),
            SourceLocation(), SourceLocation());
        args.push_back(SizeofExpr);

        // Create memcpy call
        CallExpr *MemcpyCall = Builder.call(MemcpyDecl, args);
        if (MemcpyCall) {
          stmts.push_back(MemcpyCall);
          llvm::outs() << "    Using memcpy for array field: "
                       << Field->getName() << "\n";
        }
      }
    } else {
      // Primitive or pointer member: memberwise (shallow) copy
      BinaryOperator *Assignment = Builder.assign(ThisMember, OtherMember);
      stmts.push_back(Assignment);
    }
  }

  // Create function body
  CompoundStmt *body = Builder.block(stmts);

  // Set function body
  CFunc->setBody(body);

  llvm::outs() << "  Generated copy constructor: " << funcName << "\n";
  return CFunc;
}

// ============================================================================
// Prompt #031: extern "C" and Calling Convention Support
// ============================================================================

/**
 * @brief Visit linkage specification declarations (extern "C" blocks)
 *
 * This visitor method is called automatically by Clang's AST traversal when
 * encountering extern "C" { } or extern "C++" { } blocks.
 *
 * Note: The actual linkage information is already available via
 * FunctionDecl::isExternC() and FunctionDecl::getLanguageLinkage(), so
 * this visitor is primarily for logging/debugging purposes.
 *
 * @param LS The LinkageSpecDecl node
 * @return true to continue visiting children
 */
bool CppToCVisitor::VisitLinkageSpecDecl(clang::LinkageSpecDecl *LS) {
  if (!LS) {
    return true;
  }

  // Optional: Track entering extern "C" or extern "C++" blocks for debugging
  // TODO: Fix enum access for LLVM 15 - LinkageSpecDecl::LanguageIDs may have
  // different API if (LS->getLanguage() ==
  // LinkageSpecDecl::LanguageIDs::lang_c) {
  //   // This is an extern "C" block
  //   // In the future, we could add logging here if needed
  //   // llvm::outs() << "Entering extern \"C\" block\n";
  // } else if (LS->getLanguage() == LinkageSpecDecl::LanguageIDs::lang_cxx) {
  //   // This is an extern "C++" block (rare, but possible)
  //   // llvm::outs() << "Entering extern \"C++\" block\n";
  // }

  // Continue visiting child declarations (functions, variables, etc.)
  return true;
}

// ============================================================================
// Phase 12: Exception Handling Implementation (v2.5.0)
// ============================================================================

/**
 * @brief Visit C++ try-catch statements and translate to setjmp/longjmp control
 * flow
 *
 * This method is called automatically by Clang's AST traversal when
 * encountering C++ try-catch blocks. It uses TryCatchTransformer to generate:
 * - Exception frame structure
 * - setjmp guard for catching exceptions
 * - Catch handler dispatch with type matching
 * - Frame push/pop operations
 *
 * @param S The CXXTryStmt AST node
 * @return false to prevent default traversal (we handle the try-catch
 * ourselves)
 */
bool CppToCVisitor::VisitCXXTryStmt(CXXTryStmt *S) {
  if (!S) {
    return true;
  }

  llvm::outs() << "Translating try-catch block...\n";

  // Generate unique frame and action table names
  std::string frameVarName =
      "frame_" + std::to_string(m_exceptionFrameCounter++);
  std::string actionsTableName =
      "actions_table_" + std::to_string(m_tryBlockCounter++);

  // Use TryCatchTransformer to generate complete try-catch code
  std::string transformedCode = m_tryCatchTransformer->transformTryCatch(
      S, frameVarName, actionsTableName);

  // Output the transformed code
  llvm::outs() << transformedCode;

  llvm::outs() << "Try-catch block translated successfully\n";

  // Return false to prevent default traversal (we handle the try-catch block
  // ourselves)
  return false;
}

/**
 * @brief Visit C++ throw expressions and translate to cxx_throw runtime calls
 *
 * This method is called automatically by Clang's AST traversal when
 * encountering C++ throw expressions. It uses ThrowTranslator to generate:
 * - Exception object allocation (malloc)
 * - Constructor call with arguments
 * - Type info extraction
 * - cxx_throw runtime call (never returns, performs longjmp)
 *
 * @param E The CXXThrowExpr AST node
 * @return true to indicate we've handled this expression
 */
bool CppToCVisitor::VisitCXXThrowExpr(CXXThrowExpr *E) {
  if (!E) {
    return true;
  }

  llvm::outs() << "Translating throw expression...\n";

  std::string throwCode;

  if (E->getSubExpr()) {
    // throw expression;
    throwCode = m_throwTranslator->generateThrowCode(E);
  } else {
    // throw; (re-throw)
    throwCode = m_throwTranslator->generateRethrowCode();
  }

  // Output the throw code
  llvm::outs() << throwCode;

  llvm::outs() << "Throw expression translated successfully\n";

  // Return true to indicate we've handled this
  return true;
}

// ============================================================================
// Phase 13: RTTI Translation Implementation (v2.6.0)
// ============================================================================

/**
 * @brief Visit C++ typeid expressions and translate to type_info retrieval
 *
 * This method is called automatically by Clang's AST traversal when
 * encountering C++ typeid expressions. It uses TypeidTranslator to generate:
 * - Polymorphic typeid: vtable lookup (ptr->vptr->type_info)
 * - Static typeid: compile-time constant (&__ti_ClassName)
 *
 * Examples:
 * C++: const std::type_info& ti = typeid(*ptr);  // Polymorphic
 * C:   const struct __class_type_info *ti = ptr->vptr->type_info;
 *
 * C++: const std::type_info& ti = typeid(Base);  // Static
 * C:   const struct __class_type_info *ti = &__ti_Base;
 *
 * @param E The CXXTypeidExpr AST node
 * @return true to continue traversal
 */
bool CppToCVisitor::VisitCXXTypeidExpr(CXXTypeidExpr *E) {
  if (!E) {
    return true;
  }

  // Check if RTTI is enabled
  if (!shouldEnableRTTI()) {
    llvm::errs() << "Error: typeid expression requires --enable-rtti flag\n";
    return true;
  }

  llvm::outs() << "Translating typeid expression...\n";

  // Translate using TypeidTranslator
  std::string typeidCode = m_typeidTranslator->translateTypeid(E);

  // Output the translated code
  if (!typeidCode.empty()) {
    llvm::outs() << "Typeid translation: " << typeidCode << "\n";
  } else {
    llvm::outs() << "Warning: typeid translation produced empty result\n";
  }

  llvm::outs() << "Typeid expression translated successfully\n";

  // Return true to continue traversal of subexpressions
  return true;
}

/**
 * @brief Visit C++ dynamic_cast expressions and translate to cxx_dynamic_cast
 * calls
 *
 * This method is called automatically by Clang's AST traversal when
 * encountering C++ dynamic_cast expressions. It uses DynamicCastTranslator to
 * generate:
 * - Runtime type checking via cxx_dynamic_cast()
 * - Returns NULL on failed cast
 * - Handles single and multiple inheritance hierarchies
 *
 * Example:
 * C++: Derived* d = dynamic_cast<Derived*>(base_ptr);
 * C:   struct Derived *d = (struct Derived*)cxx_dynamic_cast(
 *        (const void*)base_ptr,
 *        &__ti_Base,
 *        &__ti_Derived,
 *        -1
 *      );
 *
 * @param E The CXXDynamicCastExpr AST node
 * @return true to continue traversal
 */
/**
 * @brief Visit C++23 multidimensional subscript operator calls
 *
 * Detects and translates multidimensional subscript operators (operator[](T1, T2, ...))
 * to equivalent C function calls.
 *
 * C++23: m[i, j] = 42;
 * C:     *Matrix__subscript_2d(&m, i, j) = 42;
 *
 * @param E The CXXOperatorCallExpr AST node
 * @return true to continue traversal
 */
bool CppToCVisitor::VisitCXXOperatorCallExpr(CXXOperatorCallExpr *E) {
  if (!E) {
    return true;
  }

  // Phase 34 (v2.5.0): Skip expressions from non-transpilable files
  // For expressions, we check the source location against SourceManager
  if (!Context.getSourceManager().isInMainFile(E->getBeginLoc())) {
    // TODO: Enhance FileOriginTracker to support SourceLocation directly
    return true;
  }

  // Get the method declaration
  auto* MethodDecl = dyn_cast_or_null<CXXMethodDecl>(E->getCalleeDecl());
  if (!MethodDecl) {
    return true;
  }

  // Phase 2: Handle static operator() and operator[] call sites (C++23)
  if (MethodDecl->isStatic() &&
      (E->getOperator() == OO_Call || E->getOperator() == OO_Subscript)) {
    llvm::outs() << "  -> Translating static operator call\n";

    auto* C_Call = m_staticOperatorTrans->transformCall(E, Context);
    if (C_Call) {
      // Translation successful
      // Note: AST replacement would happen here in a full implementation
      // For now, we've generated the call expression
      llvm::outs() << "     Generated static operator call\n";
    }
    return true;
  }

  // Phase 50: Handle arithmetic operator call sites (v2.10.0)
  if (m_arithmeticOpTrans->isArithmeticOperator(E->getOperator())) {
    llvm::outs() << "  -> Translating arithmetic operator call\n";
    auto* C_Call = m_arithmeticOpTrans->transformCall(E, Context);
    if (C_Call) {
      // Translation successful
      // Note: AST replacement would happen here in a full implementation
      llvm::outs() << "     Generated arithmetic operator call\n";
    }
    return true;
  }

  // Phase 51: Handle comparison & logical operator call sites (v2.11.0)
  if (m_comparisonOpTrans->isComparisonOperator(E->getOperator())) {
    llvm::outs() << "  -> Translating comparison/logical operator call\n";
    auto* C_Call = m_comparisonOpTrans->transformCall(E, Context);
    if (C_Call) {
      // Translation successful
      // Note: AST replacement would happen here in a full implementation
      llvm::outs() << "     Generated comparison/logical operator call (returns bool)\n";
    }
    return true;
  }

  // Phase 52: Handle special operator call sites (v2.12.0)
  // Includes: operator[], operator(), operator->, operator*, operator<<, operator>>,
  // operator=, operator&, operator, (comma)
  if (m_specialOpTrans->isSpecialOperator(E->getOperator())) {
    llvm::outs() << "  -> Translating special operator call\n";
    auto* C_Call = m_specialOpTrans->transformCall(E, Context);
    if (C_Call) {
      // Translation successful
      // Note: AST replacement would happen here in a full implementation
      llvm::outs() << "     Generated special operator call\n";
    }
    return true;
  }

  // Phase 1: Check if this is a multidimensional subscript operator
  if (E->getOperator() == OO_Subscript && E->getNumArgs() >= 3) {
    // This is a multidimensional subscript (object + 2+ indices)
    llvm::outs() << "  -> Translating multidimensional subscript operator ["
                 << (E->getNumArgs() - 1) << "D]\n";

    auto* C_Call = m_multidimSubscriptTrans->transform(E, Context, C_TranslationUnit);
    if (C_Call) {
      // Translation successful
      // Note: AST replacement would happen here in a full implementation
      // For now, we've generated the function declaration in C_TranslationUnit
    }
  }

  return true;
}

bool CppToCVisitor::VisitCXXDynamicCastExpr(CXXDynamicCastExpr *E) {
  if (!E) {
    return true;
  }

  // Check if RTTI is enabled
  if (!shouldEnableRTTI()) {
    llvm::errs()
        << "Error: dynamic_cast expression requires --enable-rtti flag\n";
    return true;
  }

  llvm::outs() << "Translating dynamic_cast expression...\n";

  // Translate using DynamicCastTranslator
  std::string dynamicCastCode =
      m_dynamicCastTranslator->translateDynamicCast(E);

  // Output the translated code
  if (!dynamicCastCode.empty()) {
    llvm::outs() << "Dynamic cast translation: " << dynamicCastCode << "\n";
  } else {
    llvm::outs() << "Warning: dynamic_cast translation produced empty result\n";
  }

  llvm::outs() << "Dynamic cast expression translated successfully\n";

  // Return true to continue traversal of subexpressions
  return true;
}

// ============================================================================
// Epic #193: ACSL Annotation Generation Implementation
// ============================================================================

void CppToCVisitor::emitACSL(const std::string &acsl, ACSLOutputMode mode) {
  if (acsl.empty()) {
    return; // Nothing to emit
  }

  if (mode == ACSLOutputMode::Inline) {
    // Emit ACSL as inline comments in the C output
    llvm::outs() << "/*@\n" << acsl << "\n*/\n";
  } else {
    // For separate mode, store the annotation for later output
    // Note: Actual file writing will be handled by FileOutputManager or
    // Consumer For now, we just output to stdout with a marker
    llvm::outs() << "/* ACSL (separate mode): */\n";
    llvm::outs() << "/*@\n" << acsl << "\n*/\n";
  }
}

void CppToCVisitor::storeACSLAnnotation(const std::string &key,
                                        const std::string &acsl) {
  if (!acsl.empty()) {
    m_acslAnnotations[key] = acsl;
  }
}

// ============================================================================
// Phase 11: Template Monomorphization Implementation (v2.4.0)
// ============================================================================

/**
 * @brief Visit class template declarations
 *
 * ClassTemplateDecl is the template itself (e.g., template<typename T> class
 * Stack). We don't generate code for the template directly. Instead, we let
 * TemplateExtractor find all specializations during AST traversal.
 *
 * This visitor just marks that we've seen a template declaration.
 */
bool CppToCVisitor::VisitClassTemplateDecl(ClassTemplateDecl *D) {
  if (!D || !shouldMonomorphizeTemplates()) {
    return true;
  }

  // Phase 34 (v2.5.0): Skip declarations from non-transpilable files
  if (!fileOriginTracker.shouldTranspile(D)) {
    return true;
  }

  llvm::outs() << "Found class template: " << D->getNameAsString() << "\n";
  // Don't generate code here - wait for instantiations
  return true;
}

/**
 * @brief Visit function template declarations
 *
 * FunctionTemplateDecl is the template itself (e.g., template<typename T> T
 * max(T, T)). We don't generate code for the template directly.
 * TemplateExtractor will find all specializations.
 */
bool CppToCVisitor::VisitFunctionTemplateDecl(FunctionTemplateDecl *D) {
  if (!D || !shouldMonomorphizeTemplates()) {
    return true;
  }

  // Phase 34 (v2.5.0): Skip declarations from non-transpilable files
  if (!fileOriginTracker.shouldTranspile(D)) {
    return true;
  }

  llvm::outs() << "Found function template: " << D->getNameAsString() << "\n";
  // Don't generate code here - wait for instantiations
  return true;
}

/**
 * @brief Visit class template specializations
 *
 * ClassTemplateSpecializationDecl represents a specific instantiation
 * (e.g., Stack<int>, Stack<double>). The TemplateExtractor will collect these
 * during traversal, and we'll process them in processTemplateInstantiations().
 */
bool CppToCVisitor::VisitClassTemplateSpecializationDecl(
    ClassTemplateSpecializationDecl *D) {
  if (!D || !shouldMonomorphizeTemplates()) {
    return true;
  }

  // Phase 34 (v2.5.0): Skip declarations from non-transpilable files
  if (!fileOriginTracker.shouldTranspile(D)) {
    return true;
  }

  // Log the specialization (TemplateExtractor handles collection)
  std::string templateName = D->getSpecializedTemplate()->getNameAsString();
  llvm::outs() << "Found class template specialization: " << templateName
               << "<";

  const TemplateArgumentList &args = D->getTemplateArgs();
  for (unsigned i = 0; i < args.size(); ++i) {
    if (i > 0)
      llvm::outs() << ", ";
    const TemplateArgument &arg = args[i];
    if (arg.getKind() == TemplateArgument::Type) {
      llvm::outs() << arg.getAsType().getAsString();
    } else if (arg.getKind() == TemplateArgument::Integral) {
      llvm::outs() << arg.getAsIntegral();
    }
  }
  llvm::outs() << ">\n";

  return true;
}

/**
 * @brief Process all template instantiations and generate monomorphized C code
 *
 * This method is called after the AST traversal is complete. It:
 * 1. Uses TemplateExtractor to find all instantiations
 * 2. Deduplicates using TemplateInstantiationTracker
 * 3. Generates C code using TemplateMonomorphizer
 * 4. Stores the result in m_monomorphizedCode
 */
void CppToCVisitor::processTemplateInstantiations(TranslationUnitDecl *TU) {
  if (!shouldMonomorphizeTemplates() || !TU) {
    return;
  }

  llvm::outs() << "\n========================================\n";
  llvm::outs() << "Processing Template Instantiations\n";
  llvm::outs() << "========================================\n\n";

  // Step 1: Extract all template instantiations from the AST
  m_templateExtractor->extractTemplateInstantiations(TU);

  auto classInsts = m_templateExtractor->getClassInstantiations();
  auto funcInsts = m_templateExtractor->getFunctionInstantiations();

  llvm::outs() << "Found " << classInsts.size()
               << " class template instantiation(s)\n";
  llvm::outs() << "Found " << funcInsts.size()
               << " function template instantiation(s)\n";

  // Check instantiation limit
  unsigned int limit = getTemplateInstantiationLimit();
  unsigned int totalInsts = classInsts.size() + funcInsts.size();

  if (totalInsts > limit) {
    llvm::errs() << "Error: Template instantiation limit exceeded!\n";
    llvm::errs() << "  Found: " << totalInsts << " instantiations\n";
    llvm::errs() << "  Limit: " << limit << "\n";
    llvm::errs()
        << "  Use --template-instantiation-limit=<N> to increase the limit\n";
    return;
  }

  // Phase 32.1: AST-based template monomorphization
  // Generate C AST nodes and add them to C_TranslationUnit

  // Step 2: Process class template instantiations
  llvm::outs() << "\nMonomorphizing class templates:\n";
  for (auto *classInst : classInsts) {
    // Generate unique key for deduplication
    std::string key = m_templateExtractor->getClassInstantiationKey(classInst);

    // Check if already processed (deduplication)
    if (!m_templateTracker->addInstantiation(key)) {
      llvm::outs() << "  Skipping duplicate: " << key << "\n";
      continue;
    }

    llvm::outs() << "  Generating AST for: " << key << "\n";

    // Generate monomorphized C struct AST node
    RecordDecl* CStruct = m_templateMonomorphizer->monomorphizeClass(classInst);
    if (CStruct) {
      // BUG #3 FIX: Add struct to per-file C_TranslationUnit for emission
      // CNodeBuilder adds to shared TU, but we need it in per-file C_TU
      C_TranslationUnit->addDecl(CStruct);
      llvm::outs() << "    -> Created struct: " << CStruct->getNameAsString() << " and added to C_TU\n";

      // Generate method functions
      std::vector<FunctionDecl*> methods =
          m_templateMonomorphizer->monomorphizeClassMethods(classInst, CStruct);

      // BUG #3 FIX: Add method functions to per-file C_TranslationUnit for emission
      for (FunctionDecl* method : methods) {
        C_TranslationUnit->addDecl(method);
      }

      llvm::outs() << "    -> Created " << methods.size() << " method function(s) and added to C_TU\n";

      // BUG FIX: Translate method bodies for monomorphized functions
      // The monomorphizer creates function signatures, but bodies need translation
      //
      // NOTE: We use the INSTANTIATION's methods (classInst), not the pattern,
      // because template method out-of-line definitions are not associated with
      // the pattern's method declarations. The instantiation has all bodies.

      // Get template pattern to access method list
      ClassTemplateDecl* Template = classInst->getSpecializedTemplate();
      CXXRecordDecl* Pattern = Template ? Template->getTemplatedDecl() : nullptr;

      if (Pattern) {
        // Build a map of pattern methods (these have the names we need)
        std::map<std::string, CXXMethodDecl*> methodMap;
        for (auto* PatternMethod : Pattern->methods()) {
          // Skip compiler-generated, constructors, destructors (same as monomorphizer)
          if (PatternMethod->isImplicit()) continue;
          if (isa<CXXConstructorDecl>(PatternMethod) || isa<CXXDestructorDecl>(PatternMethod)) {
            continue;
          }
          std::string methodName = PatternMethod->getNameAsString();
          llvm::outs() << "      -> Found pattern method: " << methodName << "\n";
          methodMap[methodName] = PatternMethod;
        }

        // Translate bodies for each monomorphized method
        std::string className = CStruct->getNameAsString();
        for (FunctionDecl* MonoFunc : methods) {
          // Extract method name from monomorphized function name
          // Format: ClassName_methodName
          std::string funcName = MonoFunc->getNameAsString();
          std::string prefix = className + "_";
          if (funcName.find(prefix) != 0) {
            llvm::outs() << "      -> Warning: Unexpected function name format: " << funcName << "\n";
            continue;
          }

          std::string methodName = funcName.substr(prefix.length());

          // Find corresponding pattern method
          auto it = methodMap.find(methodName);
          if (it == methodMap.end()) {
            llvm::outs() << "      -> Warning: No method found for: " << methodName << "\n";
            continue;
          }

          CXXMethodDecl* PatternMethod = it->second;

          // The key insight: For template instantiations, we need to get the
          // body from the INSTANTIATED version. Use getTemplateInstantiationPattern
          // to find the original template, then walk to the instantiated body.
          //
          // If the pattern method is inline (body in class), it will have hasBody() = true
          // If it's out-of-line, we need to look for it in the TU declarations
          Stmt* BodyToTranslate = nullptr;

          // First try: Check if pattern has inline body
          if (PatternMethod->hasBody()) {
            llvm::outs() << "      -> Method " << methodName << " has inline body\n";
            BodyToTranslate = PatternMethod->getBody();
          } else {
            // Out-of-line definition - need to find it
            // For templates, the actual instantiated body exists in the AST
            // We need to search for the FunctionDecl that corresponds to this instantiation
            llvm::outs() << "      -> Method " << methodName << " has out-of-line definition, searching...\n";

            // Search all decls in TranslationUnit for this method's definition
            for (auto* Decl : Context.getTranslationUnitDecl()->decls()) {
              if (auto* FuncTemplate = dyn_cast<FunctionTemplateDecl>(Decl)) {
                // Check if this is the template definition for our method
                if (FuncTemplate->getTemplatedDecl()->getNameAsString() == methodName) {
                  // This might be it, but we need the instantiated version
                  // For now, try the templated decl
                  if (FuncTemplate->getTemplatedDecl()->hasBody()) {
                    llvm::outs() << "      -> Found function template definition!\n";
                    BodyToTranslate = FuncTemplate->getTemplatedDecl()->getBody();
                    break;
                  }
                }
              }
            }
          }

          if (BodyToTranslate) {
            llvm::outs() << "      -> Translating body for " << funcName << "\n";

            // Set up translation context
            if (MonoFunc->getNumParams() > 0) {
              currentThisParam = MonoFunc->getParamDecl(0);  // First param is 'this'
            }
            currentMethod = PatternMethod;

            // Bug #38 FIX: Set nested class mappings for this template
            // This allows translateDeclStmt() to substitute nested class types
            // E.g., "Node*" -> "struct LinkedList_int_Node*"
            currentNestedClassMappings = &m_templateMonomorphizer->getNestedClassMappings();

            // Translate the method body
            Stmt* TranslatedBody = translateStmt(BodyToTranslate);

            if (TranslatedBody) {
              MonoFunc->setBody(TranslatedBody);
              llvm::outs() << "      -> Body translated successfully\n";
            } else {
              llvm::outs() << "      -> Warning: Body translation returned nullptr\n";
            }

            // Clear translation context
            currentThisParam = nullptr;
            currentMethod = nullptr;
            currentNestedClassMappings = nullptr;
          } else {
            llvm::outs() << "      -> Warning: Could not find body for method: " << methodName << "\n";
          }
        }
      }
    }
  }

  // Step 3: Process function template instantiations
  llvm::outs() << "\nMonomorphizing function templates:\n";
  for (auto *funcInst : funcInsts) {
    // Generate unique key for deduplication
    std::string key =
        m_templateExtractor->getFunctionInstantiationKey(funcInst);

    // Check if already processed (deduplication)
    if (!m_templateTracker->addInstantiation(key)) {
      llvm::outs() << "  Skipping duplicate: " << key << "\n";
      continue;
    }

    llvm::outs() << "  Generating AST for: " << key << "\n";

    // Generate monomorphized C function AST node
    FunctionDecl* CFunc = m_templateMonomorphizer->monomorphizeFunction(funcInst);
    if (CFunc) {
      // BUG #3 FIX: Add function to per-file C_TranslationUnit for emission
      // CNodeBuilder adds to shared TU, but we need it in per-file C_TU
      C_TranslationUnit->addDecl(CFunc);
      llvm::outs() << "    -> Created function: " << CFunc->getNameAsString() << " and added to C_TU\n";
    }
  }

  llvm::outs() << "\n========================================\n";
  llvm::outs() << "Template Monomorphization Complete\n";
  llvm::outs() << "  Unique instantiations: " << m_templateTracker->getCount()
               << "\n";
  llvm::outs() << "========================================\n\n";

  // Phase 32.1: AST nodes are already added to C_TranslationUnit by CNodeBuilder
  // No need to output string-based code anymore
}

// ============================================================================
// Phase 31-03: COM-Style Static Declarations for All Methods
// ============================================================================

std::string CppToCVisitor::generateAllMethodDeclarations(CXXRecordDecl *RD) {
  if (!RD) {
    return "";
  }

  std::ostringstream decls;
  std::string className = RD->getNameAsString();

  // Add comment header
  decls << "// Static declarations for all " << className << " methods\n";

  int ctorCount = 0;
  int dtorCount = 0;
  int methodCount = 0;

  // Constructors
  for (auto *ctor : RD->ctors()) {
    // Skip compiler-generated implicit constructors
    if (!ctor->isImplicit()) {
      decls << MethodSignatureHelper::generateSignature(ctor, className)
            << ";\n";
      ctorCount++;
    }
  }

  // Destructor
  if (CXXDestructorDecl *dtor = RD->getDestructor()) {
    // Skip compiler-generated implicit destructor
    if (!dtor->isImplicit()) {
      decls << MethodSignatureHelper::generateSignature(dtor, className)
            << ";\n";
      dtorCount++;
    }
  }

  // All methods (virtual and non-virtual)
  for (auto *method : RD->methods()) {
    // Skip implicit methods (compiler-generated)
    if (method->isImplicit()) {
      continue;
    }

    // Skip constructors and destructors (already handled above)
    if (isa<CXXConstructorDecl>(method) || isa<CXXDestructorDecl>(method)) {
      continue;
    }

    decls << MethodSignatureHelper::generateSignature(method, className)
          << ";\n";
    methodCount++;
  }

  llvm::outs() << "  [Phase 31-03] Generated " << ctorCount << " constructor, "
               << dtorCount << " destructor, " << methodCount
               << " method declarations\n";

  return decls.str();
}

// Phase 3: [[assume]] Attribute Handler (C++23 P1774R8)
bool CppToCVisitor::VisitAttributedStmt(AttributedStmt *S) {
  // Phase 34 (v2.5.0): Skip statements from non-transpilable files
  // For statements, we check the source location against SourceManager
  if (!Context.getSourceManager().isInMainFile(S->getBeginLoc())) {
    // TODO: Enhance FileOriginTracker to support SourceLocation directly
    return true;
  }

  // Check if this is an assume attribute
  bool hasAssumeAttr = false;
  for (const auto *Attr : S->getAttrs()) {
    if (isa<CXXAssumeAttr>(Attr)) {
      hasAssumeAttr = true;
      break;
    }
  }

  if (!hasAssumeAttr) {
    // Not an assume attribute, continue traversal
    return true;
  }

  // Handle the assume attribute
  Stmt *TransformedStmt = m_assumeHandler->handle(S, Context);

  if (TransformedStmt && TransformedStmt != S) {
    // The attribute was successfully transformed
    // In a full implementation, we would replace S with TransformedStmt
    // in the C AST. For now, we just log the transformation.
    llvm::outs() << "  [Phase 3] Transformed [[assume]] attribute\n";
  }

  return true;
}

// Phase 5: if consteval visitor (C++23 P1938R3)
bool CppToCVisitor::VisitIfStmt(IfStmt *S) {
  // Phase 34 (v2.5.0): Skip statements from non-transpilable files
  // For statements, we check the source location against SourceManager
  if (!Context.getSourceManager().isInMainFile(S->getBeginLoc())) {
    // TODO: Enhance FileOriginTracker to support SourceLocation directly
    return true;
  }

  // Check if this is an 'if consteval' statement
  if (!S->isConsteval()) {
    // Regular if statement, not if consteval - continue normal traversal
    return true;
  }

  // This is an 'if consteval' statement - transform it
  llvm::outs() << "  [Phase 5] Processing if consteval at "
               << S->getBeginLoc().printToString(Context.getSourceManager()) << "\n";

  // Transform the consteval-if to C
  Stmt *TransformedStmt = m_constevalIfTrans->transform(S, Context);

  if (TransformedStmt) {
    // Successfully transformed
    // In a full implementation, we would replace S with TransformedStmt
    // in the C AST. For now, we log the transformation.
    llvm::outs() << "  [Phase 5] Transformed if consteval to runtime branch\n";
  } else {
    // No transformation (e.g., no else branch and runtime strategy)
    llvm::outs() << "  [Phase 5] if consteval has no runtime branch - emitting null statement\n";
  }

  return true;
}

// Phase 6: auto(x) decay-copy visitor (C++23 P0849R8)
bool CppToCVisitor::VisitCXXFunctionalCastExpr(CXXFunctionalCastExpr *E) {
  // Phase 34 (v2.5.0): Skip expressions from non-transpilable files
  // For expressions, we check the source location against SourceManager
  if (!Context.getSourceManager().isInMainFile(E->getBeginLoc())) {
    // TODO: Enhance FileOriginTracker to support SourceLocation directly
    return true;
  }

  // Check if this is auto(x) or auto{x}
  QualType TypeAsWritten = E->getTypeAsWritten();
  const Type* TypePtr = TypeAsWritten.getTypePtr();
  if (!TypePtr || !isa<AutoType>(TypePtr)) {
    // Not auto(x), continue normal traversal
    return true;
  }

  // This is an auto(x) or auto{x} expression - transform it
  llvm::outs() << "  [Phase 6] Processing auto(x) at "
               << E->getBeginLoc().printToString(Context.getSourceManager()) << "\n";

  // Transform the auto(x) to C
  Expr *TransformedExpr = m_autoDecayTrans->transform(E, Context);

  if (TransformedExpr) {
    // Successfully transformed
    // In a full implementation, we would replace E with TransformedExpr
    // in the C AST. For now, we log the transformation.
    llvm::outs() << "  [Phase 6] Transformed auto(x) with type decay\n";
  } else {
    // Transformation failed or not applicable
    llvm::outs() << "  [Phase 6] auto(x) transformation skipped\n";
  }

  return true;
}
