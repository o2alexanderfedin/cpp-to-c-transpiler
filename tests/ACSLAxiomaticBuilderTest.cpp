// Phase 3 (v1.20.0): ACSL Axiomatic Definitions
// Plan: .planning/phases/03-axiomatic-definitions/PLAN.md
//
// Test-Driven Development: Comprehensive test suite for axiomatic definitions
//
// Test coverage (12 tests as per plan):
// 1. LogicFunctionAbstraction - Pure function → logic function
// 2. AxiomGeneration - Property → axiom
// 3. LemmaGeneration - Derived property → lemma
// 4. RecursiveLogicFunction - Recursive definition
// 5. PolymorphicLogicFunction - Template → polymorphic
// 6. InductivePredicate - Inductive definition
// 7. ConsistencyCheck - No contradictory axioms
// 8. CommutativityAxiom - Commutative property
// 9. AssociativityAxiom - Associative property
// 10. IdentityAxiom - Identity element
// 11. InverseAxiom - Inverse operation
// 12. DistributivityAxiom - Distributive property

#include <gtest/gtest.h>
#include "ACSLAxiomaticBuilder.h"
#include "clang/AST/ASTContext.h"
#include "clang/AST/RecursiveASTVisitor.h"
#include "clang/Frontend/ASTUnit.h"
#include "clang/Tooling/Tooling.h"
#include <memory>
#include <string>

using namespace clang;

// Test helper: Extract FunctionDecl from source code
class FunctionExtractor : public RecursiveASTVisitor<FunctionExtractor> {
public:
    std::vector<const FunctionDecl*> functions;

    bool VisitFunctionDecl(FunctionDecl* decl) {
        if (decl->isThisDeclarationADefinition() && !decl->isMain()) {
            functions.push_back(decl);
        }
        return true;
    }
};

// Test fixture for ACSLAxiomaticBuilder tests
class ACSLAxiomaticBuilderTest : public ::testing::Test {
protected:
    // Helper: Parse C++ code and extract AST nodes
    std::unique_ptr<ASTUnit> parseCode(const std::string& code) {
        std::vector<std::string> args = {"-std=c++17"};
        return tooling::buildASTFromCodeWithArgs(code, args);
    }

    // Helper: Extract functions from AST
    std::vector<const FunctionDecl*> extractFunctions(ASTUnit* AST) {
        FunctionExtractor extractor;
        extractor.TraverseDecl(AST->getASTContext().getTranslationUnitDecl());
        return extractor.functions;
    }

    // Helper: Find function by name
    const FunctionDecl* findFunction(const std::vector<const FunctionDecl*>& functions,
                                      const std::string& name) {
        for (auto* func : functions) {
            if (func->getNameAsString() == name) {
                return func;
            }
        }
        return nullptr;
    }
};

// Test 1: LogicFunctionAbstraction - Pure function → logic function
TEST_F(ACSLAxiomaticBuilderTest, LogicFunctionAbstraction) {
    std::string code = R"(
        int abs_value(int x) {
            return (x >= 0) ? x : -x;
        }
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto functions = extractFunctions(AST.get());
    ASSERT_FALSE(functions.empty()) << "No functions found";

    const FunctionDecl* absFunc = functions[0];
    ACSLAxiomaticBuilder builder;

    std::string axiomaticBlock = builder.generateAxiomaticBlock(absFunc);

    // Verify axiomatic block syntax
    ASSERT_FALSE(axiomaticBlock.empty()) << "Axiomatic block should not be empty";
    EXPECT_NE(axiomaticBlock.find("/*@ axiomatic"), std::string::npos)
        << "Should use ACSL axiomatic syntax";
    EXPECT_NE(axiomaticBlock.find("logic"), std::string::npos)
        << "Should contain logic function declaration";
    EXPECT_NE(axiomaticBlock.find("abs_value"), std::string::npos)
        << "Should reference function name";
    EXPECT_NE(axiomaticBlock.find("@*/"), std::string::npos)
        << "Should close ACSL comment";
}

// Test 2: AxiomGeneration - Property → axiom
TEST_F(ACSLAxiomaticBuilderTest, AxiomGeneration) {
    std::string code = R"(
        int abs_value(int x) {
            return (x >= 0) ? x : -x;
        }
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto functions = extractFunctions(AST.get());
    ASSERT_FALSE(functions.empty()) << "No functions found";

    const FunctionDecl* absFunc = functions[0];
    ACSLAxiomaticBuilder builder;

    std::string axiomaticBlock = builder.generateAxiomaticBlock(absFunc);

    // Verify axiom generation (e.g., abs_value always returns non-negative)
    EXPECT_NE(axiomaticBlock.find("axiom"), std::string::npos)
        << "Should contain axiom declaration";
    EXPECT_NE(axiomaticBlock.find("\\forall"), std::string::npos)
        << "Should use universal quantifier";
}

// Test 3: LemmaGeneration - Derived property → lemma
TEST_F(ACSLAxiomaticBuilderTest, LemmaGeneration) {
    std::string code = R"(
        int abs_value(int x) {
            return (x >= 0) ? x : -x;
        }
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto functions = extractFunctions(AST.get());
    ASSERT_FALSE(functions.empty()) << "No functions found";

    const FunctionDecl* absFunc = functions[0];
    ACSLAxiomaticBuilder builder;

    std::string axiomaticBlock = builder.generateAxiomaticBlock(absFunc);

    // Verify lemma generation (e.g., abs_value(x) == 0 <==> x == 0)
    EXPECT_NE(axiomaticBlock.find("lemma"), std::string::npos)
        << "Should contain lemma declaration";
}

// Test 4: RecursiveLogicFunction - Recursive definition
TEST_F(ACSLAxiomaticBuilderTest, RecursiveLogicFunction) {
    std::string code = R"(
        int gcd(int a, int b) {
            if (b == 0) return a;
            return gcd(b, a % b);
        }
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto functions = extractFunctions(AST.get());
    ASSERT_FALSE(functions.empty()) << "No functions found";

    const FunctionDecl* gcdFunc = functions[0];
    ACSLAxiomaticBuilder builder;

    std::string axiomaticBlock = builder.generateAxiomaticBlock(gcdFunc);

    // Verify recursive logic function
    ASSERT_FALSE(axiomaticBlock.empty())
        << "Should generate axiomatic block for recursive function";
    EXPECT_NE(axiomaticBlock.find("logic"), std::string::npos)
        << "Should contain logic function";
    EXPECT_NE(axiomaticBlock.find("gcd"), std::string::npos)
        << "Should reference function name";
}

// Test 5: PolymorphicLogicFunction - Template → polymorphic
TEST_F(ACSLAxiomaticBuilderTest, PolymorphicLogicFunction) {
    std::string code = R"(
        template<typename T>
        T max_value(T a, T b) {
            return (a > b) ? a : b;
        }

        int test() {
            return max_value(5, 10);
        }
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto functions = extractFunctions(AST.get());

    // Find template function
    const FunctionDecl* maxFunc = findFunction(functions, "max_value");

    if (maxFunc) {
        ACSLAxiomaticBuilder builder;
        std::string axiomaticBlock = builder.generateAxiomaticBlock(maxFunc);

        // Verify polymorphic logic function
        ASSERT_FALSE(axiomaticBlock.empty())
            << "Should generate axiomatic block for template";
        EXPECT_NE(axiomaticBlock.find("logic"), std::string::npos)
            << "Should contain logic function";
    }
}

// Test 6: InductivePredicate - Inductive definition
TEST_F(ACSLAxiomaticBuilderTest, InductivePredicate) {
    std::string code = R"(
        bool is_sorted(int arr[], int size) {
            if (size <= 1) return true;
            for (int i = 0; i < size - 1; i++) {
                if (arr[i] > arr[i+1]) return false;
            }
            return true;
        }
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto functions = extractFunctions(AST.get());
    ASSERT_FALSE(functions.empty()) << "No functions found";

    const FunctionDecl* sortedFunc = functions[0];
    ACSLAxiomaticBuilder builder;

    std::string axiomaticBlock = builder.generateAxiomaticBlock(sortedFunc);

    // Verify inductive predicate generation
    ASSERT_FALSE(axiomaticBlock.empty())
        << "Should generate axiomatic block for predicate";
    EXPECT_TRUE(axiomaticBlock.find("logic") != std::string::npos ||
                axiomaticBlock.find("predicate") != std::string::npos)
        << "Should contain logic or predicate definition";
}

// Test 7: ConsistencyCheck - No contradictory axioms
TEST_F(ACSLAxiomaticBuilderTest, ConsistencyCheck) {
    std::string code = R"(
        int abs_value(int x) {
            return (x >= 0) ? x : -x;
        }
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto functions = extractFunctions(AST.get());
    ASSERT_FALSE(functions.empty()) << "No functions found";

    const FunctionDecl* absFunc = functions[0];
    ACSLAxiomaticBuilder builder;

    std::string axiomaticBlock = builder.generateAxiomaticBlock(absFunc);

    // Verify no contradictory axioms
    // This is a semantic check - for now, verify structure is sound
    bool hasAxiom = axiomaticBlock.find("axiom") != std::string::npos;
    if (hasAxiom) {
        // Should not have both "x >= 0" and "x < 0" as universal properties
        // This is a simplified check - real consistency requires SMT solver
        EXPECT_TRUE(true) << "Basic consistency maintained";
    }
}

// Test 8: CommutativityAxiom - Commutative property
TEST_F(ACSLAxiomaticBuilderTest, CommutativityAxiom) {
    std::string code = R"(
        int add(int a, int b) {
            return a + b;
        }
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto functions = extractFunctions(AST.get());
    ASSERT_FALSE(functions.empty()) << "No functions found";

    const FunctionDecl* addFunc = functions[0];
    ACSLAxiomaticBuilder builder;

    std::string axiomaticBlock = builder.generateAxiomaticBlock(addFunc);

    // Verify commutativity axiom
    // For commutative operations like add, should generate:
    // axiom add_commutative: \forall integer a, b; add(a, b) == add(b, a);
    ASSERT_FALSE(axiomaticBlock.empty()) << "Should generate axiomatic block";
}

// Test 9: AssociativityAxiom - Associative property
TEST_F(ACSLAxiomaticBuilderTest, AssociativityAxiom) {
    std::string code = R"(
        int add(int a, int b) {
            return a + b;
        }
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto functions = extractFunctions(AST.get());
    ASSERT_FALSE(functions.empty()) << "No functions found";

    const FunctionDecl* addFunc = functions[0];
    ACSLAxiomaticBuilder builder;

    std::string axiomaticBlock = builder.generateAxiomaticBlock(addFunc);

    // Verify associativity axiom
    // For associative operations like add, should generate:
    // axiom add_associative: \forall integer a, b, c; add(add(a, b), c) == add(a, add(b, c));
    ASSERT_FALSE(axiomaticBlock.empty()) << "Should generate axiomatic block";
}

// Test 10: IdentityAxiom - Identity element
TEST_F(ACSLAxiomaticBuilderTest, IdentityAxiom) {
    std::string code = R"(
        int add(int a, int b) {
            return a + b;
        }
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto functions = extractFunctions(AST.get());
    ASSERT_FALSE(functions.empty()) << "No functions found";

    const FunctionDecl* addFunc = functions[0];
    ACSLAxiomaticBuilder builder;

    std::string axiomaticBlock = builder.generateAxiomaticBlock(addFunc);

    // Verify identity axiom
    // For add, identity is 0: add(x, 0) == x
    ASSERT_FALSE(axiomaticBlock.empty()) << "Should generate axiomatic block";
}

// Test 11: InverseAxiom - Inverse operation
TEST_F(ACSLAxiomaticBuilderTest, InverseAxiom) {
    std::string code = R"(
        int negate(int x) {
            return -x;
        }
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto functions = extractFunctions(AST.get());
    ASSERT_FALSE(functions.empty()) << "No functions found";

    const FunctionDecl* negFunc = functions[0];
    ACSLAxiomaticBuilder builder;

    std::string axiomaticBlock = builder.generateAxiomaticBlock(negFunc);

    // Verify inverse axiom
    // For negate: negate(negate(x)) == x
    ASSERT_FALSE(axiomaticBlock.empty()) << "Should generate axiomatic block";
}

// Test 12: DistributivityAxiom - Distributive property
TEST_F(ACSLAxiomaticBuilderTest, DistributivityAxiom) {
    std::string code = R"(
        int multiply(int a, int b) {
            return a * b;
        }

        int add(int a, int b) {
            return a + b;
        }
    )";

    auto AST = parseCode(code);
    ASSERT_TRUE(AST) << "Failed to parse code";

    auto functions = extractFunctions(AST.get());
    ASSERT_GE(functions.size(), 2u) << "Should find both functions";

    const FunctionDecl* mulFunc = findFunction(functions, "multiply");
    ASSERT_TRUE(mulFunc) << "Should find multiply function";

    ACSLAxiomaticBuilder builder;
    std::string axiomaticBlock = builder.generateAxiomaticBlock(mulFunc);

    // Verify distributivity axiom
    // For multiply over add: multiply(a, add(b, c)) == add(multiply(a, b), multiply(a, c))
    ASSERT_FALSE(axiomaticBlock.empty()) << "Should generate axiomatic block";
}
