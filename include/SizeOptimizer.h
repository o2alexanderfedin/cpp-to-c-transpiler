/**
 * SizeOptimizer.h
 *
 * Story #119: Implement Size Optimization with LTO/PGO Support
 * Epic #16: Runtime Optimization & Configuration
 *
 * Code-level size optimization including:
 * - Dead code elimination
 * - Function inlining for small helpers
 * - Constant folding
 * - String deduplication
 *
 * SOLID Principles:
 * - Single Responsibility: Performs code-level optimizations only
 * - Open/Closed: Extensible for new optimization passes
 * - Liskov Substitution: Can be substituted with specialized optimizers
 * - Interface Segregation: Minimal, focused interface
 * - Dependency Inversion: Depends on OptimizationPass abstraction
 *
 * Design Patterns:
 * - Strategy pattern for different optimization strategies
 * - Chain of Responsibility for optimization passes
 */

#ifndef SIZE_OPTIMIZER_H
#define SIZE_OPTIMIZER_H

#include <string>
#include <vector>
#include <set>
#include <map>

/**
 * Optimization pass interface
 *
 * Abstract base class for optimization passes
 */
class OptimizationPass {
public:
    virtual ~OptimizationPass() = default;

    /**
     * Apply optimization to code
     *
     * @param code Input code string
     * @return Optimized code string
     */
    virtual std::string optimize(const std::string& code) = 0;

    /**
     * Get optimization pass name
     *
     * @return Name of the optimization pass
     */
    virtual std::string getName() const = 0;
};

/**
 * Size optimizer for generated C code
 *
 * Applies various size optimization techniques:
 * - Dead code elimination
 * - Function inlining
 * - Constant folding
 * - String deduplication
 */
class SizeOptimizer {
public:
    /**
     * Default constructor
     */
    SizeOptimizer();

    /**
     * Destructor
     */
    ~SizeOptimizer();

    /**
     * Enable dead code elimination
     *
     * Removes unused functions and variables
     */
    void enableDeadCodeElimination();

    /**
     * Disable dead code elimination
     */
    void disableDeadCodeElimination();

    /**
     * Enable function inlining
     *
     * @param maxLines Maximum lines for inlining (default: 3)
     */
    void enableFunctionInlining(int maxLines = 3);

    /**
     * Disable function inlining
     */
    void disableFunctionInlining();

    /**
     * Enable constant folding
     *
     * Pre-computes constant expressions
     */
    void enableConstantFolding();

    /**
     * Disable constant folding
     */
    void disableConstantFolding();

    /**
     * Enable string deduplication
     *
     * Shares storage for identical strings
     */
    void enableStringDeduplication();

    /**
     * Disable string deduplication
     */
    void disableStringDeduplication();

    /**
     * Optimize code with enabled passes
     *
     * @param code Input code string
     * @return Optimized code string
     */
    std::string optimize(const std::string& code);

    /**
     * Get list of enabled optimization passes
     *
     * @return Vector of pass names
     */
    std::vector<std::string> getEnabledPasses() const;

private:
    bool deadCodeEliminationEnabled;
    bool functionInliningEnabled;
    bool constantFoldingEnabled;
    bool stringDeduplicationEnabled;
    int inlineMaxLines;

    /**
     * Perform dead code elimination
     *
     * @param code Input code
     * @return Code with unused functions/variables removed
     */
    std::string performDeadCodeElimination(const std::string& code);

    /**
     * Perform function inlining
     *
     * @param code Input code
     * @return Code with small functions inlined
     */
    std::string performFunctionInlining(const std::string& code);

    /**
     * Perform constant folding
     *
     * @param code Input code
     * @return Code with constants folded
     */
    std::string performConstantFolding(const std::string& code);

    /**
     * Perform string deduplication
     *
     * @param code Input code
     * @return Code with deduplicated strings
     */
    std::string performStringDeduplication(const std::string& code);

    /**
     * Find all function definitions in code
     *
     * @param code Input code
     * @return Set of function names
     */
    std::set<std::string> findFunctionDefinitions(const std::string& code);

    /**
     * Find all function calls in code
     *
     * @param code Input code
     * @return Set of function names
     */
    std::set<std::string> findFunctionCalls(const std::string& code);

    /**
     * Check if function is small enough to inline
     *
     * @param functionBody Function body
     * @param maxLines Maximum allowed lines
     * @return true if function should be inlined
     */
    bool shouldInlineFunction(const std::string& functionBody, int maxLines);

    /**
     * Evaluate constant expression
     *
     * @param expr Expression string
     * @return Evaluated result or empty string if not constant
     */
    std::string evaluateConstantExpression(const std::string& expr);

    /**
     * Find all string literals in code
     *
     * @param code Input code
     * @return Map from string content to list of positions
     */
    std::map<std::string, std::vector<size_t>> findStringLiterals(const std::string& code);
};

#endif // SIZE_OPTIMIZER_H
