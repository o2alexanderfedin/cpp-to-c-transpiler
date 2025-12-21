/**
 * @file TemplateInstantiationTracker.h
 * @brief Phase 11: Template Instantiation Tracking (v2.4.0)
 *
 * Tracks which template instantiations have been processed to prevent
 * duplicate code generation during template monomorphization.
 *
 * Design Principles:
 * - Single Responsibility: Only track instantiation uniqueness
 * - Open/Closed: Can extend tracking metadata without modifying core logic
 * - Interface Segregation: Simple, focused interface
 */

#ifndef TEMPLATE_INSTANTIATION_TRACKER_H
#define TEMPLATE_INSTANTIATION_TRACKER_H

#include <string>
#include <set>
#include <vector>

/**
 * @class TemplateInstantiationTracker
 * @brief Tracks unique template instantiations to prevent duplicates
 *
 * This class maintains a set of unique template instantiation keys
 * (e.g., "Stack<int>", "Vector<Pair<int,double>>") and provides
 * methods to check if an instantiation has already been processed.
 *
 * Usage:
 * ```cpp
 * TemplateInstantiationTracker tracker;
 *
 * if (tracker.addInstantiation("Stack<int>")) {
 *     // First time seeing Stack<int>, generate code
 * } else {
 *     // Already processed, skip
 * }
 * ```
 */
class TemplateInstantiationTracker {
public:
    /**
     * @brief Default constructor
     */
    TemplateInstantiationTracker() = default;

    /**
     * @brief Add a template instantiation to the tracking set
     * @param instantiationKey Unique key for the instantiation (e.g., "Stack<int>")
     * @return true if this is a new instantiation, false if already tracked
     *
     * This method attempts to add the instantiation key to the internal set.
     * If the key already exists (duplicate), it returns false.
     * If the key is new, it's added and returns true.
     *
     * Single Responsibility: Manage uniqueness of instantiations
     */
    bool addInstantiation(const std::string& instantiationKey);

    /**
     * @brief Check if an instantiation has already been tracked
     * @param instantiationKey Unique key for the instantiation
     * @return true if the instantiation has been tracked, false otherwise
     *
     * Query method that doesn't modify state.
     */
    bool isTracked(const std::string& instantiationKey) const;

    /**
     * @brief Get all tracked instantiation keys
     * @return Vector of all instantiation keys that have been tracked
     *
     * Useful for debugging, reporting, and verification.
     */
    std::vector<std::string> getAllTracked() const;

    /**
     * @brief Get count of tracked instantiations
     * @return Number of unique instantiations tracked
     */
    size_t getCount() const;

    /**
     * @brief Clear all tracked instantiations
     *
     * Resets the tracker to initial state.
     * Useful for processing multiple translation units independently.
     */
    void clear();

private:
    /**
     * @brief Set of tracked instantiation keys
     *
     * Using std::set for O(log n) lookup and automatic deduplication.
     * Keys are in the form: "TemplateName<Arg1,Arg2,...>"
     */
    std::set<std::string> trackedInstantiations;
};

#endif // TEMPLATE_INSTANTIATION_TRACKER_H
