/**
 * @file TemplateInstantiationTracker.cpp
 * @brief Implementation of Template Instantiation Tracker (v2.4.0)
 */

#include "TemplateInstantiationTracker.h"
#include <algorithm>

bool TemplateInstantiationTracker::addInstantiation(const std::string& instantiationKey) {
    // Try to insert the key into the set
    // insert() returns a pair: (iterator, bool)
    // The bool is true if insertion occurred (new element), false if already exists
    auto result = trackedInstantiations.insert(instantiationKey);
    return result.second;  // Return true if newly inserted, false if duplicate
}

bool TemplateInstantiationTracker::isTracked(const std::string& instantiationKey) const {
    return trackedInstantiations.find(instantiationKey) != trackedInstantiations.end();
}

std::vector<std::string> TemplateInstantiationTracker::getAllTracked() const {
    // Convert set to vector for easier iteration and testing
    return std::vector<std::string>(trackedInstantiations.begin(),
                                    trackedInstantiations.end());
}

size_t TemplateInstantiationTracker::getCount() const {
    return trackedInstantiations.size();
}

void TemplateInstantiationTracker::clear() {
    trackedInstantiations.clear();
}
