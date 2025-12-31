/**
 * @file NameMangler_v2.h
 * @brief Functional composition-based name mangling following user's reference implementation
 */

#pragma once

#include <range/v3/all.hpp>
#include "clang/AST/Decl.h"
#include "clang/AST/DeclCXX.h"
#include "clang/Basic/OperatorKinds.h"
#include <vector>
#include <string>
#include <string_view>

namespace cpptoc {
namespace rv = ranges::views;

inline std::string sanitize_type_name(std::string_view s) {
    std::string result;
    result.reserve(s.size());

    for (std::size_t i = 0; i < s.size(); ++i) {
        switch (s[i]) {
            case ' ':  break;
            case '*':  result += "ptr"; break;
            case '&':
                if (i + 1 < s.size() && s[i + 1] == '&') {
                    result += "rref"; ++i;
                } else {
                    result += "ref";
                }
                break;
            case '<':  result += "_"; break;
            case '>':  break;
            case ',':  result += "_"; break;
            case ':':
                if (i + 1 < s.size() && s[i + 1] == ':') {
                    result += "_"; ++i;
                }
                break;
            case '[':  result += "arr"; break;
            case ']':  break;
            case '(':  break;
            case ')':  break;
            default:   result += s[i];
        }
    }
    return result;
}

inline std::string operator_name(clang::OverloadedOperatorKind kind) {
    switch (kind) {
        case clang::OO_Plus:          return "op_add";
        case clang::OO_Minus:         return "op_sub";
        case clang::OO_Star:          return "op_mul";
        case clang::OO_Slash:         return "op_div";
        case clang::OO_Percent:       return "op_mod";
        case clang::OO_Caret:         return "op_xor";
        case clang::OO_Amp:           return "op_bitand";
        case clang::OO_Pipe:          return "op_bitor";
        case clang::OO_Tilde:         return "op_compl";
        case clang::OO_Exclaim:       return "op_not";
        case clang::OO_Equal:         return "op_assign";
        case clang::OO_Less:          return "op_lt";
        case clang::OO_Greater:       return "op_gt";
        case clang::OO_PlusEqual:     return "op_addassign";
        case clang::OO_MinusEqual:    return "op_subassign";
        case clang::OO_StarEqual:     return "op_mulassign";
        case clang::OO_SlashEqual:    return "op_divassign";
        case clang::OO_PercentEqual:  return "op_modassign";
        case clang::OO_CaretEqual:    return "op_xorassign";
        case clang::OO_AmpEqual:      return "op_andassign";
        case clang::OO_PipeEqual:     return "op_orassign";
        case clang::OO_LessLess:      return "op_shl";
        case clang::OO_GreaterGreater: return "op_shr";
        case clang::OO_LessLessEqual: return "op_shlassign";
        case clang::OO_GreaterGreaterEqual: return "op_shrassign";
        case clang::OO_EqualEqual:    return "op_eq";
        case clang::OO_ExclaimEqual:  return "op_ne";
        case clang::OO_LessEqual:     return "op_le";
        case clang::OO_GreaterEqual:  return "op_ge";
        case clang::OO_Spaceship:     return "op_spaceship";
        case clang::OO_AmpAmp:        return "op_and";
        case clang::OO_PipePipe:      return "op_or";
        case clang::OO_PlusPlus:      return "op_inc";
        case clang::OO_MinusMinus:    return "op_dec";
        case clang::OO_Comma:         return "op_comma";
        case clang::OO_ArrowStar:     return "op_arrowstar";
        case clang::OO_Arrow:         return "op_arrow";
        case clang::OO_Call:          return "op_call";
        case clang::OO_Subscript:     return "op_index";
        case clang::OO_New:           return "op_new";
        case clang::OO_Delete:        return "op_delete";
        case clang::OO_Array_New:     return "op_new_arr";
        case clang::OO_Array_Delete:  return "op_delete_arr";
        case clang::OO_Coawait:       return "op_coawait";
        default:                      return "op_unknown";
    }
}

inline std::string get_decl_name(const clang::NamedDecl *ND) {
    if (llvm::isa<clang::CXXConstructorDecl>(ND)) {
        return "ctor";
    }

    if (llvm::isa<clang::CXXDestructorDecl>(ND)) {
        return "dtor";
    }

    if (const auto *CD = llvm::dyn_cast<clang::CXXConversionDecl>(ND)) {
        return "op_conv_" + sanitize_type_name(
            CD->getConversionType().getAsString()
        );
    }

    if (const auto *MD = llvm::dyn_cast<clang::CXXMethodDecl>(ND)) {
        if (MD->isOverloadedOperator()) {
            return operator_name(MD->getOverloadedOperator());
        }
    }

    // Free-standing overloaded operators
    if (const auto *FD = llvm::dyn_cast<clang::FunctionDecl>(ND)) {
        if (FD->isOverloadedOperator()) {
            return operator_name(FD->getOverloadedOperator());
        }
    }

    return ND->getNameAsString();
}

// Helper to get param types as vector (since ranges::experimental::generator requires coroutines)
// We'll use a simple vector approach for now that can be composed with range-v3
inline std::vector<std::string> param_types_vec(const clang::FunctionDecl *FD) {
    if (!FD) return {};

    std::vector<std::string> types;
    for (const clang::ParmVarDecl *P : FD->parameters()) {
        types.push_back(sanitize_type_name(P->getType().getAsString()));
    }
    return types;
}

inline std::vector<std::string> decl_name_parts_vec(const clang::Decl *D) {
    if (!D) return {};

    std::vector<std::string> result;
    std::vector<std::string> contexts;
    const clang::DeclContext *DC = D->getDeclContext();

    while (DC) {
        if (const auto *NS = llvm::dyn_cast<clang::NamespaceDecl>(DC)) {
            contexts.push_back(
                NS->isAnonymousNamespace() ? "anon" : NS->getNameAsString()
            );
        } else if (const auto *RD = llvm::dyn_cast<clang::RecordDecl>(DC)) {
            contexts.push_back(
                RD->getIdentifier() ? RD->getNameAsString() : "anon"
            );
        }
        DC = DC->getParent();
    }

    // Add contexts in reverse order (outermost first)
    for (auto it = contexts.rbegin(); it != contexts.rend(); ++it) {
        result.push_back(*it);
    }

    // Add declaration name
    if (const auto *ND = llvm::dyn_cast<clang::NamedDecl>(D)) {
        result.push_back(get_decl_name(ND));
    }

    // Add param types
    if (const auto *FD = llvm::dyn_cast<clang::FunctionDecl>(D)) {
        if (FD->param_empty()) {
            result.push_back("void");
        } else {
            auto params = param_types_vec(FD);
            auto joined = params
                | rv::join(std::string_view("_"))
                | ranges::to<std::string>();
            result.push_back(joined);
        }
    }

    return result;
}

inline std::string mangle_decl(const clang::Decl *D) {
    auto parts = decl_name_parts_vec(D);
    return ranges::views::all(parts)
        | rv::join(std::string_view("__"))
        | ranges::to<std::string>();
}

// Convenience wrappers for specific declaration types
inline std::string mangle_method(const clang::CXXMethodDecl *MD) {
    return mangle_decl(MD);
}

inline std::string mangle_constructor(const clang::CXXConstructorDecl *CD) {
    return mangle_decl(CD);
}

inline std::string mangle_destructor(const clang::CXXDestructorDecl *DD) {
    return mangle_decl(DD);
}

inline std::string mangle_function(const clang::FunctionDecl *FD) {
    // Special case: main() and extern "C" are not mangled
    if (FD && FD->getName() == "main") {
        return "main";
    }
    if (FD && FD->isExternC()) {
        return FD->getNameAsString();
    }
    return mangle_decl(FD);
}

inline std::string mangle_static_member(const clang::VarDecl *VD) {
    return mangle_decl(VD);
}

inline std::string mangle_class(const clang::CXXRecordDecl *RD) {
    return mangle_decl(RD);
}

} // namespace cpptoc
