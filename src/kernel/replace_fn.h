/*
Copyright (c) 2013-2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Leonardo de Moura
*/
#pragma once
#include <tuple>
#include "runtime/interrupt.h"
#include "kernel/expr.h"
#include "kernel/expr_maps.h"
#include "kernel/open_hash_table.h"

namespace lean {
/**
   \brief Apply <tt>f</tt> to the subexpressions of a given expression.

   f is invoked for each subexpression \c s of the input expression e.
   In a call <tt>f(s, n)</tt>, n is the scope level, i.e., the number of
   bindings operators that enclosing \c s. The replaces only visits children of \c e
   if f return none_expr.
*/
expr replace(expr const & e, std::function<optional<expr>(expr const &, unsigned)> const & f, bool use_cache = true);
inline expr replace(expr const & e, std::function<optional<expr>(expr const &)> const & f, bool use_cache = true) {
    return replace(e, [&](expr const & e, unsigned) { return f(e); }, use_cache);
}

/* Cache of `replace`-style traversals, mapping a subterm (by pointer) and its scope level to its
   result. Keys are borrowed from the input expression. */
class replace_cache {
    struct entry { object * m_key; object * m_val; unsigned m_offset; };
    typedef std::pair<object *, unsigned> key;
    struct traits {
        static bool matches(entry const & s, key const & k) { return s.m_key == k.first && s.m_offset == k.second; }
        static void release(entry & s) { dec_ref(s.m_val); }
    };
    open_hash_table<entry, traits> m_table;
    static unsigned key_hash(object * e, unsigned offset) {
        return static_cast<unsigned>(hash(reinterpret_cast<size_t>(e) >> 3, offset));
    }
public:
    expr const * find(expr const & e, unsigned offset) const {
        entry const * s = m_table.find(key_hash(e.raw(), offset), key(e.raw(), offset));
        return s ? &TO_REF(expr, s->m_val) : nullptr;
    }
    /* Does nothing if the key is already present. */
    void insert(expr const & e, unsigned offset, expr const & r) {
        auto p = m_table.find_or_add(key_hash(e.raw(), offset), key(e.raw(), offset));
        if (p.second) {
            p.first->m_key    = e.raw();
            p.first->m_val    = r.to_obj_arg();
            p.first->m_offset = offset;
        }
    }
};

template<typename F>
class replace_loose_bvars_fn {
    replace_cache m_cache;
    unsigned      m_s;
    F const &     m_f;

    expr save_result(expr const & e, unsigned offset, expr r, bool shared) {
        if (shared)
            m_cache.insert(e, offset, r);
        return r;
    }

    expr apply(expr const & e, unsigned offset) {
        unsigned s1 = m_s + offset;
        if (s1 < m_s /* overflow, no bound variable index is >= s1 */ || s1 >= get_loose_bvar_range(e))
            return e;
        bool shared = false;
        if (!is_likely_unshared(e)) {
            if (expr const * r = m_cache.find(e, offset))
                return *r;
            shared = true;
        }
        switch (e.kind()) {
        case expr_kind::BVar:
            return save_result(e, offset, m_f(e, offset), shared);
        case expr_kind::MData: {
            expr new_e = apply(mdata_expr(e), offset);
            return save_result(e, offset, update_mdata(e, new_e), shared);
        }
        case expr_kind::Proj: {
            expr new_e = apply(proj_expr(e), offset);
            return save_result(e, offset, update_proj(e, new_e), shared);
        }
        case expr_kind::App: {
            expr new_f = apply(app_fn(e), offset);
            expr new_a = apply(app_arg(e), offset);
            return save_result(e, offset, update_app(e, new_f, new_a), shared);
        }
        case expr_kind::Pi: case expr_kind::Lambda: {
            expr new_d = apply(binding_domain(e), offset);
            expr new_b = apply(binding_body(e), offset+1);
            return save_result(e, offset, update_binding(e, new_d, new_b), shared);
        }
        case expr_kind::Let: {
            expr new_t = apply(let_type(e), offset);
            expr new_v = apply(let_value(e), offset);
            expr new_b = apply(let_body(e), offset+1);
            return save_result(e, offset, update_let(e, new_t, new_v, new_b), shared);
        }
        case expr_kind::Const: case expr_kind::Sort: case expr_kind::Lit:
        case expr_kind::MVar:  case expr_kind::FVar:
            lean_unreachable(); // they have no loose bound variables
        }
        lean_unreachable();
    }
public:
    replace_loose_bvars_fn(unsigned s, F const & f):m_s(s), m_f(f) {}
    expr operator()(expr const & e) { return apply(e, 0); }
};

/* Return `e` with each loose bound variable `#i` such that `i >= s + offset`, where `offset` is
   the number of binders above it, replaced by `f(#i, offset)`. This is `replace` with a function
   that returns subterms without such variables unchanged, and it produces the same result
   (including sharing), but these subterms bypass the cache. */
template<typename F>
expr replace_loose_bvars(expr const & e, unsigned s, F const & f) {
    return replace_loose_bvars_fn<F>(s, f)(e);
}
}
