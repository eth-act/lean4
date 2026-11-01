/*
Copyright (c) 2026 Kevaundray Wedderburn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author: Kevaundray Wedderburn
*/
#pragma once
#include <cstdlib>
#include <climits>
#include <cstdint>
#include <cstring>
#include <new>
#include <utility>
#include "util/alloc.h"
#include "runtime/hash.h"
#include "kernel/expr.h"

namespace lean {
/* Insert-only hash table for the kernel caches, some of which reach millions of entries.
   Entries are stored in insertion order in an array, and an open-addressing index (linear
   probing, power-of-two capacity, load factor at most 3/4) maps the 32-bit hash of a key to its
   entry. Unlike `lean::unordered_map`, it allocates no node per entry, a lookup scans adjacent
   index slots and only touches an entry on a hash match, and resizing the index does not touch
   the entries. Entries are released in reverse insertion order: the objects they own were mostly
   allocated in that order as well, and freeing them in a random order would miss the processor
   caches on almost every object. `Traits` provides `matches(entry, key)` and `release(entry)`.
   As with `unordered_map::insert`, an existing key keeps its entry. */
template<typename Entry, typename Traits>
class open_hash_table {
    /* `m_hash == 0` marks an empty index slot; keys whose hash is zero are stored with hash one. */
    struct index_slot { unsigned m_hash; unsigned m_entry; };
    index_slot * m_index            = nullptr;
    size_t       m_index_capacity   = 0;
    unsigned     m_shift            = 64;
    Entry *      m_entries          = nullptr;
    size_t       m_entries_capacity = 0;
    size_t       m_size             = 0;

    static unsigned stored_hash(unsigned h) { return h == 0 ? 1 : h; }

    size_t position(unsigned h) const {
        return static_cast<size_t>((static_cast<uint64>(h) * 0x9E3779B97F4A7C15ull) >> m_shift);
    }

    static void * alloc_array(size_t n, size_t elem_size) {
        if (n > SIZE_MAX / elem_size) throw std::bad_alloc();
#ifdef LEAN_MIMALLOC
        void * r = mi_malloc(n * elem_size);
#else
        void * r = malloc(n * elem_size);
#endif
        if (r == nullptr) throw std::bad_alloc();
        return r;
    }

    static void free_block(void * block) {
#ifdef LEAN_MIMALLOC
        mi_free(block);
#else
        free(block);
#endif
    }

    void grow_index() {
        size_t new_capacity = m_index_capacity == 0 ? 16 : 2 * m_index_capacity;
        index_slot * new_index = static_cast<index_slot *>(alloc_array(new_capacity, sizeof(index_slot)));
        memset(static_cast<void *>(new_index), 0, new_capacity * sizeof(index_slot));
        unsigned new_shift = 64 - __builtin_ctzll(new_capacity);
        size_t mask = new_capacity - 1;
        for (size_t i = 0; i < m_index_capacity; i++) {
            index_slot s = m_index[i];
            if (s.m_hash == 0) continue;
            size_t j = static_cast<size_t>((static_cast<uint64>(s.m_hash) * 0x9E3779B97F4A7C15ull) >> new_shift);
            while (new_index[j].m_hash != 0) j = (j + 1) & mask;
            new_index[j] = s;
        }
        free_block(m_index);
        m_index          = new_index;
        m_index_capacity = new_capacity;
        m_shift          = new_shift;
    }

    void grow_entries() {
        size_t new_capacity = m_entries_capacity == 0 ? 8 : 2 * m_entries_capacity;
        if (new_capacity > static_cast<size_t>(UINT_MAX)) throw std::bad_alloc();
        Entry * new_entries = static_cast<Entry *>(alloc_array(new_capacity, sizeof(Entry)));
        if (m_size > 0)
            memcpy(static_cast<void *>(new_entries), m_entries, m_size * sizeof(Entry));
        free_block(m_entries);
        m_entries          = new_entries;
        m_entries_capacity = new_capacity;
    }

public:
    open_hash_table() {}
    open_hash_table(open_hash_table const &) = delete;
    open_hash_table & operator=(open_hash_table const &) = delete;
    ~open_hash_table() {
        free_block(m_index);
        for (size_t i = m_size; i > 0; i--)
            Traits::release(m_entries[i - 1]);
        free_block(m_entries);
    }

    size_t size() const { return m_size; }

    /* Return the entry matching `key` (whose hash is `h`), or `nullptr`. */
    template<typename Key>
    Entry const * find(unsigned h, Key const & key) const {
        if (m_size == 0) return nullptr;
        h = stored_hash(h);
        size_t mask = m_index_capacity - 1;
        for (size_t i = position(h);; i = (i + 1) & mask) {
            index_slot s = m_index[i];
            if (s.m_hash == 0) return nullptr;
            if (s.m_hash == h && Traits::matches(m_entries[s.m_entry], key)) return &m_entries[s.m_entry];
        }
    }

    /* Return the entry matching `key` (whose hash is `h`) and `false`, or an uninitialized entry
       for `key` and `true`. The caller must construct the new entry before using the table again. */
    template<typename Key>
    std::pair<Entry *, bool> find_or_add(unsigned h, Key const & key) {
        if (4 * (m_size + 1) > 3 * m_index_capacity) grow_index();
        h = stored_hash(h);
        size_t mask = m_index_capacity - 1;
        for (size_t i = position(h);; i = (i + 1) & mask) {
            index_slot & s = m_index[i];
            if (s.m_hash == 0) {
                if (m_size == m_entries_capacity) grow_entries();
                s.m_hash  = h;
                s.m_entry = static_cast<unsigned>(m_size);
                return std::make_pair(&m_entries[m_size++], true);
            }
            if (s.m_hash == h && Traits::matches(m_entries[s.m_entry], key))
                return std::make_pair(&m_entries[s.m_entry], false);
        }
    }
};

/* Map from expressions to expressions, keys compared with structural equality (`operator==`). */
class structural_expr_map {
    struct entry { object * m_key; object * m_val; };
    struct traits {
        static bool matches(entry const & s, expr const & k) { return TO_REF(expr, s.m_key) == k; }
        static void release(entry & s) { dec_ref(s.m_key); dec_ref(s.m_val); }
    };
    open_hash_table<entry, traits> m_table;
public:
    expr const * find(expr const & k) const {
        entry const * s = m_table.find(hash(k), k);
        return s ? &TO_REF(expr, s->m_val) : nullptr;
    }
    /* Does nothing if `k` is already present. */
    void insert(expr const & k, expr const & v) {
        auto r = m_table.find_or_add(hash(k), k);
        if (r.second) {
            r.first->m_key = k.to_obj_arg();
            r.first->m_val = v.to_obj_arg();
        }
    }
};

/* Map from an expression, compared by pointer, and a list of universe levels, compared
   structurally, to an expression. */
class expr_levels_map {
    struct entry { object * m_expr; object * m_levels; object * m_val; };
    typedef std::pair<expr const *, levels const *> key;
    struct traits {
        static bool matches(entry const & s, key const & k) {
            return s.m_expr == k.first->raw() && TO_REF(levels, s.m_levels) == *k.second;
        }
        static void release(entry & s) { dec_ref(s.m_expr); dec(s.m_levels); dec_ref(s.m_val); }
    };
    open_hash_table<entry, traits> m_table;
    static unsigned key_hash(expr const & e, levels const & ls) {
        uint64 h = reinterpret_cast<size_t>(e.raw()) >> 3;
        for (level const & l : ls)
            h = hash(h, static_cast<uint64>(hash(l)));
        return static_cast<unsigned>(h);
    }
public:
    expr const * find(expr const & e, levels const & ls) const {
        entry const * s = m_table.find(key_hash(e, ls), key(&e, &ls));
        return s ? &TO_REF(expr, s->m_val) : nullptr;
    }
    /* Does nothing if the key is already present. */
    void insert(expr const & e, levels const & ls, expr const & v) {
        auto r = m_table.find_or_add(key_hash(e, ls), key(&e, &ls));
        if (r.second) {
            r.first->m_expr   = e.to_obj_arg();
            r.first->m_levels = ls.to_obj_arg();
            r.first->m_val    = v.to_obj_arg();
        }
    }
};

/* Set of pairs of expressions, compared with structural equality. */
class structural_expr_pair_set {
    struct entry { object * m_fst; object * m_snd; };
    typedef std::pair<expr const *, expr const *> key;
    struct traits {
        static bool matches(entry const & s, key const & k) {
            return TO_REF(expr, s.m_fst) == *k.first && TO_REF(expr, s.m_snd) == *k.second;
        }
        static void release(entry & s) { dec_ref(s.m_fst); dec_ref(s.m_snd); }
    };
    open_hash_table<entry, traits> m_table;
    static unsigned pair_hash(expr const & a, expr const & b) {
        return static_cast<unsigned>(hash(static_cast<uint64>(hash(a)), static_cast<uint64>(hash(b))));
    }
public:
    bool contains(expr const & a, expr const & b) const {
        return m_table.find(pair_hash(a, b), key(&a, &b)) != nullptr;
    }
    void insert(expr const & a, expr const & b) {
        auto r = m_table.find_or_add(pair_hash(a, b), key(&a, &b));
        if (r.second) {
            r.first->m_fst = a.to_obj_arg();
            r.first->m_snd = b.to_obj_arg();
        }
    }
};
}
