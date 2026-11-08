/**
 * @file leaf_algebraic_acn.cpp
 * Leaf arithmetic over acn algebraic complex numbers (buddy_acn target).
 */

extern "C" {
#include "../../symb_utils.h"
#include "../../mtbdd_symb_val.h"
#include "../../medusa_mem_track.h"
#include "../../error.h"
#include "../../hash.h"
}

#include "../../../lib/algebraic-complex-numbers/include/acn/acn.hpp"

#include <algorithm>
#include <complex>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <string>
#include <unordered_set>
#include <memory>

// TODO: Finer rotations!

using acnValue = acn::Acn<ACN_N, acn::BigInt>;

struct sl_val_t { symexp_list_t *e[ACN_N]; };

struct sl_map_t { vars_t v[ACN_N]; };

static int64_t g_sqrt2_exp = 0;
static int64_t g_sqrt2_exp_symb = 0;

// Common K during the evaluation of symbolic loops
static acn::ScaleExp g_symb_common_k = 0;

// BigInt and leaf_primitive_t (i.e mpz) are the same thing
struct LEAF_TYPE_IMPL {
    acnValue acn;
};

static inline LEAF_TYPE allocPimpl(acnValue& from)
{
    medusa_mem_note_pimpl_alloc();
    return { .pImpl = new LEAF_TYPE_IMPL{ from }};
}

static inline LEAF_TYPE allocPimpl(acnValue&& from)
{
    medusa_mem_note_pimpl_alloc();
    return { .pImpl = new LEAF_TYPE_IMPL{ std::move(from) }};
}


extern "C" {

/*
 * Tuple lifecycle
 */

LEAF_TYPE clonePimpl(LEAF_TYPE a)
{
  if (!a.pImpl)
        return (LEAF_TYPE){ .pImpl = NULL };
     return allocPimpl(a.pImpl->acn);
}

void freePimpl(void *leafraw)
{
    if (!leafraw) return;

    LEAF_TYPE *leaf = (LEAF_TYPE*) leafraw;
    if (!leaf->pImpl) return;

    delete leaf->pImpl;
    leaf->pImpl = NULL;
    medusa_mem_note_pimpl_free();
}

/*
 * Tuple identity (compare + hash)
 */

int terminal_compare_generic(void *a, void *b)
{
    LEAF_TYPE *ldata_a = (LEAF_TYPE *) a;
    LEAF_TYPE *ldata_b = (LEAF_TYPE *) b;

    bool null_a = (ldata_a == NULL || ldata_a->pImpl == NULL);
    bool null_b = (ldata_b == NULL || ldata_b->pImpl == NULL);

    if (null_a && null_b) return 1;   // both NULL --  equal
    if (null_a || null_b) return 0;   // one NULL -- not equal

    return ldata_a->pImpl->acn == ldata_b->pImpl->acn;
}

unsigned terminal_hash_generic(void *q)
{
    LEAF_TYPE *ldata = (LEAF_TYPE*) q;
    if (!ldata || !ldata->pImpl) return 0;
    uint64_t val = acn::hash_value(ldata->pImpl->acn);
    return (unsigned)(val ^ (val >> 32));
}

/*
 * Output
 */

static int g_print_leaf_prob = 0;

void setLeafPrintProb(bool is_prob)
{
    g_print_leaf_prob = is_prob ? 1 : 0;
}

static double leaf_prob(const LEAF_TYPE_IMPL *l)
{
    return std::norm(l->acn.scale(static_cast<acn::ScaleExp>(-g_sqrt2_exp)).to_complex());
}

static std::string omega_pow(std::size_t j)
{
    static const char *sup[] = {"⁰", "¹", "²", "³", "⁴", "⁵", "⁶", "⁷", "⁸", "⁹"};
    std::string s = "ω";
    if (j > 1) {
        for (char d : std::to_string(j))
            s += sup[d - '0'];
    }
    return s;
}

char *terminal_to_str_generic(void *ldata_raw, char *buddy_buf,
                              size_t buddy_bufsize)
{
    LEAF_TYPE *leaf = (LEAF_TYPE*) ldata_raw;
    std::string s;

    if (!leaf || !leaf->pImpl) {
        s = g_print_leaf_prob ? "0.000000" : "0";
    }
    else if (g_print_leaf_prob) {
        char prob[64];
        std::snprintf(prob, sizeof(prob), "%f", leaf_prob(leaf->pImpl));
        s = prob;
    }
    else {
        // Same label as the mpz leaf: (1/√2)^(k) * (a+bω+cω²+dω³), where k is
        // the amplitude's exponent: the leaf's own plus the global one.
        const acnValue &v = leaf->pImpl->acn;
        s = "(1/√2)^(" + std::to_string((long long)v.scale_exp() + g_sqrt2_exp) + ") * (";
        auto coeffs = v.coeffs();
        for (std::size_t j = 0; j < coeffs.size(); j++) {
            std::string num = coeffs[j].to_string();
            if (j > 0 && num[0] != '-')
                s += "+";
            s += num;
            if (j > 0)
                s += omega_pow(j);
        }
        s += ")";
    }

    if (s.size() + 1 > buddy_bufsize) {
        buddy_buf = (char*) std::realloc(buddy_buf, s.size() + 1);
        if (buddy_buf == NULL)
            error_exit("Bad memory allocation.\n");
    }
    std::memcpy(buddy_buf, s.c_str(), s.size() + 1);
    return buddy_buf;
}

/*
 * Algebraic operations classical
 */

LEAF_TYPE invertLeaf(LEAF_TYPE a)
{
    if (a.pImpl == NULL) return a;
    return allocPimpl(-a.pImpl->acn);
}

LEAF_TYPE addLeaf(LEAF_TYPE a, LEAF_TYPE b)
{
    if (a.pImpl == NULL) return clonePimpl(b);
    if (b.pImpl == NULL) return clonePimpl(a);

    acnValue sum = a.pImpl->acn + b.pImpl->acn;
    if (sum.is_zero())
        return (LEAF_TYPE){ .pImpl = NULL };

    return allocPimpl(std::move(sum));
}

LEAF_TYPE addLeafS(LEAF_TYPE a, LEAF_TYPE b)
{
    // multiplication by 1/sqrt(2) done externally
    return addLeaf(a, b);
}

LEAF_TYPE subLeaf(LEAF_TYPE a, LEAF_TYPE b)
{
    if (a.pImpl == NULL) return invertLeaf(b);
    if (b.pImpl == NULL) return clonePimpl(a);

    acnValue diff = a.pImpl->acn - b.pImpl->acn;
    if (diff.is_zero())
        return (LEAF_TYPE){ .pImpl = NULL };

    return allocPimpl(std::move(diff));
}

LEAF_TYPE subLeafS(LEAF_TYPE a, LEAF_TYPE b)
{
    // multiplication by 1/sqrt(2) done externally
    return subLeaf(a, b);
}

LEAF_TYPE rotateCoef1(LEAF_TYPE l)
{
    if (l.pImpl == NULL) return l;
    return { allocPimpl(l.pImpl->acn.mul_omega(ACN_N / 4)) };
}

LEAF_TYPE rotateCoef1S(LEAF_TYPE l)
{
    // multiplication by 1/sqrt(2) done externally
    return rotateCoef1(l);
}

LEAF_TYPE rotateCoef1S_inv(LEAF_TYPE l)
{
    if (l.pImpl == NULL) return l;
    return { allocPimpl(l.pImpl->acn.mul_omega(-(ACN_N / 4))) };
}

LEAF_TYPE rotateCoef2(LEAF_TYPE l)
{
    if (l.pImpl == NULL) return l;
    return { allocPimpl(l.pImpl->acn.mul_omega(ACN_N * 2 / 4)) };
}

LEAF_TYPE rotateCoef2S(LEAF_TYPE l)
{
    // multiplication by 1/sqrt(2) done externally
    return rotateCoef2(l);
}

LEAF_TYPE times2Leaf(LEAF_TYPE l)
{
    if (l.pImpl == NULL) return l;
    return { allocPimpl( l.pImpl->acn.scale(2) ) };
}

LEAF_TYPE times2LeafS(LEAF_TYPE l)
{
    // multiplication by 1/sqrt(2) done externally
    return times2Leaf(l);
}

/*
 * Symbolic terminals and operations
 */

static bool all_null(const sl_val_t *v)
{
    for (size_t i = 0; i < ACN_N; i++)
        if (v->e[i]) return false;
    return true;
}

static void symb_rotate(sl_val_t *dst, const sl_val_t *src, int s)
{
    for (int j = 0; j < ACN_N; j++) {
        int from = j - s;
        bool neg = false;
        if (from < 0)      { from += ACN_N; neg = true; }
        if (from >= ACN_N) { from -= ACN_N; neg = true; }
        dst->e[j] = neg ? symexp_op(NULL, src->e[from], SYMEXP_SUB) : src->e[from];
    }
}

LEAF_TYPE terminal_symb_val_clone(LEAF_TYPE a)
{
    if (!a.pImpl) return (LEAF_TYPE){ .pImpl = NULL };
    sl_val_t *src = (sl_val_t *)a.pImpl;
    sl_val_t *dst = (sl_val_t *)malloc(sizeof(sl_val_t));
    if (!dst) exit(EXIT_FAILURE);
    *dst = *src;
    return (LEAF_TYPE){ .pImpl = (LEAF_TYPE_IMPL *)dst };
}

LEAF_TYPE terminal_symb_map_clone(LEAF_TYPE a)
{
    if (!a.pImpl) return (LEAF_TYPE){ .pImpl = NULL };
    sl_map_t *src = (sl_map_t *)a.pImpl;
    sl_map_t *dst = (sl_map_t *)malloc(sizeof(sl_map_t));
    if (!dst) exit(EXIT_FAILURE);
    *dst = *src;
    return (LEAF_TYPE){ .pImpl = (LEAF_TYPE_IMPL *)dst };
}

LEAF_TYPE mtbdd_symb_neg_i(LEAF_TYPE t)
{
    if (t.pImpl == NULL) return t;
    sl_val_t *ldata = (sl_val_t*) t.pImpl;
    sl_val_t *res_data = (sl_val_t*)malloc(sizeof(sl_val_t));

    for (size_t i = 0; i < ACN_N; i++) {
        res_data->e[i] = symexp_op(NULL, ldata->e[i], SYMEXP_SUB);
    }

    if (all_null(res_data)) {
        free(res_data);
        return (LEAF_TYPE){ .pImpl = NULL };
    }

    return (LEAF_TYPE){ .pImpl = (LEAF_TYPE_IMPL*) res_data };
}

LEAF_TYPE mtbdd_symb_coef_rot1_i(LEAF_TYPE t)
{
    if (t.pImpl == NULL) return t;
    sl_val_t *ldata = (sl_val_t*) t.pImpl;
    sl_val_t *res_data = (sl_val_t*)malloc(sizeof(sl_val_t));
    symb_rotate(res_data, ldata, ACN_N / 4);
    return (LEAF_TYPE){ .pImpl = (LEAF_TYPE_IMPL*)res_data };
}

LEAF_TYPE mtbdd_symb_coef_rot2_i(LEAF_TYPE t)
{
    if (t.pImpl == NULL) return t;
    sl_val_t *ldata = (sl_val_t*) t.pImpl;
    sl_val_t *res_data = (sl_val_t*)malloc(sizeof(sl_val_t));
    symb_rotate(res_data, ldata, ACN_N / 2);
    return (LEAF_TYPE){ .pImpl = (LEAF_TYPE_IMPL*)res_data };

}

LEAF_TYPE mtbdd_symb_plus_i(LEAF_TYPE a, LEAF_TYPE b)
{
    if (a.pImpl == NULL) return terminal_symb_val_clone(b);
    if (b.pImpl == NULL) return terminal_symb_val_clone(a);
    sl_val_t *a_data = (sl_val_t*) a.pImpl;
    sl_val_t *b_data = (sl_val_t*) b.pImpl;
    sl_val_t *res_data = (sl_val_t*)malloc(sizeof(sl_val_t));

    for (size_t i = 0; i < ACN_N; i++) {
        res_data->e[i] = symexp_op(a_data->e[i], b_data->e[i], SYMEXP_ADD);
    }

    if (all_null(res_data)) {
        free(res_data);
        return (LEAF_TYPE){ .pImpl = NULL };
    }

    return (LEAF_TYPE){ .pImpl = (LEAF_TYPE_IMPL*) res_data };
}

LEAF_TYPE mtbdd_symb_minus_i(LEAF_TYPE a, LEAF_TYPE b)
{
    if (a.pImpl == NULL) return mtbdd_symb_neg_i(b);
    if (b.pImpl == NULL) return terminal_symb_val_clone(a);
    sl_val_t *a_data = (sl_val_t*) a.pImpl;
    sl_val_t *b_data = (sl_val_t*) b.pImpl;
    sl_val_t *res_data = (sl_val_t*)malloc(sizeof(sl_val_t));

    for (size_t i = 0; i < ACN_N; i++) {
        res_data->e[i] = symexp_op(a_data->e[i], b_data->e[i], SYMEXP_SUB);
    }

    if (all_null(res_data)) {
        free(res_data);
        return (LEAF_TYPE){ .pImpl = NULL };
    }

    return (LEAF_TYPE){ .pImpl = (LEAF_TYPE_IMPL*) res_data };
}

LEAF_TYPE mtbdd_symb_times_c_i(LEAF_TYPE t, size_t c_raw)
{
    if (t.pImpl == NULL) return t;

    sl_val_t *ldata = (sl_val_t*) t.pImpl;
    sl_val_t *res_data = (sl_val_t *)malloc(sizeof(sl_val_t));
    unsigned long c = (unsigned long)c_raw;

    for (size_t i = 0; i < ACN_N; i++) {
        res_data->e[i] = symexp_mul_c(ldata->e[i], c);
    }

    LEAF_TYPE res = {.pImpl = (LEAF_TYPE_IMPL*)res_data};
    return res;
}

qBDD mtbdd_map_to_symb_val_reduced_i(qBDD t, size_t raw_map)
{
    if (qBDD_isTerminal(t)) {
        coef_t* map = (coef_t*) raw_map;
        LEAF_TYPE leaf = qBDD_getTerminalValue(t);
        sl_map_t *t_data = (sl_map_t*) leaf.pImpl;

        bool all_zero = true;
        for (int j = 0; j < ACN_N; j++) {
            if (mpz_sgn(map[t_data->v[j]]) != 0) {
                all_zero = false;
                break;
            }
        }
        if (all_zero) {
            validateApplyResult();
            return qBDD_false();
        }

        sl_val_t *new_data = (sl_val_t*)malloc(sizeof(sl_val_t));

        for (size_t i = 0; i < ACN_N; i++) {
            new_data->e[i] = symexp_init(t_data->v[i]);
        }

        LEAF_TYPE *newLeaf = (LEAF_TYPE*)malloc(sizeof(LEAF_TYPE));
        newLeaf->pImpl = (LEAF_TYPE_IMPL *)(void *)new_data;

        qBDD res = qBDD_maketerminal(qBDD_symbolicValLType(), (void *) newLeaf);
        validateApplyResult();
        return res;
    }
    invalidateApplyResult();
    return qBDD_false(); // Recurse deeper
}

qBDD mtbdd_map_to_symb_val_i(qBDD t, size_t raw_map)
{
    if (qBDD_isTerminal(t)) {
        coef_t* map = (coef_t*) raw_map;
        LEAF_TYPE leaf = qBDD_getTerminalValue(t);
        sl_map_t *t_data = (sl_map_t*) leaf.pImpl;
        sl_val_t *new_data = (sl_val_t*)malloc(sizeof(sl_val_t));

        for (size_t i = 0; i < ACN_N; i++) {
            new_data->e[i] = symexp_init(t_data->v[i]);
        }

        LEAF_TYPE *newLeaf = (LEAF_TYPE*)malloc(sizeof(LEAF_TYPE));
        newLeaf->pImpl = (LEAF_TYPE_IMPL *)(void *)new_data;

        qBDD res = qBDD_maketerminal(qBDD_symbolicValLType(), (void*) newLeaf);
        validateApplyResult();
        return res;
    }
    invalidateApplyResult();
    return qBDD_false(); // Recurse deeper
}

LEAF_TYPE mtbdd_symb_coef_rot1_i_inv(LEAF_TYPE t)
{
    if (t.pImpl == NULL) return t;
    sl_val_t *ldata = (sl_val_t*) t.pImpl;
    sl_val_t *res_data = (sl_val_t*)malloc(sizeof(sl_val_t));
    symb_rotate(res_data, ldata, -(ACN_N / 4));
    return (LEAF_TYPE){ .pImpl = (LEAF_TYPE_IMPL*)res_data };

}

qBDD t_xt_comp_create_i(qBDD t, size_t xt)
{
    if (qBDD_isFalse(t)) {
        validateApplyResult();
        return qBDD_false();
    }


    if (qBDD_isInternal(t)) {
        if(qBDD_getVar(t) == xt) {
            validateApplyResult();
            return qBDD_getLow(t);
        }
    } else {
        validateApplyResult();
        return t;
    }

    invalidateApplyResult(); // further recursion
    return t; // any, not considered
}

qBDD t_xt_create_i(qBDD t, size_t xt)
{
    if (qBDD_isFalse(t)) return qBDD_false();

    if (qBDD_isInternal(t)) {
        if(qBDD_getVar(t) == xt) {
            validateApplyResult();
            return qBDD_getHigh(t);
        }
    } else {
        validateApplyResult();
        return t;
    }

    invalidateApplyResult(); // further recursion
    return t; // any, not considered
}

static bool are_same(std::span<const vars_t> first,const sl_map_t* mdata)
{
    for (size_t i = 0; i < ACN_N; i++) {
        if (first[i] != mdata->v[i]) {
            return false;
        }
    }
    return true;
}

qBDD mtbdd_symb_refine_i(qBDD map, qBDD val, size_t rd_raw)
{
    rdata_t *rd = (rdata_t*) rd_raw;

    if (qBDD_isTerminal(map) && qBDD_isTerminal(val)) {
        LEAF_TYPE mapVal = qBDD_getTerminalValue(map);
        sl_map_t *mdata = (sl_map_t*) mapVal.pImpl; 
        std::array<vars_t, ACN_N> new_target;

        if (qBDD_isFalse(val)) {
            for (size_t i = 0; i < ACN_N; i++) {
                new_target[i] = refine_var_check(mdata->v[i], (symexp_list_t*) SYMEXP_NULL, rd);
            }
        }
        else {
            LEAF_TYPE valVal = qBDD_getTerminalValue(val);
            sl_val_t *vdata = (sl_val_t*) valVal.pImpl;
            for (size_t i = 0; i < ACN_N; i++) {
                new_target[i] = refine_var_check(mdata->v[i], vdata->e[i], rd);
            }
        }

        if (are_same(new_target, mdata)) {
            validateApplyResult();
            return map;
        }

        // new symbolic var needed
        sl_map_t *new_data = (sl_map_t*)malloc(sizeof(sl_map_t));
        for (size_t i = 0; i < ACN_N; i++) {
            new_data->v[i] = new_target[i];
        }

        LEAF_TYPE *newLeaf = (LEAF_TYPE*)malloc(sizeof(LEAF_TYPE));
        newLeaf->pImpl = (LEAF_TYPE_IMPL *)(void *)new_data;

        qBDD res = qBDD_maketerminal(qBDD_symbolicMapLType(), (void*)newLeaf);
        validateApplyResult();
        return res;
    }
    invalidateApplyResult();
    return qBDD_false(); // Recurse deeper
    
}

// Helper functions to put the coeficients of ACN to the same K
static void mul_sqrt2(mpz_t *x)
{
    mpz_t y[ACN_N];
    for (int j = 0; j < ACN_N; j++)
        mpz_init(y[j]);

    const int shifts[2] = { ACN_N / 4, 3 * ACN_N / 4 };   // + omega^(N/4), - omega^(3N/4)
    for (int t = 0; t < 2; t++) {
        for (int j = 0; j < ACN_N; j++) {
            int from = j - shifts[t];
            bool neg = false;
            if (from < 0) { from += ACN_N; neg = true; }
            bool subtract = (t == 1) != neg;              // the 2nd term is subtracted
            if (subtract) mpz_sub(y[j], y[j], x[from]);
            else          mpz_add(y[j], y[j], x[from]);
        }
    }

    for (int j = 0; j < ACN_N; j++) {
        mpz_swap(x[j], y[j]);
        mpz_clear(y[j]);
    }
}

static void mul_sqrt2_pow(mpz_t *x, long m)
{
    if (m >= 2)
        for (int j = 0; j < ACN_N; j++)
            mpz_mul_2exp(x[j], x[j], (mp_bitcnt_t)(m / 2));
    if (m & 1)
        mul_sqrt2(x);
}

qBDD mtbdd_to_symb_map_i(qBDD a, size_t raw_m)
{
    if (!qBDD_isFalse(a) && !qBDD_isTerminal(a)) {
        invalidateApplyResult();
        return qBDD_false();
    }

    vmap_t* m = (vmap_t*) raw_m;

    qBDD found = vmap_lookup(m, a);
    if (!qBDD_isFalse(found)) {
        validateApplyResult();
        return found;
    }

    // Initialize the variables
    vars_t arr[ACN_N];
    for (size_t i = 0; i < ACN_N; i++) {
        arr[i] = m->next_var + i;
    }

    // Partial function check
    if (qBDD_isFalse(a)) {
        // initial vmap size does not count with 'mtbdd_false' leaves, so vmap needs to be resized
        m->map = (leaf_primitive_t *) my_realloc(m->map, sizeof(coef_t) * (m->msize + ACN_N));
        m->msize += ACN_N;
        for (size_t i = 0; i < ACN_N; i++) {
            mpz_init_set_ui(m->map[arr[i]],0);
        }
    }
    else if (qBDD_isTerminal(a)) {
        const acnValue &x = qBDD_getTerminalValue(a).pImpl->acn;
        auto coeffs = x.coeffs();
        for (int i = 0; i < ACN_N; i++)
            // BigInt to mpz
            mpz_init_set_str(m->map[arr[i]], coeffs[i].to_string().c_str(), 10);
        mul_sqrt2_pow(&m->map[arr[0]], (long)g_symb_common_k - (long)x.scale_exp());
    }

    sl_map_t *new_data = (sl_map_t*) malloc(sizeof(sl_map_t));
    if (new_data == NULL) {
        printf("ERROR ALLOCATION\n");
        exit(EXIT_FAILURE);
    }
    for (int i = 0; i < ACN_N; i++) {
        new_data->v[i] = arr[i];
    }

    LEAF_TYPE *newLeaf = (LEAF_TYPE*)malloc(sizeof(LEAF_TYPE));
    newLeaf->pImpl = (LEAF_TYPE_IMPL *)(void *)new_data;

    qBDD res = qBDD_maketerminal(qBDD_symbolicMapLType(), (void *) newLeaf);
    m->next_var += ACN_N;
    validateApplyResult();
    vmap_insert(m, a, res);
    return res;
}

/*
 * Terminal type registration
 */

void terminal_symb_map_free(void *leafraw)
{
    if (!leafraw) return;
    LEAF_TYPE *leaf = (LEAF_TYPE *)leafraw;
    if (leaf->pImpl) {
        free(leaf->pImpl);
        leaf->pImpl = NULL;
    }
}

void terminal_symb_val_free(void *leafraw)
{
    if (!leafraw) return;
    LEAF_TYPE *leaf = (LEAF_TYPE *)leafraw;
    if (leaf->pImpl) {
        free(leaf->pImpl);
        leaf->pImpl = NULL;
    }
}

int terminal_symb_map_compare_generic(void *l_a, void *l_b)
{
    if (l_a == NULL && l_b == NULL) return 1;
    if ((l_a == NULL) != (l_b == NULL)) return 0;
    LEAF_TYPE *la = (LEAF_TYPE *)l_a;
    LEAF_TYPE *lb = (LEAF_TYPE *)l_b;
    if (la->pImpl == NULL || lb->pImpl == NULL) return 0;
    sl_map_t *ldata_a = (sl_map_t *)la->pImpl;
    sl_map_t *ldata_b = (sl_map_t *)lb->pImpl;
    for (size_t i = 0; i < ACN_N; i++) {
        if (ldata_a->v[i] != ldata_b->v[i]) {
            return 0;
        }
    }
    return 1;
}

unsigned terminal_symb_map_hash_generic(void *l_a)
{
    if (l_a == NULL) return 0;
    LEAF_TYPE *la = (LEAF_TYPE *)l_a;
    if (la->pImpl == NULL) return 0;
    sl_map_t *ldata = (sl_map_t *)la->pImpl;
    uint64_t val = 1;

    for (size_t i = 0; i < ACN_N; i++) {
        val = MY_HASH_COMB(val, ldata->v[i]);
    }
    return (unsigned)val;
}

int terminal_symb_val_compare_generic(void *l_a, void *l_b)
{
    if (l_a == NULL && l_b == NULL) return 1;
    if ((l_a == NULL) != (l_b == NULL)) return 0;
    LEAF_TYPE *la = (LEAF_TYPE *)l_a;
    LEAF_TYPE *lb = (LEAF_TYPE *)l_b;
    if (la->pImpl == NULL || lb->pImpl == NULL) return 0;
    sl_val_t *ldata_a = (sl_val_t *)la->pImpl;
    sl_val_t *ldata_b = (sl_val_t *)lb->pImpl;
    for (size_t i = 0; i < ACN_N; i++) {
        if (ldata_a->e[i] != ldata_b->e[i]) {
            return 0;
        }
    }
    return 1;

}

unsigned terminal_symb_val_hash_generic(void *l_a)
{
    if (l_a == NULL) return 0;
    LEAF_TYPE *la = (LEAF_TYPE *)l_a;
    if (la->pImpl == NULL) return 0;
    sl_val_t *ldata = (sl_val_t *)la->pImpl;
    uint64_t val = 1;

    for (size_t i = 0; i < ACN_N; i++) {
        val = MY_HASH_COMB(val, ldata->e[i]);
    }
    return (unsigned)val;

}

qBDD mtbdd_from_symb_i(qBDD t, size_t raw_map)
{
    // Partial function check
    if (qBDD_isFalse(t)) {
        validateApplyResult();
        return t;
    }

    if (qBDD_isTerminal(t)) {
        coef_t* map = (coef_t*) raw_map;
        LEAF_TYPE leaf = qBDD_getTerminalValue(t);
        sl_map_t *data = (sl_map_t*) leaf.pImpl;

        std::array<acn::BigInt, ACN_N> target;
        for (size_t i = 0; i < ACN_N; i++) {
            char *txt = mpz_get_str(NULL, 10, map[data->v[i]]);
            target[i] = *acn::BigInt::parse(txt);
            void (*freefn)(void *, size_t);
            mp_get_memory_functions(NULL, NULL, &freefn);
            freefn(txt, std::strlen(txt) + 1);
        }

        acnValue v = acnValue::from_coeffs(target, g_symb_common_k);
        if (v.is_zero()) {
            validateApplyResult();
            return qBDD_false();
        }

        LEAF_TYPE *newLeaf = (LEAF_TYPE*) malloc(sizeof(LEAF_TYPE));
        *newLeaf = allocPimpl(std::move(v));

        qBDD res = qBDD_maketerminal(qBDD_classicLType(), (void*) newLeaf);
        validateApplyResult();
        return res;
    }
    invalidateApplyResult();
    return qBDD_false(); // Recurse deeper
}



bool can_be_reduced(mtbdd_symb_t *symbc, rdata_t *rdata)
{
    bool is_correct = true;
    std::unique_ptr<bool[]> is_zero(new bool[rdata->vm->next_var]());
    for (int i = 0; i < rdata->vm->next_var; i++) {
        is_zero[i] = false;
    }

    // The whole leaf behaves the same way, so checking every 4th variable is sufficient
    for (int i = 0; i + ACN_N <= rdata->vm->next_var; i += ACN_N) {
        bool leaf_zero = true;
        for (size_t j = 0; j < ACN_N; j++) {
            if (sgn_generic(rdata->vm->map[i + j]) != 0) { leaf_zero = false; break; }
        }

        if (!leaf_zero) {
            continue;
        }

        bool all_updated = true;
        for (size_t j = 0; j < ACN_N; j++) {
            is_zero[i + j] = true;
            if (rdata->upd->arr[i + j] == SYMEXP_NULL) all_updated = false;
        }
        if (all_updated) {
            is_correct = false;
            break;
        }
    }

    // Check if swap with 0 leaf occurs 
    // (i.e., if these variables appear alone on some right side of update equation)
    for(size_t i = 0; i + ACN_N <= rdata->vm->next_var; i += ACN_N) {
        // Check for permutations as well, first variable of the leaf is sufficient
        // (we always swap the whole leaf)
        if (rdata->upd->arr[i] != NULL && rdata->upd->arr[i] != SYMEXP_NULL) {
            if (symexp_is_first_var_marked(rdata->upd->arr[i], is_zero.get())) {
                is_correct = false;
                break;
            }
        }
    }

    if (!is_correct) {
        symbc->is_reduced = false;
    }
    return is_correct;

}

/*
 * Package bootstrap
 */
void circuit_init_interface(qBDD *c, const uint32_t n)
{
    unsigned varNum = n;
    if (bdd_varnum() < varNum)
        bdd_setvarnum(varNum);

    g_sqrt2_exp = 0;

    LEAF_TYPE *one = (LEAF_TYPE*) std::malloc(sizeof(LEAF_TYPE));
    if (one == NULL) { bdd_error(BDD_MEMORY); }
    *one = allocPimpl(acnValue::one());

    qBDD leaf1 = qBDD_maketerminal(qBDD_classicLType(), one);
    qBDD_protect(leaf1);

    qBDD cube = leaf1;
    for (uint32_t i = n; i > 0; i--)
        cube = newqBDD(i - 1, cube, qBDD_false());

    qBDD_protect(cube);
    qBDD_unprotect(leaf1);
    *c = cube;
}

static void max_leaf_k(qBDD t, std::unordered_set<qBDD> &seen, acn::ScaleExp &k, bool &found)
{
    if (qBDD_isFalse(t) || !seen.insert(t).second)
        return;
    if (qBDD_isTerminal(t)) {
        LEAF_TYPE tv = qBDD_getTerminalValue(t);
        if (tv.pImpl) {
            acn::ScaleExp lk = tv.pImpl->acn.scale_exp();
            k = found ? std::max(k, lk) : lk;
            found = true;
        }
        return;
    }
    max_leaf_k(qBDD_getLow(t),  seen, k, found);
    max_leaf_k(qBDD_getHigh(t), seen, k, found);
}

void symb_init(qBDD *circ, mtbdd_symb_t *symbc)
{
    std::unordered_set<qBDD> seen;
    acn::ScaleExp k = 0;
    bool found = false;
    max_leaf_k(*circ, seen, k, found);
    g_symb_common_k = k;

    size_t msize = ACN_N * (qBDD_leafcount(*circ));

    vmap_init(&(symbc->vm), msize);
    symbc->is_reduced = true;
    symbc->is_refined = false;

    symbc->map = my_mtbdd_to_symb_map_i(*circ, (size_t)(uintptr_t)symbc->vm);
    qBDD_protect(symbc->map);
    symbc->val = my_mtbdd_map_to_symb_val_i(symbc->map,
                                            (size_t)(uintptr_t)symbc->vm->map,
                                            symbc->is_reduced);
    qBDD_protect(symbc->val);
    initInvSqrtCoeffSymb();
}

/*
 * Probability computation
 */

double qBDD_calculateProb(qBDD terminal)
{
    if (qBDD_isFalse(terminal))
        return 0.0;
    LEAF_TYPE tv = qBDD_getTerminalValue(terminal);
    if (!tv.pImpl)
        return 0.0;
    return leaf_prob(tv.pImpl);
}

/*
 * Global square root coeffs handles
 */

[[noreturn]] static void _fatal_error()
{
    std::fprintf(stderr, "1/sqrt2 exponent exceeds the acn ScaleExp range! aborting...");
    std::abort();
}

static void check_sqrt2_exp(int64_t e)
{
    if (e > std::numeric_limits<acn::ScaleExp>::max())
    {
        _fatal_error();
    }
}

void incInvSqrtCoeff()
{
    check_sqrt2_exp(++g_sqrt2_exp);
}

void incInvSqrtCoeffSymb()
{
    ++g_sqrt2_exp_symb;
}

void initInvSqrtCoeffSymb()
{
    g_sqrt2_exp_symb = 0;
}

void addInvSqrtCoeffs()
{
    int64_t r;
    if (__builtin_add_overflow(g_sqrt2_exp, g_sqrt2_exp_symb, &r))
    {
        _fatal_error();
    }
    check_sqrt2_exp(r);
    g_sqrt2_exp = r;
}

void mulInvSqrtCoeff(mpz_t res, mpz_t a, unsigned long mul)
{
    mpz_mul_ui(res, a, mul);
}

void clearInvSqrtCoeffSymb()
{
    g_sqrt2_exp_symb = 0;
}

void clearInvSqrtCoeffNormal()
{
    g_sqrt2_exp = 0;
}

void resetInvSqrtCoeffSymb()
{
    g_sqrt2_exp_symb = 0;
}

void mulInvSqrtSymbCoeff(unsigned long a)
{
    int64_t r;
    if (__builtin_mul_overflow(g_sqrt2_exp_symb, (int64_t)a, &r))
    {
        _fatal_error();
    }
    g_sqrt2_exp_symb = r;
}

/*
 * Rotation and phase gates
 */
[[noreturn]] static void _unsupported(const char *name)
{
    std::fprintf(stderr, "ERROR: %s is not supported by the acn backend (ACN_N=%d). "
                         "Use a floating-point backend for this rotation.\n", name, ACN_N);
    std::abort();
}

LEAF_TYPE rx_low_leaf(LEAF_TYPE low, LEAF_TYPE high, size_t param)
{
    (void)low;(void)high;(void)param; _unsupported("rx_low_leaf");
}

LEAF_TYPE rx_high_leaf(LEAF_TYPE low, LEAF_TYPE high, size_t param)
{
    (void)low;(void)high;(void)param; _unsupported("rx_high_leaf");
}

LEAF_TYPE ry_low_leaf(LEAF_TYPE low, LEAF_TYPE high, size_t param)
{

    (void)low;(void)high;(void)param; _unsupported("ry_low_leaf");
}

LEAF_TYPE ry_high_leaf(LEAF_TYPE low, LEAF_TYPE high, size_t param)
{
    (void)low;(void)high;(void)param; _unsupported("ry_high_leaf");
}

LEAF_TYPE rz_low_leaf(LEAF_TYPE l, size_t param)
{
    (void)l;(void)param; _unsupported("rz_low_leaf");
}

LEAF_TYPE rz_high_leaf(LEAF_TYPE l, size_t param)
{
    (void)l;(void)param; _unsupported("rz_high_leaf");
}

LEAF_TYPE negI_mul(LEAF_TYPE a)
{
    (void)a; _unsupported("negI_mul");
}

LEAF_TYPE mulPhaseLeaf(LEAF_TYPE t, size_t arg)
{
    (void)t;(void)arg; _unsupported("mulPhaseLeaf");
}

} /* extern "C" */
